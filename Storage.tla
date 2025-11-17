---- MODULE Storage ----
EXTENDS Sequences, Functions, Naturals, Integers, TLC

\* 
\* Formal model of the WiredTiger key-value storage interface.
\*
\* This covers many of the core facets of the storage interface utilized by
\* MongoDB nodes, when executing either single node operations or operations
\* that are a part of a cross-shard, distributed transaction.
\*
\* The "return" status of each transaction operation can be checked by a client
\* by checking the value of the 'txnStatus' variable after the execution of an
\* action/transition. This is a simple way to emulate the notion of
\* return/status codes in a standard programming language-oriented API.
\* 


\* The set of all possible keys. In this spec we assume keys are simply a subset
\* of natural numbers so that they have a natural total order associated with
\* them.
CONSTANT Keys 

\* Set of transaction ids.
CONSTANT TxnId

\* Set of timestamps.
CONSTANT Timestamps

CONSTANT NoValue


\* Log of prepared/committed transaction ops.
VARIABLE txnLog

\* Stores snapshots for running transactions on the underlying MongoDB instance.
VARIABLE txnSnapshots

\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

\* Tracks the global "stable timestamp" within the storage layer.
VARIABLE stableTs

\* Tracks the global "oldest timestamp" within the storage layer.
VARIABLE oldestTs

\* Tracks the global "all durable timestamp" within the storage layer.
VARIABLE allDurableTs


vars == <<txnLog, txnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs>>


\* Status codes for transaction operations.
STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"
STATUS_NOTFOUND == "WT_NOTFOUND"
STATUS_PREPARE_CONFLICT == "WT_PREPARE_CONFLICT"


\* Make values the same as transaction IDs.
Values == TxnId

\* The result a read will have if no value can be found.
NotFoundReadResult == [
    txnLogIndex |-> 0,
    value |-> NoValue
]

--------------------------------------------------------

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

CommitEntries(lg) == {e \in Range(lg) : ("ts" \in DOMAIN e) /\ ("prepare" \notin DOMAIN e)}
CommitOnlyTimestamps(lg) == {e.ts : e \in CommitEntries(lg)}
CommitTimestamps == {txnLog[i].ts : i \in DOMAIN txnLog}
ActiveReadTimestamps == { IF txnSnapshots[tx]["state"] = "init" THEN 0 ELSE txnSnapshots[tx].ts : tx \in DOMAIN txnSnapshots}
ActiveTransactions == {tid \in TxnId : txnSnapshots[tid]["state"] \in {"active", "prepared"}}
PreparedTransactions == {tid \in ActiveTransactions : txnSnapshots[tid]["state"] = "prepared"}
CommittedTransactions == {tid \in TxnId : txnSnapshots[tid]["state"] = "committed"}

\* Currently in this model, where transactions don't set timestamps while they're in progress,
\* the all_durable will just be the same as the newest committed timestamp.
AllDurableTs == IF CommittedTransactions = {} THEN 0 ELSE Max(CommitOnlyTimestamps(txnLog'))

\* 
\* Perform a snapshot read of a given key at timestamp.
\* 
\* That is, return the latest value associated with the key 
\* that was written at ts <= index. If no value was yet written
\* to the key, then return NotFoundReadResult.
\* 
SnapshotRead(key, ts) == 
    LET snapshotKeyWrites == 
        { i \in DOMAIN txnLog :
            /\ "data" \in DOMAIN txnLog[i] \* exclude 'prepare' entries.
            /\ \E k \in DOMAIN txnLog[i].data : k = key
            \* Determine read visibility based on commit timestamp.
            /\ txnLog[i].ts <= ts } IN
        IF snapshotKeyWrites = {}
            THEN NotFoundReadResult
            ELSE [txnLogIndex |-> Max(snapshotKeyWrites), value |-> txnLog[Max(snapshotKeyWrites)].data[key]]

\* Snapshot of the full KV store at a given index/timestamp.
SnapshotKV(tid, uid, ts, ignorePrepare) == 
    \* Local reads just read at the latest timestamp in the log.
    LET txnReadTs == ts IN
    [
        uid |-> uid,
        ts |-> txnReadTs,
        data |-> [k \in Keys |-> SnapshotRead(k, txnReadTs).value],
        prepareTs |-> 0,
        state |-> "active",
        readSet |-> {},
        writeSet |-> {},
        ignorePrepare |-> ignorePrepare,
        concurrentTxns |-> {tc \in TxnId \ {tid} : txnSnapshots[tc]["state"] \in {"active", "prepared"}}
    ]

PreparedTxnWroteKeyBehindMe(tOther, tid, k) ==
    \* \E tOther \in TxnId \ {tid}:
    \E pmind, cmind \in DOMAIN txnLog :
        \* Prepare log entry exists.
        /\ "prepare" \in DOMAIN txnLog[pmind]
        /\ txnLog[pmind].tid = tOther
        \* Commit log entry exists and is at timestamp <= our snapshot.
        /\ "data" \in DOMAIN txnLog[cmind]
        /\ txnLog[cmind].tid = tOther
        /\ txnLog[cmind].ts <= txnSnapshots[tid].ts
        /\ k \in DOMAIN txnLog[cmind].data
        \* If we wrote to this key within our transaction, then we will always read our latest write.
        \* /\ k \notin txnSnapshots[tid].writeSet

\* Does a write conflict exist for this transaction's write to a given key.
\* 
\* If someone else has written an update to this key that is not visible 
\* in your snapshot, then we need to abort.
\* 
WriteConflictExists(tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in TxnId \ {tid}:
        \* Transaction wrote to this key and is not visible in our snapshot.
        \/ /\ tid \in ActiveTransactions
           /\ txnSnapshots[tOther]["state"] \in {"active", "prepared"} 
           /\ k \in txnSnapshots[tOther].writeSet
           /\ \/ txnSnapshots[tOther].uid > txnSnapshots[tid].uid
              \* A transaction not in your snapshot wrote to the key.   
              \/ tOther \in txnSnapshots[tid]["concurrentTxns"] 
           \* Also not the case that this was a prepared transaction that now committed into our snapshot.
           \* We also don't conflict with a prepared transaction update that is now visible to us.
           /\ ~PreparedTxnWroteKeyBehindMe(tOther, tid, k)
        \* If there exists another transaction that has written to this key and
        \* committed at a timestamp newer than your snapshot, this also should
        \* manifest as a conflict, since it implies this transaction may have
        \* overlapped with you (in timestamp order).
        \/ \E ind \in DOMAIN txnLog :
            /\ "data" \in DOMAIN txnLog[ind]
            /\ txnLog[ind].ts > txnSnapshots[tid].ts
            /\ k \in (DOMAIN txnLog[ind].data)


TxnRead(tid, k) == 
    \* If a prepared transaction has committed behind our snapshot read timestamp
    \* while we were running, then we must observe the effects of its writes.
    IF  \E tOther \in TxnId \ {tid}:
        \E pmind \in DOMAIN txnLog :
        \E cmind \in DOMAIN txnLog :
            \* Prepare log entry exists.
            /\ "prepare" \in DOMAIN txnLog[pmind]
            /\ txnLog[pmind].tid = tOther
            \* Commit log entry exists and is at timestamp <= our snapshot.
            /\ "data" \in DOMAIN txnLog[cmind]
            /\ txnLog[cmind].tid = tOther
            /\ txnLog[cmind].ts <= txnSnapshots[tid].ts
            /\ k \in DOMAIN txnLog[cmind].data
            \* If we wrote to this key within our transaction, then we will always read our latest write.
            /\ k \notin txnSnapshots[tid].writeSet
        \* Snapshot read directly from the log.
        THEN SnapshotRead(k, txnSnapshots[tid].ts).value 
        \* Just read from your stored snapshot.
        ELSE txnSnapshots[tid].data[k]

UpdateSnapshot(tid, k, v) == [txnSnapshots EXCEPT ![tid].data[k] = v]

SnapshotUpdatedKeys(tid) == {
    k \in Keys : 
        /\ tid \in ActiveTransactions
        /\ k \in txnSnapshots[tid]["writeSet"]
}

CommitLogEntry(tid, commitTs) == [
    data |-> [key \in SnapshotUpdatedKeys(tid) |-> txnSnapshots[tid].data[key]],
    ts |-> commitTs, 
    tid |-> tid
]

CommitTxnToLog(tid, commitTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(txnLog, CommitLogEntry(tid, commitTs))

CommitTxnToLogWithDurable(tid, commitTs, durableTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(txnLog, CommitLogEntry(tid, commitTs) @@ [durableTs |-> durableTs])

PrepareTxnToLog(tid, prepareTs) ==
    Append(txnLog, [prepare |-> TRUE, ts |-> prepareTs, tid |-> tid])

PrepareConflict(tid, k) ==
    \* Is there another transaction prepared at T <= readTs that has modified this key?
    \E tother \in TxnId :
        /\ tother # tid
        /\ tother \in ActiveTransactions
        /\ txnSnapshots[tother]["state"] = "prepared"
        /\ k \in SnapshotUpdatedKeys(tother)
        /\ txnSnapshots[tother].prepareTs <= txnSnapshots[tid].ts

---------------------------------------------------------------------

\* Checks the status of a transaction is OK after it has executed some enabled action.
TransactionPostOpStatus(tid) == txnStatus'[tid]

\* Globally unique, monotonically increasing identifier for a transaction.
NextUID == Max({IF txnSnapshots[t]["state"] # "init" THEN txnSnapshots[t]["uid"] ELSE 0 : t \in DOMAIN txnSnapshots}) + 1

\* Start the transaction at given read timestamp 'readTs'.
StartTransaction(tid, readTs, ignorePrepare) == 
    \* Save a snapshot of the current KV store instance for this transaction to use.
    /\ tid \notin ActiveTransactions
    \* Only run transactions for a given transactionid once.
    /\ txnSnapshots[tid]["state"] \notin {"committed", "aborted"}
    \* Don't re-use transaction ids.
    /\ ~\E i \in DOMAIN (txnLog) : txnLog[i].tid = tid
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid] = SnapshotKV(tid, NextUID, readTs, ignorePrepare)]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<txnLog, stableTs, oldestTs>>
    /\ allDurableTs' = allDurableTs

\* Transactions writes key 'k' with value 'v'.
TransactionWrite(tid, k, v) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in (ActiveTransactions \ PreparedTransactions)
    \* Transactions that ignore prepare cannot perform updates, though those with "force" can.
    /\ txnSnapshots[tid]["ignorePrepare"] # "true"
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(tid, k)
          \* Update the transaction's snapshot data.
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k}, 
                                                    ![tid].data[k] = tid]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back (i.e. it is aborted).
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ txnSnapshots' = txnSnapshots
    /\ UNCHANGED <<txnLog, stableTs, oldestTs, allDurableTs>>

\* Transactions reads key 'k' with value 'v'.
TransactionRead(tid, k, v) ==
    /\ tid \in (ActiveTransactions \ PreparedTransactions)
    /\ v = TxnRead(tid, k)
    /\ \/ /\ ~PrepareConflict(tid, k) \/ txnSnapshots[tid]["ignorePrepare"] \in {"true", "force"}
          /\ v # NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["readSet"] = @ \cup {k}]
       \* Key does not exist.
       \/ /\ ~PrepareConflict(tid, k) \/ txnSnapshots[tid]["ignorePrepare"] \in {"true", "force"}
          /\ v = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_NOTFOUND]
          /\ UNCHANGED txnSnapshots
      \* Prepare conflict (transaction is not aborted).
       \/ /\ PrepareConflict(tid, k)
          /\ txnSnapshots[tid]["ignorePrepare"] = "false"
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_PREPARE_CONFLICT]
          /\ UNCHANGED txnSnapshots
    /\ UNCHANGED <<txnLog, stableTs, oldestTs, allDurableTs>>

\* Delete a key.
TransactionRemove(tid, k) ==
    /\ tid \in (ActiveTransactions \ PreparedTransactions)
    /\ txnSnapshots[tid]["ignorePrepare"] = "false"
    /\ \/ /\ ~WriteConflictExists(tid, k)
          /\ TxnRead(tid, k) # NoValue 
          \* Update the transaction's snapshot data.
          /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k}, 
                                                    ![tid].data[k] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \* If key does not exist in your snapshot then you can't remove it.
       \/ /\ ~WriteConflictExists(tid, k)
          /\ TxnRead(tid, k) = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_NOTFOUND]
          /\ UNCHANGED txnSnapshots
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ txnSnapshots' = txnSnapshots
    /\ UNCHANGED <<txnLog, stableTs, oldestTs, allDurableTs>>


\* Commits a running, active transaction whose transaction id is 'tid' and
\* commit timestamp is 'commitTs'. This terminates the transaction and persists
\* all of the transaction's write to the key-value store. Transactions cannot
\* commit at a timestamp older than the active read timestamp of any currently
\* running transaction. 
CommitTransaction(tid, commitTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ commitTs > stableTs 
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    \* Must be greater than the newest known commit timestamp.
    /\ (ActiveReadTimestamps \cup CommitTimestamps) # {} => commitTs > Max(ActiveReadTimestamps \cup CommitTimestamps)
    \* /\ ActiveReadTimestamps(n) # {} => commitTs > Max(ActiveReadTimestamps(n)) \* TODO: Check this condition against WT behavior.
    \* Commit the transaction on the KV store and write all updated keys back to the log.
    /\ txnLog' = CommitTxnToLog(tid, commitTs)
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["state"] = "committed"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ allDurableTs' = allDurableTs
    /\ UNCHANGED <<stableTs, oldestTs>>

CommitPreparedTransaction(tid, commitTs, durableTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the log.
    /\ commitTs = durableTs \* for now force these equal.
    /\ commitTs > stableTs 
    /\ tid \in ActiveTransactions
    /\ tid \in PreparedTransactions
    \* Commit timestamp must be at least as new as the prepare timestamp. Note
    \* that for prepared (i.e. distributed) transactions, though, commit
    \* timestamps may be chosen older than active read timestamps.
    /\ commitTs >= txnSnapshots[tid].prepareTs
    /\ txnLog' = CommitTxnToLogWithDurable(tid, commitTs, durableTs)
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["state"] = "committed"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ allDurableTs' = allDurableTs
    /\ UNCHANGED <<stableTs, oldestTs>>

PrepareTransaction(tid, prepareTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ prepareTs > stableTs
    /\ tid \in (ActiveTransactions \ PreparedTransactions)
    \* Prepare timestamp mustn't be less than any active read timestamp
    \* (includes our own). For now, in this model, we impose the condition that
    \* prepare timesatmps are strictly greater than any read timestamp. This
    \* doesn't appear to be a strict requirement of the underlying WiredTiger
    \* API, but we enforce it for now since we expect MongoDB distributed
    \* transactions to obey this same contract.
    /\ prepareTs > Max(ActiveReadTimestamps)
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["state"] = "prepared", ![tid]["prepareTs"] = prepareTs]
    /\ txnLog' = PrepareTxnToLog(tid, prepareTs)
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<stableTs, oldestTs, allDurableTs>>

\* Truncate (i.e. remove) the range of all keys "between" k1 and k2.
TransactionTruncate(tid, klo, khi) ==
    /\ tid \in (ActiveTransactions \ PreparedTransactions)
    /\ txnSnapshots[tid]["ignorePrepare"] = "false"
    \* Truncate succeeds even if some keys in the range don't exist.
    \* But, we only mark keys that exist for conflicts.
    /\ LET keysPresentInRange == {k \in klo..khi : TxnRead(tid, k) # NoValue} IN
        /\ \A k \in keysPresentInRange : ~WriteConflictExists(tid, k)
        \* Update the transaction's snapshot data.
        /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup keysPresentInRange, 
                                                ![tid].data = [
                                                    kx \in Keys |-> 
                                                        IF kx \in keysPresentInRange THEN NoValue ELSE txnSnapshots[tid].data[kx]]]
        /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<txnLog, stableTs, oldestTs, allDurableTs>>

AbortTransaction(tid) == 
    /\ tid \in ActiveTransactions
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![tid]["state"] = "aborted"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<txnLog, stableTs, oldestTs, allDurableTs>>

SetStableTimestamp(ts) == 
    /\ ts > stableTs
    /\ stableTs' = ts
    /\ UNCHANGED <<txnLog, txnSnapshots, txnStatus, oldestTs, allDurableTs>>

SetOldestTimestamp(ts) ==
    /\ ts > oldestTs
    /\ ts <= stableTs
    /\ oldestTs' = ts
    /\ UNCHANGED <<txnLog, txnSnapshots, txnStatus, stableTs, allDurableTs>>

\* Roll back storage state to the stable timestamp.
RollbackToStable == 
    \* Mustn't initiate a RTS call if there are any open transactions.
    /\ ActiveTransactions = {}
    /\ stableTs > 0 \* Stable timestamp has been set.
    \* Truncate all log operations at timestamps in front of the stable timestamp.
    /\ txnLog' = SelectSeq(txnLog, LAMBDA op : op.ts <= stableTs)
    /\ stableTs' = stableTs
    /\ UNCHANGED <<txnSnapshots, txnStatus, oldestTs, allDurableTs>>

\* Explicit initialization for each state variable.
Init_txnLog == <<>>
Init_txnSnapshots == [t \in TxnId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]

Init == 
    /\ txnLog = <<>>
    /\ txnSnapshots = [t \in TxnId |-> [state |-> "init"]]
    /\ txnStatus = [t \in TxnId |-> STATUS_OK]
    /\ stableTs = -1
    /\ oldestTs = -1
    /\ allDurableTs = 0

\* All ignore_prepare options. Can optionally be overwritten in configuration.
\* IgnorePrepareOptions == {"false", "true", "force"}
IgnorePrepareOptions == {"false"}

Next == 
    \/ \E tid \in TxnId, readTs \in Timestamps, ignorePrepare \in IgnorePrepareOptions : StartTransaction(tid, readTs, ignorePrepare)
    \/ \E tid \in TxnId, k \in Keys, v \in Values : TransactionWrite(tid, k, v)
    \/ \E tid \in TxnId, k \in Keys, v \in (Values \cup {NoValue}) : TransactionRead(tid, k, v)
    \/ \E tid \in TxnId, k \in Keys : TransactionRemove(tid, k)
    \/ \E tid \in TxnId, k1,k2 \in Keys : TransactionTruncate(tid, k1, k2)
    \/ \E tid \in TxnId, prepareTs \in Timestamps : PrepareTransaction(tid, prepareTs)
    \/ \E tid \in TxnId, commitTs \in Timestamps : CommitTransaction(tid, commitTs)
    \/ \E tid \in TxnId, commitTs, durableTs \in Timestamps : CommitPreparedTransaction(tid, commitTs, durableTs)
    \/ \E tid \in TxnId : AbortTransaction(tid)
    \/ \E ts \in Timestamps : SetStableTimestamp(ts)
    \/ \E ts \in Timestamps : SetOldestTimestamp(ts)
    \/ RollbackToStable


---------------------------------------------------------------------

\* Symmetry == Permutations(TxnId) \cup Permutations(Keys)
Symmetry == Permutations(TxnId)

===============================================================================