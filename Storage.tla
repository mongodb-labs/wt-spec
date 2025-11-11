---- MODULE Storage ----
EXTENDS Sequences, Naturals, Integers, Util, TLC

\* 
\* Formal model of the WiredTiger key-value storage interface.
\*
\* This covers many of the core facets of the storage interface utilized by
\* MongoDB nodes, when executing either single node operations or those
\* that are a part of a cross-shard, distributed transaction.
\*
\* The "return" status of each transaction operation can be checked by a client
\* by checking the value of the 'txnStatus' variable after the execution of an
\* action/transition. This is a simple way to emulate the notion of
\* return/status codes in a standard programming-oriented API.
\* 


CONSTANT Keys 
CONSTANT TxnId
CONSTANT Timestamps

CONSTANT NoValue


VARIABLE mlog

\* Stores snapshots for running transactions on the underlying MongoDB instance.
VARIABLE mtxnSnapshots

\* Stores latest operation status for each operation of a transaction (e.g.
\* records error codes, etc.)
VARIABLE txnStatus

\* Tracks the global "stable timestamp" within the storage layer.
VARIABLE stableTs

\* Tracks the global "oldest timestamp" within the storage layer.
VARIABLE oldestTs

\* Tracks the global "all durable timestamp" within the storage layer.
VARIABLE allDurableTs

vars == <<mlog, mtxnSnapshots, txnStatus, stableTs, oldestTs, allDurableTs>>


\* Status codes for transaction operations.
STATUS_OK == "OK"
STATUS_ROLLBACK == "WT_ROLLBACK"
STATUS_NOTFOUND == "WT_NOTFOUND"
STATUS_PREPARE_CONFLICT == "WT_PREPARE_CONFLICT"

WCVALUES == {"one", 
             "majority"}

RCVALUES == {"linearizable", 
             "snapshot", 
             "local",
             "available"}

LogIndices == Nat \ {0}

\* Make values the same as transaction IDs.
Values == TxnId

\* The result a read will have if no value can be found.
NotFoundReadResult == [
    mlogIndex |-> 0,
    value |-> NoValue
]

\* Log entries contain one key-value pair each, modeled as a record
LogEntries ==
    [
        key: Keys,
        value: Values
    ]

Logs == Seq(LogEntries)

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

--------------------------------------------------------

PrepareOrCommitTimestamps == {IF "ts" \in DOMAIN e THEN e.ts ELSE  0 : e \in Range(mlog)}
CommitEntries(lg) == {e \in Range(lg) : ("ts" \in DOMAIN e) /\ ("prepare" \notin DOMAIN e)}
CommitOnlyTimestamps(lg) == {e.ts : e \in CommitEntries(lg)}
CommitTimestamps == {mlog[i].ts : i \in DOMAIN mlog}

ActiveReadTimestamps == { IF ~mtxnSnapshots[tx]["state"] = "active" THEN 0 ELSE mtxnSnapshots[tx].ts : tx \in DOMAIN mtxnSnapshots}

\* Next timestamp to use for a transaction operation.
NextTs == Max(PrepareOrCommitTimestamps \cup ActiveReadTimestamps) + 1

ActiveTransactions == {tid \in TxnId : mtxnSnapshots[tid]["state"] \in {"active", "prepared"}}
PreparedTransactions == {tid \in ActiveTransactions : mtxnSnapshots[tid]["state"] = "prepared"}
CommittedTransactions == {tid \in TxnId : mtxnSnapshots[tid]["state"] = "committed"}

\* Currently in this model, where transactions don't set timestamps while they're in progress,
\* the all_durable will just be the same as the newest committed timestamp.
AllDurableTs == IF CommittedTransactions = {} THEN 0 ELSE Max(CommitOnlyTimestamps(mlog'))

\* 
\* Perform a snapshot read of a given key at timestamp.
\* 
\* That is, return the latest value associated with the key 
\* that was written at ts <= index. If no value was yet written
\* to the key, then return NotFoundReadResult.
\* 
SnapshotRead(key, ts) == 
    LET snapshotKeyWrites == 
        { i \in DOMAIN mlog :
            /\ "data" \in DOMAIN mlog[i] \* exclude 'prepare' entries.
            /\ \E k \in DOMAIN mlog[i].data : k = key
            \* Determine read visibility based on commit timestamp.
            /\ mlog[i].ts <= ts } IN
        IF snapshotKeyWrites = {}
            THEN NotFoundReadResult
            ELSE [mlogIndex |-> Max(snapshotKeyWrites), value |-> mlog[Max(snapshotKeyWrites)].data[key]]

\* Snapshot of the full KV store at a given index/timestamp.
SnapshotKV(ts, ignorePrepare) == 
    \* Local reads just read at the latest timestamp in the log.
    LET txnReadTs == ts IN
    [
        ts |-> txnReadTs,
        data |-> [k \in Keys |-> SnapshotRead(k, txnReadTs).value],
        prepareTs |-> 0,
        state |-> "active",
        readSet |-> {},
        writeSet |-> {},
        ignorePrepare |-> ignorePrepare
    ]
    

\* Not currently used but could be considered in future.
WriteReadConflictExists(n, tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in TxnId \ {tid}:
        \* Transaction is running. 
        \/ /\ tid \in ActiveTransactions
           /\ tOther \in ActiveTransactions
           \* The other transaction is on the same snapshot and read this value.
           /\ mtxnSnapshots[tOther].ts = mtxnSnapshots[tOther].ts
           /\ k \in mtxnSnapshots[tOther].readSet

\* Does a write conflict exist for this transaction's write to a given key.
WriteConflictExists(tid, k) ==
    \* Exists another running transaction on the same snapshot
    \* that has written to the same key.
    \E tOther \in TxnId \ {tid}:
        \* Transaction is running concurrently. 
        \/ /\ tid \in ActiveTransactions
           /\ tOther \in ActiveTransactions
           /\ k \in mtxnSnapshots[tOther].writeSet
        \* If there exists another transaction that has written to this key and
        \* committed at a timestamp newer than your snapshot, this also should
        \* manifest as a conflict, since it implies this transaction may have
        \* overlapped with you (in timestamp order).
        \/ \E ind \in DOMAIN mlog :
            /\ "data" \in DOMAIN mlog[ind]
            /\ mlog[ind].ts > mtxnSnapshots[tid].ts
            /\ k \in (DOMAIN mlog[ind].data)


TxnRead(tid, k) == 
    \* If a prepared transaction has committed behind our snapshot read timestamp
    \* while we were running, then we must observe the effects of its writes.
    IF  \E tOther \in TxnId \ {tid}:
        \E pmind \in DOMAIN mlog :
        \E cmind \in DOMAIN mlog :
            \* Prepare log entry exists.
            /\ "prepare" \in DOMAIN mlog[pmind]
            /\ mlog[pmind].tid = tOther
            \* Commit log entry exists and is at timestamp <= our snapshot.
            /\ "data" \in DOMAIN mlog[cmind]
            /\ mlog[cmind].tid = tOther
            /\ mlog[cmind].ts <= mtxnSnapshots[tid].ts
            /\ k \in DOMAIN mlog[cmind].data
            \* If we wrote to this key within our transaction, then we will always read our latest write.
            /\ k \notin mtxnSnapshots[tid].writeSet
        \* Snapshot read directly from the log.
        THEN SnapshotRead(k, mtxnSnapshots[tid].ts).value 
        \* Just read from your stored snapshot.
        ELSE mtxnSnapshots[tid].data[k]

UpdateSnapshot(tid, k, v) == [mtxnSnapshots EXCEPT ![tid].data[k] = v]

SnapshotUpdatedKeys(tid) == {
    k \in Keys : 
        /\ tid \in ActiveTransactions
        /\ k \in mtxnSnapshots[tid]["writeSet"]
}

CommitLogEntry(tid, commitTs) == [
    data |-> [key \in SnapshotUpdatedKeys(tid) |-> mtxnSnapshots[tid].data[key]],
    ts |-> commitTs, 
    tid |-> tid
]

CommitTxnToLog(tid, commitTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog, CommitLogEntry(tid, commitTs))

CommitTxnToLogWithDurable(tid, commitTs, durableTs) == 
    \* Even for read only transactions, we write a no-op to the log.
    Append(mlog, CommitLogEntry(tid, commitTs) @@ [durableTs |-> durableTs])


PrepareTxnToLog(tid, prepareTs) ==
    Append(mlog, [prepare |-> TRUE, ts |-> prepareTs, tid |-> tid])

TxnCanStart(tid, readTs) ==
    \* Cannot start a transaction at a timestamp T if there is another 
    \* currently prepared transaction at timestamp < T.
    ~\E tother \in TxnId :
        /\ tother \in ActiveTransactions
        /\ mtxnSnapshots[tother]["state"] = "prepared" 
        /\ mtxnSnapshots[tother].ts < readTs 

\* TODO/Question: If a transaction T1 starts at ts > P, and another transaction
\* then prepares after this at P, it appears that reads in WiredTiger from T1
\* don't actually encounter prepare conflicts (?) In MongoDB, is it ever
\* possible to prepare at a timestamp higher than an existing read timestamp? I
\* don't think so?

PrepareConflict(tid, k) ==
    \* Is there another transaction prepared at T <= readTs that has modified this key?
    \E tother \in TxnId :
        /\ tother # tid
        /\ tother \in ActiveTransactions
        /\ mtxnSnapshots[tother]["state"] = "prepared"
        /\ k \in SnapshotUpdatedKeys(tother)
        /\ mtxnSnapshots[tother].prepareTs <= mtxnSnapshots[tid].ts

---------------------------------------------------------------------

\* Checks the status of a transaction is OK after it has executed some enabled action.
TransactionPostOpStatus(tid) == txnStatus'[tid]

StartTransaction(tid, readTs, ignorePrepare) == 
    \* Start the transaction on the MDB KV store.
    \* Save a snapshot of the current MongoDB instance at this shard for this transaction to use.
    /\ tid \notin ActiveTransactions
    \* Only run transactions for a given transactionid once.
    /\ mtxnSnapshots[tid]["state"] \notin {"committed", "aborted"}
    \* Don't re-use transaction ids.
    /\ ~\E i \in DOMAIN (mlog) : mlog[i].tid = tid
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid] = SnapshotKV(readTs, ignorePrepare)]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, stableTs, oldestTs>>
    /\ allDurableTs' = allDurableTs

\* Writes to the local KV store of a shard.
TransactionWrite(tid, k, v) == 
    \* The write to this key does not overlap with any writes to the same key
    \* from other, concurrent transactions.
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    \* Transactions that ignore prepare cannot perform updates, though those with "force" can.
    /\ mtxnSnapshots[tid]["ignorePrepare"] # "true"
    \* Transactions always write their own ID as the value, to uniquely identify their writes.
    /\ v = tid
    /\ \/ /\ ~WriteConflictExists(tid, k)
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k}, 
                                                    ![tid].data[k] = tid]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back (i.e. it is aborted).
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, stableTs, oldestTs, allDurableTs>>

\* Reads from the local KV store of a shard.
TransactionRead(tid, k, v) ==
    /\ tid \in ActiveTransactions    
    /\ tid \notin PreparedTransactions
    /\ v = TxnRead(tid, k)
    /\ \/ /\ ~PrepareConflict(tid, k) \/ mtxnSnapshots[tid]["ignorePrepare"] \in {"true", "force"}
          /\ v # NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["readSet"] = @ \cup {k}]
       \* Key does not exist.
       \/ /\ ~PrepareConflict(tid, k) \/ mtxnSnapshots[tid]["ignorePrepare"] \in {"true", "force"}
          /\ v = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
      \* Prepare conflict (transaction is not aborted).
       \/ /\ PrepareConflict(tid, k)
          /\ mtxnSnapshots[tid]["ignorePrepare"] = "false"
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_PREPARE_CONFLICT]
          /\ UNCHANGED mtxnSnapshots
    /\ UNCHANGED <<mlog, stableTs, oldestTs, allDurableTs>>

\* Delete a key.
TransactionRemove(tid, k) ==
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    /\ mtxnSnapshots[tid]["ignorePrepare"] = "false"
    /\ \/ /\ ~WriteConflictExists(tid, k)
          /\ TxnRead(tid, k) # NoValue 
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k}, 
                                                    ![tid].data[k] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \* If key does not exist in your snapshot then you can't remove it.
       \/ /\ ~WriteConflictExists(tid, k)
          /\ TxnRead(tid, k) = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
       \/ /\ WriteConflictExists(tid, k)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, stableTs, oldestTs, allDurableTs>>


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
    /\ mlog' = CommitTxnToLog(tid, commitTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["state"] = "committed"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ allDurableTs' = allDurableTs
    /\ UNCHANGED <<stableTs, oldestTs>>

CommitPreparedTransaction(tid, commitTs, durableTs) == 
    \* Commit the transaction on the MDB KV store.
    \* Write all updated keys back to the shard oplog.
    /\ commitTs = durableTs \* for now force these equal.
    /\ commitTs > stableTs 
    /\ tid \in ActiveTransactions
    /\ tid \in PreparedTransactions
    \* Commit timestamp must be at least as new as the prepare timestamp. Note
    \* that for prepared (i.e. distributed) transactions, though, commit
    \* timestamps may be chosen older than active read timestamps.
    /\ commitTs >= mtxnSnapshots[tid].prepareTs
    /\ mlog' = CommitTxnToLogWithDurable(tid, commitTs, durableTs)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["state"] = "committed"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ allDurableTs' = allDurableTs
    /\ UNCHANGED <<stableTs, oldestTs>>

PrepareTransaction(tid, prepareTs) == 
    \* TODO: Eventually make this more permissive and explictly check errors on
    \* invalid commit timestamps w.r.t stable timestamp (?)
    /\ prepareTs > stableTs
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    \* Prepare timestamp mustn't be less than any active read timestamp
    \* (includes our own). For now, in this model, we impose the condition that
    \* prepare timesatmps are strictly greater than any read timestamp. This
    \* doesn't appear to be a strict requirement of the underlying WiredTiger
    \* API, but we enforce it for now since we expect MongoDB distributed
    \* transactions to obey this same contract.
    /\ prepareTs > Max(ActiveReadTimestamps)
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["state"] = "prepared", ![tid]["prepareTs"] = prepareTs]
    /\ mlog' = PrepareTxnToLog(tid, prepareTs)
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<stableTs, oldestTs, allDurableTs>>

\* Truncate a range of all keys "between" k1 and k2.
TransactionTruncate(tid, k1, k2) ==
    /\ tid \in ActiveTransactions
    /\ tid \notin PreparedTransactions
    /\ mtxnSnapshots[tid]["ignorePrepare"] = "false"
    /\ \/ /\ ~WriteConflictExists(tid, k1)
          /\ TxnRead(tid, k1) # NoValue 
          \* Update the transaction's snapshot data.
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["writeSet"] = @ \cup {k1}, 
                                                    ![tid].data[k1] = NoValue]
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
       \* If key does not exist in your snapshot then you can't remove it.
       \/ /\ ~WriteConflictExists(tid, k1)
          /\ TxnRead(tid, k1) = NoValue
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_NOTFOUND]
          /\ UNCHANGED mtxnSnapshots
       \/ /\ WriteConflictExists(tid, k1)
          \* If there is a write conflict, the transaction must roll back.
          /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_ROLLBACK]
          /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["aborted"] = TRUE]
    /\ UNCHANGED <<mlog, stableTs, oldestTs, allDurableTs>>

AbortTransaction(tid) == 
    /\ tid \in ActiveTransactions
    /\ mtxnSnapshots' = [mtxnSnapshots EXCEPT ![tid]["state"] = "aborted"]
    /\ txnStatus' = [txnStatus EXCEPT ![tid] = STATUS_OK]
    /\ UNCHANGED <<mlog, stableTs, oldestTs, allDurableTs>>

SetStableTimestamp(ts) == 
    /\ ts > stableTs
    /\ stableTs' = ts
    /\ UNCHANGED <<mlog, mtxnSnapshots, txnStatus, oldestTs, allDurableTs>>

SetOldestTimestamp(ts) ==
    /\ ts > oldestTs
    /\ ts <= stableTs
    /\ oldestTs' = ts
    /\ UNCHANGED <<mlog, mtxnSnapshots, txnStatus, stableTs, allDurableTs>>

\* Roll back storage state to the stable timestamp.
RollbackToStable == 
    \* Mustn't initiate a RTS call if there are any open transactions.
    /\ ActiveTransactions = {}
    /\ stableTs > 0 \* Stable timestamp has been set.
    \* Truncate all log operations at timestamps in front of the stable timestamp.
    /\ mlog' = SelectSeq(mlog, LAMBDA op : op.ts <= stableTs)
    /\ stableTs' = stableTs
    /\ UNCHANGED <<mtxnSnapshots, txnStatus, oldestTs, allDurableTs>>

\* Explicit initialization for each state variable.
Init_mlog == <<>>
Init_mtxnSnapshots == [t \in TxnId |-> [active |-> FALSE, committed |-> FALSE, aborted |-> FALSE]]

Init == 
    /\ mlog = <<>>
    /\ mtxnSnapshots = [t \in TxnId |-> [state |-> "init"]]
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

Symmetry == Permutations(TxnId) \cup Permutations(Keys)

===============================================================================