---- MODULE wtmodel ----
EXTENDS TLC, Sequences, Naturals


(**************************************************************************************************)
(* The constant parameters of the spec.                                                           *)
(**************************************************************************************************)

\* Set of all transaction ids.
CONSTANT txnIds

\* Set of all data store keys/values.
CONSTANT keys, values

\* An empty value.
CONSTANT Empty

(**************************************************************************************************)
(* The variables of the spec.                                                                     *)
(**************************************************************************************************)

\* The clock, which measures 'time', is just a counter, that increments (ticks) 
\* whenever a transaction starts or commits.
VARIABLE clock

\* The set of all currently running transactions.
VARIABLE runningTxns

\* The full history of all transaction operations. It is modeled as a linear 
\* sequence of events. Such a history would likely never exist in a real implementation, 
\* but it is used in the model to check the properties of snapshot isolation.
VARIABLE txnHistory

\* (NOT NECESSARY)
\* The key-value data store. In this spec, we model a data store explicitly, even though it is not actually
\* used for the verification of any correctness properties. This was added initially as an attempt the make the
\* spec more intuitive and understandable. It may play no important role at this point, however. If a property
\* check was ever added for view serializability, this, and the set of transaction snapshots, may end up being
\* useful.
VARIABLE dataStore

\* (NOT NECESSARY)
\* The set of snapshots needed for all running transactions. Each snapshot 
\* represents the entire state of the data store as of a given point in time. 
\* It is a function from transaction ids to data store snapshots. This, like the 'dataStore' variable, may 
\* now be obsolete for a spec at this level of abstraction, since the correctness properties we check do not 
\* depend on the actual data being read/written.
VARIABLE txnSnapshots

vars == <<clock, runningTxns, txnSnapshots, dataStore, txnHistory>>


(**************************************************************************************************)
(* Data type definitions.                                                                         *)
(**************************************************************************************************)

DataStoreType == [keys -> (values \cup {Empty})]
BeginOpType   == [type : {"begin"}  , txnId : txnIds , time : Nat]
CommitOpType  == [type : {"commit"} , txnId : txnIds , time : Nat, updatedKeys : SUBSET keys]
WriteOpType   == [type : {"write"}  , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
ReadOpType    == [type : {"read"}   , txnId : txnIds , key: SUBSET keys , val : SUBSET values]
AnyOpType     == UNION {BeginOpType, CommitOpType, WriteOpType, ReadOpType}

(**************************************************************************************************)
(* The type invariant and initial predicate.                                                      *)
(**************************************************************************************************)

TypeInvariant == 
    \* /\ txnHistory \in Seq(AnyOpType) seems expensive to check with TLC, so disable it.
    /\ dataStore    \in DataStoreType
    /\ txnSnapshots \in [txnIds -> (DataStoreType \cup {Empty})]
    /\ runningTxns  \in SUBSET [ id : txnIds, 
                                 startTime  : Nat, 
                                 commitTime : Nat \cup {Empty}]

Init ==  
    /\ runningTxns = {} 
    /\ txnHistory = <<>>
    /\ clock = 0
    /\ txnSnapshots = [id \in txnIds |-> Empty]
    /\ dataStore = [k \in keys |-> Empty]

(**************************************************************************************************)
(* Helpers for querying transaction histories.                                                    *)
(*                                                                                                *)
(* These are parameterized on a transaction history and a transaction id, if applicable.          *)
(**************************************************************************************************)

\* Generic TLA+ helper.
Range(f) == {f[x] : x \in DOMAIN f}

\* The begin or commit op for a given transaction id.
BeginOp(h, txnId)  == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "begin"
CommitOp(h, txnId) == CHOOSE op \in Range(h) : op.txnId = txnId /\ op.type = "commit"

\* The set of all committed/aborted transaction ids in a given history.
CommittedTxns(h) == {op.txnId : op \in {op \in Range(h) : op.type = "commit"}}
AbortedTxns(h)   == {op.txnId : op \in {op \in Range(h) : op.type = "abort"}}

\* The set of all read or write ops done by a given transaction.                   
ReadsByTxn(h, txnId)  == {op \in Range(h) : op.txnId = txnId /\ op.type = "read"}
WritesByTxn(h, txnId) == {op \in Range(h) : op.txnId = txnId /\ op.type = "write"}

\* The set of all keys read or written to by a given transaction.                   
KeysReadByTxn(h, txnId)    == { op.key : op \in ReadsByTxn(txnHistory, txnId)}
KeysWrittenByTxn(h, txnId) == { op.key : op \in WritesByTxn(txnHistory, txnId)}

\* The index of a given operation in the transaction history sequence.
IndexOfOp(h, op) == CHOOSE i \in DOMAIN h : h[i] = op

RunningTxnIds == {txn.id : txn \in runningTxns}

(**************************************************************************************************)
(*                                                                                                *)
(* Action Definitions                                                                             *)
(*                                                                                                *)
(**************************************************************************************************)


(**************************************************************************************************)
(* When a transaction starts, it gets a new, unique transaction id and is added to the set of     *)
(* running transactions.  It also "copies" a local snapshot of the data store on which it will    *)
(* perform its reads and writes against.  In a real system, this data would not be literally      *)
(* "copied", but this is the fundamental concept of snapshot isolation i.e.  that each            *)
(* transaction appears to operate on its own local snapshot of the database.                      *)
(**************************************************************************************************)
BeginTransaction(newTxnId) == 
    LET newTxn == 
        [ id |-> newTxnId, 
            startTime |-> clock+1, 
            commitTime |-> Empty] IN
    \* Must choose an unused transaction id. There must be no other operation
    \* in the history that already uses this id.
    /\ ~\E op \in Range(txnHistory) : op.txnId = newTxnId
    \* Save a snapshot of current data store for this transaction, and
    \* and append its 'begin' event to the history.
    /\ txnSnapshots' = [txnSnapshots EXCEPT ![newTxnId] = dataStore]
    /\ LET beginOp == [ type  |-> "begin", 
                        txnId |-> newTxnId, 
                        time  |-> clock+1 ] IN
        txnHistory' = Append(txnHistory, beginOp)
    \* Add transaction to the set of active transactions.
    /\ runningTxns' = runningTxns \cup {newTxn}
    \* Tick the clock.
    /\ clock' = clock + 1    
    /\ UNCHANGED <<dataStore>>
                          
                        
(**************************************************************************************************)
(* When a transaction T0 is ready to commit, it obeys the "First Committer Wins" rule.  T0 will   *)
(* only successfully commit if no concurrent transaction has already committed writes of data     *)
(* objects that T0 intends to write.  Transactions T0, T1 are considered concurrent if the        *)
(* intersection of their timespans is non empty i.e.                                              *)
(*                                                                                                *)
(*     [start(T0), commit(T0)] \cap [start(T1), commit(T1)] != {}                                 *)
(**************************************************************************************************)

\* Checks whether a given transaction is allowed to commit, based on whether it conflicts
\* with other concurrent transactions that have already committed.
TxnCanCommit(txnId) ==
    \E txn \in runningTxns : 
        /\ txn.id = txnId
        /\ ~\E op \in Range(txnHistory) :
            /\ op.type = "commit" 
            \* Did another transaction start after me.
            /\ txn.id = txnId /\ op.time > txn.startTime 
            /\ KeysWrittenByTxn(txnHistory, txnId) \cap op.updatedKeys /= {} \* Must be no conflicting keys.
         
CommitTxn(txnId) == 
    \* Transaction must be able to commit i.e. have no write conflicts with concurrent.
    \* committed transactions.
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}
    /\ TxnCanCommit(txnId)  
    /\ LET commitOp == [ type          |-> "commit", 
                         txnId         |-> txnId, 
                         time          |-> clock + 1,
                         updatedKeys   |-> KeysWrittenByTxn(txnHistory, txnId)] IN
       txnHistory' = Append(txnHistory, commitOp)            
    \* Merge this transaction's updates into the data store. If the 
    \* transaction has updated a key, then we use its version as the new
    \* value for that key. Otherwise the key remains unchanged.
    /\ dataStore' = [k \in keys |-> IF k \in KeysWrittenByTxn(txnHistory, txnId) 
                                        THEN txnSnapshots[txnId][k]
                                        ELSE dataStore[k]]
    \* Remove the transaction from the active set. 
    /\ runningTxns' = {r \in runningTxns : r.id # txnId}
    /\ clock' = clock + 1
    \* We can leave the snapshot around, since it won't be used again.
    /\ UNCHANGED <<txnSnapshots>>

(**************************************************************************************************)
(* In this spec, a transaction aborts if and only if it cannot commit, due to write conflicts.    *)
(**************************************************************************************************)
AbortTxn(txnId) ==
    \* If a transaction can't commit due to write conflicts, then it
    \* must abort.
    /\ txnId \in RunningTxnIds
    \* Must not be a no-op transaction.
    /\ (WritesByTxn(txnHistory, txnId) \cup ReadsByTxn(txnHistory, txnId)) /= {}
    /\ ~TxnCanCommit(txnId)
    /\ LET abortOp == [ type   |-> "abort", 
                        txnId  |-> txnId, 
                        time   |-> clock + 1] IN    
       txnHistory' = Append(txnHistory, abortOp)
    /\ runningTxns' = {r \in runningTxns : r.id # txnId} \* transaction is no longer running.
    /\ clock' = clock + 1
    \* No changes are made to the data store.
    /\ UNCHANGED <<dataStore, txnSnapshots>>

(***************************************************************************************************)
(* Read and write operations executed by transactions.                                            *)
(*                                                                                                *)
(* As a simplification, and to limit the size of potential models, we allow transactions to only  *)
(* read or write to the same key once.  The idea is that it limits the state space without loss   *)
(* of generality.                                                                                 *)
(**************************************************************************************************)

TxnRead(txnId, k) == 
    \* Read from this transaction's snapshot.
    /\ txnId \in RunningTxnIds
    /\ LET valRead == txnSnapshots[txnId][k]
        readOp == [ type  |-> "read", 
                    txnId |-> txnId, 
                    key   |-> k, 
                    val   |-> valRead] IN
        /\ k \notin KeysReadByTxn(txnHistory, txnId)   
        /\ txnHistory' = Append(txnHistory, readOp)
        /\ UNCHANGED <<dataStore, clock, runningTxns, txnSnapshots>>
                   
TxnUpdate(txnId, k, v) == 
    /\ txnId \in RunningTxnIds
    /\ LET writeOp == [ type  |-> "write", 
                        txnId |-> txnId, 
                        key   |-> k, 
                        val   |-> v] IN  
        /\ k \notin KeysWrittenByTxn(txnHistory, txnId)
        \* We update the transaction's snapshot, not the actual data store.
        /\ LET updatedSnapshot == [txnSnapshots[txnId] EXCEPT ![k] = v] IN
            txnSnapshots' = [txnSnapshots EXCEPT ![txnId] = updatedSnapshot]
        /\ txnHistory' = Append(txnHistory, writeOp)
        /\ UNCHANGED <<dataStore, runningTxns, clock>>

(**************************************************************************************************)
(* The next-state relation and spec definition.                                                   *)
(*                                                                                                *)
(* Since it is desirable to have TLC check for deadlock, which may indicate bugs in the spec or   *)
(* in the algorithm, we want to explicitly define what a "valid" termination state is.  If all    *)
(* transactions have run and either committed or aborted, we consider that valid termination, and *)
(* is allowed as an infinite suttering step.                                                      *)
(*                                                                                                *)
(* Also, once a transaction knows that it cannot commit due to write conflicts, we don't let it   *)
(* do any more reads or writes, so as to eliminate wasted operations.  That is, once we know a    *)
(* transaction can't commit, we force its next action to be abort.                                *)
(**************************************************************************************************)           

AllTxnsFinished == AbortedTxns(txnHistory) \cup CommittedTxns(txnHistory) = txnIds
    
Next == 
    \/ \E tid \in txnIds : BeginTransaction(tid)
    \* Ends a given transaction by either committing or aborting it. To exclude uninteresting 
    \* histories, we require that a transaction does at least one operation before committing or aborting. 
    \* Assumes that the given transaction is currently running.
    \/ \E tid \in txnIds : CommitTxn(tid)
    \/ \E tid \in txnIds : AbortTxn(tid)
    \* Transaction reads or writes a key. We limit transactions
    \* to only read or write the same key once.
    \/ \E tid \in txnIds, k \in keys : TxnRead(tid, k)
    \/ \E tid \in txnIds, k \in keys, v \in values : TxnUpdate(tid, k, v)
    \/ (AllTxnsFinished /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====