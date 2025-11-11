---- MODULE Storage_anim ----
EXTENDS Sequences, Naturals, Integers, Util, TLC, Storage, SVG

Injective(f) == \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* Establish a fixed mapping to assign an ordering to elements in these sets.
\* ServerId == CHOOSE f \in [Server -> 1..Cardinality(Person)] : Injective(f)
\* RMId == CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)
\* SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : Injective(f)
\* RMId == SetToSeq(Server)
\* CHOOSE f \in [1..Cardinality(Server) -> Server] : Injective(f)

\* ---------------------------------------------
\* Animation derived from Storage.tla state
\* ---------------------------------------------

IndexOf(seq, elem) == CHOOSE i \in DOMAIN seq : seq[i] = elem

\* Sequence of nodes (for deterministic layout)
\* NodeSeq == SetToSeq(Node)

\* Compute a readable label for a single log entry
LogEntryLabel(e) ==
    LET kind == IF "prepare" \in DOMAIN e THEN "prepare" ELSE "commit"
        tid  == IF "tid" \in DOMAIN e THEN e.tid ELSE -1
        ts   == IF "ts" \in DOMAIN e THEN e.ts ELSE -1
        dur  == IF "durableTs" \in DOMAIN e THEN e.durableTs ELSE 0
    IN ToString(kind) \o " tid=" \o ToString(tid) \o " ts=" \o ToString(ts) \o (IF dur # 0 THEN (" dur=" \o ToString(dur)) ELSE "")

\* Render log of a node n as a vertical list
NodeLogElem(ox, oy) ==
    LET entries == mlog
        lines == [ i \in DOMAIN entries |->
                    LET y == oy + 16*i
                        label == LogEntryLabel(entries[i])
                    IN Text(ox, y, label, ("font-size" :> "10px")) ]
    IN Group(<<Text(ox, oy, "mlog", ("font-weight" :> "bold"))>> \o SetToSeq(Range(lines)), <<>>)

\* Render timestamps for a node n
NodeTsElem(ox, oy) ==
    Group(<<
        Text(ox, oy, "stableTs=" \o ToString(stableTs), ("fill" :> "#444" @@ "font-size" :> "10px")),
        Text(ox, oy+14, "oldestTs=" \o ToString(oldestTs), ("fill" :> "#444" @@ "font-size" :> "10px")),
        Text(ox, oy+28, "allDurableTs=" \o ToString(allDurableTs), ("fill" :> "#444" @@ "font-size" :> "10px"))
    >>, <<>>)

\* Determine a concise status string for a txn at node n
TxnStatusStr(tid) ==
    IF mtxnSnapshots[tid].committed THEN "committed"
    ELSE IF mtxnSnapshots[tid]["state"] = "aborted" THEN "aborted"
    ELSE IF mtxnSnapshots[tid]["state"] = "active" /\ ~mtxnSnapshots[tid].prepared THEN "active"
    ELSE IF "prepared" \in DOMAIN mtxnSnapshots[tid] THEN "prepared"
    ELSE "idle"

\* Render active/known transactions at node n
NodeTxnsElem(ox, oy) ==
    LET tids == SetToSeq(TxnId)
        rows == [ i \in DOMAIN tids |->
                  LET tid == tids[i]
                      y == oy + 14*i
                      snap == mtxnSnapshots[tid]
                      status == TxnStatusStr(tid)
                      tsStr == IF "ts" \in DOMAIN snap THEN ToString(snap.ts) ELSE "-"
                      prepStr == IF snap.prepared THEN "/ prepTs=" \o ToString(snap.prepareTs) ELSE ""
                      label == "txn " \o ToString(tid) \o ": " \o status \o (IF snap.active THEN (" ts=" \o tsStr \o prepStr) ELSE "")
                  IN Text(ox, y, label, ("font-size" :> "10px")) ]
    IN Group(<<Text(ox, oy, "txns[" \o "]", ("font-weight" :> "bold"))>> \o SetToSeq(Range(rows)), <<>>)

\* Layout for a single node panel
NodePanel(idx) ==
    LET baseX == 20 + 360*(idx-1)
        baseY == 20
    IN Group(<<
        Rect(baseX-10, baseY-10, 340, 220, ("fill" :> "#f9f9f9" @@ "stroke" :> "#ddd")),
        Text(baseX, baseY-20, "Node", ("font-weight" :> "bold")),
        NodeTsElem(baseX, baseY),
        NodeLogElem(baseX, baseY+50),
        NodeTxnsElem(baseX+180, baseY)
    >>, <<>>)

\* Top-level animation view aggregating all nodes
AnimView ==
    LET panels == <<NodePanel(1)>>
    IN Group(SetToSeq(Range(panels)), [transform |-> "translate(0, 0) scale(1.0)"])


===============================================================================