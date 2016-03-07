------------------------------- MODULE Caesar -------------------------------

(***************************************************************************)
(* It seems to me that we can express Caesar in the framework of the BA    *)
(* using the same algorithm merging technique as for EPaxos.  Only phase 1 *)
(* is a little different with the waiting.                                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, C, MaxTime, Quorum


ASSUME N \in Nat /\ N > 0

P ==  1..N

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}

(***************************************************************************)
(* Majority quorums.                                                       *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : Cardinality(Q) > Cardinality(P) \div 2}

Time == 1..MaxTime

TimeStamp == P \times Time 

VARIABLES time, seen, proposed, phase1Ack, phase1Reject, stable
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : TimeStamp, pred : SUBSET C]

CmdInfoWithStat == [ts : TimeStamp, pred : SUBSET C, status: Status]

ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

TypeInvariant ==
    /\ time \in [P -> Nat]
    /\ \E D \in SUBSET C : proposed \in [D -> TimeStamp]
    /\ \forall p \in P :
        /\ \E D \in SUBSET C : seen[p] \in [D -> CmdInfoWithStat]
        /\ \E D \in SUBSET C : phase1Ack[p] \in [D -> CmdInfo]
        /\ \E D \in SUBSET C : phase1Reject[p] \in [D -> CmdInfo]
    /\ \E D \in SUBSET C : stable \in [D -> [ts: TimeStamp, pred : SUBSET C]]


Inv1 == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ stable[c1].ts \prec stable[c2].ts =>
    c1 \in stable[c2].pred /\ c2 \notin stable[c1].pred

Init ==
    /\ time = [p \in P |-> 1]
    /\ seen = [p \in P |-> <<>>]
    /\ proposed = <<>>
    /\ phase1Ack = [p \in P |-> <<>>]
    /\ phase1Reject = [p \in P |-> <<>>]
    /\ stable = <<>>

Propose(p, c) == 
    /\ \forall c2 \in DOMAIN proposed : c2 # c \* no duplicate commands
    /\ proposed' = [c2 \in DOMAIN proposed \cup {c} |-> 
        IF c2 = c THEN <<p,time[p]>> ELSE proposed[c2]]
    /\ time' = [time EXCEPT ![p] = @ + 1] \* increment the local time of p to avoid having two proposals with the same Time.
    /\ time[p]' \in Time 
    /\ UNCHANGED <<seen, phase1Ack, phase1Reject, stable>>

Conflicts(p, c1, c2) == \* c1 must be in seen[p] and c2 must be in proposed
    /\ proposed[c2] \prec seen[p][c1].ts
    /\ c2 \notin seen[p][c1].pred

Blocks(p, c1, c2) == 
    /\ Conflicts(p,c1,c2)
    /\ seen[p][c1].status \notin {"stable","accepted"}

RcvPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  \forall c2 \in DOMAIN seen[p] : \neg Blocks(p, c2, c) \* The wait condition
    /\  IF \exists c2 \in DOMAIN seen[p] : Conflicts(p, c2, c)
        THEN LET 
                cStatus == "rejected"
                cDeps == DOMAIN seen[p]
                cTs == proposed[c] 
            IN
                /\ phase1Reject' = [phase1Reject EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                    IF c2 = c THEN [ts |-> cTs, pred |-> cDeps]
                    ELSE @[c2]]]
                /\ seen' = [seen EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                        IF c2 = c THEN [ts |-> cTs, status |-> cStatus, pred |-> cDeps]
                        ELSE @[c2]]]
                /\ UNCHANGED phase1Ack
        ELSE LET
                cStatus == "pending"
                cTs == proposed[c] 
                cDeps == {c2 \in DOMAIN seen[p] : seen[p][c2].ts \prec cTs} 
            IN
                /\ phase1Ack' = [phase1Ack EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                    IF c2 = c THEN [ts |-> cTs, pred |-> cDeps]
                    ELSE @[c2]]]
                /\ seen' = [seen EXCEPT ![p] = [c2 \in DOMAIN @ \union {c} |->
                        IF c2 = c THEN [ts |-> cTs, status |-> cStatus, pred |-> cDeps]
                        ELSE @[c2]]]
                /\ UNCHANGED phase1Reject
    /\ UNCHANGED <<proposed, time, stable>>

Tick(p) == 
    /\ time' = [time EXCEPT ![p] = @+1]
    /\ time[p]' \in Time
    /\ UNCHANGED <<proposed, seen, phase1Ack, phase1Reject, stable>>

(***************************************************************************)
(* Models the command leader sending a stable message for c.               *)
(***************************************************************************)
Stable(c) ==
    /\ c \notin DOMAIN stable
    /\ \E q \in Quorum : 
        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2]
        /\  LET pred == UNION {phase1Ack[p2][c].pred : p2 \in q}
                ts == proposed[c]
            IN
                /\ stable' = [c2 \in DOMAIN stable \union {c} |->
                    IF c2 = c THEN [ts |-> ts, pred |-> pred]
                    ELSE stable[c2]]
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, seen>>
    
    
(***************************************************************************)
(* Models a process receiving the stable message from the command leader.  *)
(* Useless for now.                                                        *)
(***************************************************************************)
RcvStable(c, p) ==
    /\ c \in DOMAIN seen[p]
    /\ c \in DOMAIN stable
    /\ seen' = [seen EXCEPT ![p] = [@ EXCEPT ![c] = 
        [@ EXCEPT !.status = "stable", !.ts = stable[c].ts, !.pred = stable[c].pred]]]
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, stable>>
    
    
Next == \E p \in P : \E c \in C : 
    \/  Propose(p,c)
    \/  RcvPropose(p)
    \/  Tick(p)
    \/  Stable(c)
    \*\/  RcvStable(c,p) 
    


=============================================================================
\* Modification History
\* Last modified Mon Mar 07 13:58:37 EST 2016 by nano
\* Created Mon Mar 07 11:08:24 EST 2016 by nano
