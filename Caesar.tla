------------------------------- MODULE Caesar -------------------------------

(***************************************************************************)
(* It seems to me that we can express Caesar in the framework of the BA    *)
(* using the same algorithm merging technique as for EPaxos.  Only phase 1 *)
(* is a little different with the waiting.                                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

Image(f) == {f[x] : x \in DOMAIN f}

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

VARIABLES time, estimate, proposed, phase1Ack, phase1Reject, stable, retry, retryAck
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : TimeStamp, pred : SUBSET C]

CmdInfoWithStat == [ts : TimeStamp, pred : SUBSET C, status: Status]

ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x

TypeInvariant ==
    /\ time \in [P -> Nat]
    /\ \E D \in SUBSET C : proposed \in [D -> TimeStamp]
    /\ \forall p \in P :
        /\ \E D \in SUBSET C : estimate[p] \in [D -> CmdInfoWithStat]
        /\ \E D \in SUBSET C : phase1Ack[p] \in [D -> CmdInfo]
        /\ \E D \in SUBSET C : phase1Reject[p] \in [D -> CmdInfo]
        /\ \E D \in SUBSET C : retryAck[p] \in [D -> CmdInfo]
    /\ \E D \in SUBSET C : stable \in [D -> CmdInfo]
    /\ \E D \in SUBSET C : retry \in [D -> CmdInfo]


Init ==
    /\ time = [p \in P |-> 1]
    /\ estimate = [p \in P |-> <<>>]
    /\ proposed = <<>>
    /\ phase1Ack = [p \in P |-> <<>>]
    /\ phase1Reject = [p \in P |-> <<>>]
    /\ stable = <<>>
    /\ retry = <<>>
    /\ retryAck = [p \in P |-> <<>>]

Propose(p, c) == 
    /\ \forall c2 \in DOMAIN proposed : c2 # c \* no duplicate commands
    /\ proposed' = [c2 \in DOMAIN proposed \cup {c} |-> 
        IF c2 = c THEN <<p,time[p]>> ELSE proposed[c2]]
    /\ time' = [time EXCEPT ![p] = @ + 1] \* increment the local time of p to avoid having two proposals with the same Time.
    /\ time[p]' \in Time 
    /\ UNCHANGED <<estimate, phase1Ack, phase1Reject, stable, retry, retryAck>>

Conflicts(p, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed
    /\ proposed[c2] \prec estimate[p][c1].ts
    /\ c2 \notin estimate[p][c1].pred

Blocks(p, c1, c2) == 
    /\ Conflicts(p,c1,c2)
    /\ estimate[p][c1].status \notin {"stable","accepted"}

Wait(p, c) == \forall c2 \in DOMAIN estimate[p] : \neg Blocks(p, c2, c) 

AckPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  Wait(p,c)
    /\  \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c2, c)
    /\  LET cStatus == "pending"
            cTs == proposed[c] 
            cDeps == {c2 \in DOMAIN estimate[p] : estimate[p][c2].ts \prec cTs} 
        IN
            /\ phase1Ack' = [phase1Ack EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, pred |-> cDeps]>>]
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>]
            /\ UNCHANGED phase1Reject
    /\ UNCHANGED <<proposed, time, stable, retry, retryAck>>

RejectPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  Wait(p,c)
    /\  \exists c2 \in DOMAIN estimate[p] : Conflicts(p, c2, c)
    /\  LET cStatus == "rejected"
            cDeps == DOMAIN estimate[p]
            cTs == proposed[c] 
        IN
            /\ phase1Reject' = [phase1Reject EXCEPT ![p] = @  ++ <<c, [ts |-> cTs, pred |-> cDeps]>>]
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>]
            /\ UNCHANGED phase1Ack
    /\ UNCHANGED <<proposed, time, stable, retry, retryAck>>

Tick(p) ==
    /\ time' = [time EXCEPT ![p] = @+1]
    /\ time[p]' \in Time
    /\ UNCHANGED <<proposed, estimate, phase1Ack, phase1Reject, stable, retry, retryAck>>

(***************************************************************************)
(* Model a command leader starting the retry phase.  Note that here any    *)
(* node can do this.  TODO: is this bad?                                   *)
(***************************************************************************)
Retry(c, p) ==
    /\ c \notin DOMAIN retry
    /\ c \in DOMAIN estimate[p]
    /\ \E q \in Quorum : 
        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2] \union DOMAIN phase1Reject[p2]
        /\ \E p2 \in q : c \in DOMAIN phase1Reject[p2]
        /\  LET pred == DOMAIN estimate[p]
                tsm == Max({info.ts : info \in Image(estimate[p])})
                ts == <<p, tsm[2]+1>>
            IN  /\ ts \in TimeStamp
                /\ retry' = retry ++ <<c, [ts |-> ts, pred |-> pred]>>
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, estimate, stable, retryAck>>

AckRetry(p) == \E c \in DOMAIN retry :
    /\  \neg c \in DOMAIN retryAck[p]
    /\  LET ts ==  retry[c].ts
            pred == {c3 \in DOMAIN estimate[p] : estimate[p][c3].ts \prec retry[c].ts}
        IN 
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ 
                <<c, [ts |-> ts, status |-> "accepted", pred |-> pred]>>]
            /\ retryAck' = [retryAck EXCEPT ![p] = @ ++ <<c, [ts |-> ts, pred |-> pred]>>]
    /\ UNCHANGED  <<proposed, time, phase1Ack, phase1Reject, stable, retry>>

(***************************************************************************)
(* Models the command leader sending a stable message for c.               *)
(***************************************************************************)
Stable(c) ==
    /\ c \notin DOMAIN stable
    /\ \E q \in Quorum :
        \/  /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2]
            /\  LET pred == UNION {phase1Ack[p2][c].pred : p2 \in q}
                    ts == proposed[c]
                IN
                    stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
        \/  /\  \A p2 \in q : c \in DOMAIN retryAck[p2]
            /\  LET pred == UNION {retryAck[p2][c].pred : p2 \in q}
                    ts == CHOOSE ts \in {retryAck[p2][c].ts : p2 \in q} : TRUE
                IN  stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, estimate, retry, retryAck>>
    
(***************************************************************************)
(* Models a process receiving the stable message from the command leader.  *)
(***************************************************************************)
RcvStable(c, p) ==
    /\ c \in DOMAIN estimate[p]
    /\ c \in DOMAIN stable
    /\ estimate' = [estimate EXCEPT ![p] = [@ EXCEPT ![c] = 
        [@ EXCEPT !.status = "stable", !.ts = stable[c].ts, !.pred = stable[c].pred]]]
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, stable, retry, retryAck>>
    
    
Next == \E p \in P : \E c \in C : 
    \/  Propose(p,c)
    \/  AckPropose(p)
    \/  RejectPropose(p)
    \/  Tick(p)
    \/  Stable(c)
    \/  RcvStable(c,p) 
    \/  Retry(c, p)
    \/  AckRetry(p)
    
Inv1 == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ stable[c1].ts \prec stable[c2].ts =>
    c1 \in stable[c2].pred /\ c2 \notin stable[c1].pred

=============================================================================
\* Modification History
\* Last modified Mon Mar 07 16:17:46 EST 2016 by nano
\* Created Mon Mar 07 11:08:24 EST 2016 by nano
