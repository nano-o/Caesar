------------------------------- MODULE Caesar -------------------------------

(***************************************************************************)
(* Spec of the Caesar algorithm, based on my interpretation of Balaji's    *)
(* pseudo-code.  The spec does not include crash-recovery.  We assume that *)
(* all commandes conflict (no commands commute).                           *)
(*                                                                         *)
(* We do not model the network.  Instead the processes can read each       *)
(* others private state directly.                                          *)
(***************************************************************************)


(***************************************************************************)
(* It seems to me that we can express Caesar in the framework of the BA    *)
(* using the same algorithm merging technique as for EPaxos.  Only phase 1 *)
(* is a little different with the waiting.                                 *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
(***************************************************************************)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(***************************************************************************)
(* The image of a map                                                      *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* N is the number of processes, C the set of commands.                    *)
(***************************************************************************)
CONSTANTS N, C, MaxTime, Quorum, FastQuorum

ASSUME N \in Nat /\ N > 0

P ==  1..N

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourth quorums.                              *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

Time == 1..MaxTime
TimeStamp == P \times Time 

VARIABLES time, estimate, proposed, phase1Ack, phase1Reject, stable, retry, retryAck
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : TimeStamp, pred : SUBSET C]
CmdInfoWithStat == [ts : TimeStamp, pred : SUBSET C, status: Status]

(***************************************************************************)
(* An ordering relation among pairs of the form <<pid, timestamp>>         *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x

(***************************************************************************)
(* An invariant describing the type of the different variables.  Note that *)
(* we extensively use maps (also called functions) keyed by commands.  The *)
(* set of keys of a map m is noted DOMAIN m.                               *)
(***************************************************************************)
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

(***************************************************************************)
(* The initial state.                                                      *)
(***************************************************************************)
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
    /\ proposed' = proposed ++ <<c, <<p,time[p]>>>>
    /\ time' = [time EXCEPT ![p] = @ + 1] \* increment the local time of p to avoid having two proposals with the same Time.
    /\ time[p]' \in Time 
    /\ UNCHANGED <<estimate, phase1Ack, phase1Reject, stable, retry, retryAck>>

Conflicts(p, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
    /\ proposed[c2] \prec estimate[p][c1].ts
    /\ c2 \notin estimate[p][c1].pred

Blocks(p, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
    /\ Conflicts(p,c1,c2)
    /\ estimate[p][c1].status \notin {"stable","accepted"}

Wait(p, c) == \forall c2 \in DOMAIN estimate[p] : \neg Blocks(p, c2, c)

NextTimeValue(p, ts) == IF ts[2] > time[p] THEN ts[2] ELSE time[p]

AckPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  Wait(p,c)
    /\  \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c2, c) \* There is no conflict.
    /\  LET cStatus == "pending"
            cTs == proposed[c] \* The timestamp with which c was initially proposed.
            cDeps == {c2 \in DOMAIN estimate[p] : estimate[p][c2].ts \prec cTs} 
        IN
            /\ phase1Ack' = [phase1Ack EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, pred |-> cDeps]>>] \* Notify the command leader of the ack.
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>] \* Add the command to the local estimate.
            /\ time' = [time EXCEPT ![p] = NextTimeValue(p, cTs)] /\ time[p]' \in Time
    /\ UNCHANGED <<proposed, stable, retry, retryAck, phase1Reject>>

(***************************************************************************)
(* This is the NACK, which I can't pronounce differently from ACK, and so  *)
(* I call it "reject".                                                     *)
(***************************************************************************)
RejectPropose(p) == \E c \in DOMAIN proposed :
    /\  c \notin DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \* Proposal has not been received yet.
    /\  Wait(p,c)
    /\  \exists c2 \in DOMAIN estimate[p] : Conflicts(p, c2, c) \* There is a conflict.
    /\  LET cStatus == "rejected"
            cDeps == DOMAIN estimate[p]
            cTs == proposed[c]
        IN
            /\ phase1Reject' = [phase1Reject EXCEPT ![p] = @  ++ <<c, [ts |-> cTs, pred |-> cDeps]>>] \* Notify the command leader of the reject.
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>] \* Add the command to the local estimate.
            /\ time' = [time EXCEPT ![p] = NextTimeValue(p, cTs)] /\ time[p]' \in Time
    /\ UNCHANGED <<proposed, stable, retry, retryAck, phase1Ack>>

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
    /\ c \in DOMAIN estimate[p] \* TODO: the pseudo-code does not have this.
    /\ \E q \in Quorum : 
        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2] \union DOMAIN phase1Reject[p2]
        /\ \E p2 \in q : c \in DOMAIN phase1Reject[p2] \* At least one node rejected the command.
        /\  LET pred == DOMAIN estimate[p]
                tsm == Max({info.ts : info \in Image(estimate[p])})
                ts == <<p, tsm[2]+1>>
            IN  /\ ts \in TimeStamp
                /\ retry' = retry ++ <<c, [ts |-> ts, pred |-> pred]>>
                /\ time' = [time EXCEPT ![p] = NextTimeValue(p, ts)]
    /\ UNCHANGED <<proposed, phase1Ack, phase1Reject, estimate, stable, retryAck>>

AckRetry(p) == \E c \in DOMAIN retry :
    /\  \neg c \in DOMAIN retryAck[p] \* Not acked yet.
    /\  LET ts ==  retry[c].ts
            pred == retry[c].pred
        IN 
            /\ estimate' = [estimate EXCEPT ![p] = @ ++ 
                <<c, [ts |-> ts, status |-> "accepted", pred |-> pred]>>]
            /\ retryAck' = [retryAck EXCEPT ![p] = @ ++ <<c, [ts |-> ts, pred |-> pred]>>]
    /\ UNCHANGED  <<proposed, time, phase1Ack, phase1Reject, stable, retry>>

(***************************************************************************)
(* Models the command leader sending a stable message for c.               *)
(***************************************************************************)
StableAfterPhase1(c) ==
    /\ c \notin DOMAIN stable
    /\ \E q \in Quorum :
        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2]
        /\  LET pred == UNION {phase1Ack[p2][c].pred : p2 \in q}
                ts == proposed[c]
            IN stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, estimate, retry, retryAck>>
    
StableAfterRetry(c) ==
    /\ c \notin DOMAIN stable
    /\ \E q \in Quorum :
        /\  \A p2 \in q : c \in DOMAIN retryAck[p2]
        /\  LET pred == CHOOSE pred \in {retryAck[p2][c].pred : p2 \in q} : TRUE \* All retryAcks should contain the same pred set.
                ts == CHOOSE ts \in {retryAck[p2][c].ts : p2 \in q} : TRUE \* All retryAcks should contain the same timestamp.
            IN  stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, estimate, retry, retryAck>>
    
(***************************************************************************)
(* Models a process receiving the stable message from the command leader.  *)
(***************************************************************************)
RcvStable(c, p) ==
    /\ c \in DOMAIN stable
    /\ estimate' = [estimate EXCEPT ![p] = 
        @ ++ <<c, [status |-> "stable", ts |-> stable[c].ts, pred |-> stable[c].pred]>>]
    /\ UNCHANGED <<proposed, time, phase1Ack, phase1Reject, stable, retry, retryAck>>
    
    
Next == \E p \in P : \E c \in C : 
    \/  Propose(p,c)
    \/  AckPropose(p)
    \/  RejectPropose(p)
    \/  Tick(p)
    \/  StableAfterPhase1(c)
    \/  StableAfterRetry(c)
    \/  RcvStable(c,p) 
    \/  Retry(c, p)
    \/  AckRetry(p)
    
Inv1 == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ stable[c1].ts \prec stable[c2].ts =>
    c1 \in stable[c2].pred /\ c2 \notin stable[c1].pred

=============================================================================
\* Modification History
\* Last modified Tue Mar 08 17:35:09 EST 2016 by nano
\* Created Mon Mar 07 11:08:24 EST 2016 by nano
