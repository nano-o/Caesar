------------------------------ MODULE Caesar2 ------------------------------

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
CONSTANTS N, C, MaxTime, Quorum, FastQuorum, MaxBallot

ASSUME N \in Nat /\ N > 0

P ==  1..N 

ASSUME MaxBallot \in Nat /\ MaxBallot >= 1

Ballot == 1..MaxBallot

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourth quorums.                              *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

Time == Nat

(***************************************************************************)
(* An ordering relation among pairs of the form <<pid, timestamp>>         *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    
(***************************************************************************)
(* Let's make sure that a command cannot be proposed twice.                *)
(***************************************************************************)

(***********

--algorithm Caesar {

    variables
        seen = [p \in P |-> {}],
        ballot = [p \in P |-> [c \in C |-> 1]], \* map an acceptor p to a command c to a ballot b, indicating that the acceptor p is in ballot b for command c.
        estimate = [p \in P |-> [c \in C |-> <<>>]], \* the estimate of acceptor p for command c in ballot ballot[p][c].
        propose = <<>>, \* maps a pair <<c,b>> to a timestamp t, indicating that the proposal for command c in ballot b is timestamp t.
        stable = <<>>, \* maps a c to a set of dependencies ds and a timestamp t, indicating that c has been committed with timestamp t and dependencies ds. 
        retry = <<>>, \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c is to be retried with timestamp t and dependencies ds. 

    define {

        Conflicts(p, b, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
            /\ propose[c2] \prec estimate[p][c1][b].ts
            /\ c2 \notin estimate[p][c1][b].pred
        
        Blocks(p, b, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
            /\ Conflicts(p,b,c1,c2)
            /\ estimate[p][c1][b].status \notin {"stable","accepted"}
        
        Blocked(p, b, c) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, b, c2, c)
        
        NextTimeValue(p, ts) == IF ts[2] > time[p] THEN ts[2] ELSE time[p]
        
        FastDecisionPossible(c, b, q) ==  
            q \in FastQuorum /\ \A p \in q : c \in DOMAIN estimate[p] 
                /\ b \in DOMAIN estimate[p][c] /\ estimate[p][c][b].status = "pending"
    
        RetryDecisionPossible(c, b, q) == 
            q \in Quorum /\ \A p \in q : c \in DOMAIN estimate[p] /\ b \in DOMAIN estimate[p][c]  
                /\ estimate[p][c][b].status = "accepted"
        
        \* c has been proposed by some process in ballot b.
        Proposed(c, b) == \E p \in P : c \in DOMAIN propose[p] => b \in DOMAIN propose[p][c]
        
        }
 
    \* Models broadcasting a proposal.
    macro Propose(p, b) {
        with (c \in C) {
            \* nobody proposed it before in this ballot:
            when \neg Proposed(c, b);
            \* first we have to ask the others to join our ballot...
            \* In fact in the first phase we are asking the others to allocate an instantiation for the command.
            \* A command is associated with a ballot (<<p,1>>) and a timestamp (<<p,time[p]>>).
            propose :=  [propose EXCEPT ![p] = @ ++ <<c, @[c] ++ <<1, <<p,time[p]>> >> >>]; \* Broadcast proposal, logically staring the consensus instance for c.
            ballot := [ballot EXCEPT ![p] = @ ++ <<c, 1 >>];
            time := [time EXCEPT ![p] = @ + 1];
            when time[p] \in 1..MaxTime;
        }
    }

    \* Models replying to a proposal with an ACK message.  
    macro AckPropose(p) {
          with (c \in DOMAIN proposed) {
              when \neg Blocked(self, c);
              when \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c2, c); \* There is no conflict.
              with (  cStatus = "pending";
                      \* The timestamp with which c was initially proposed: 
                      cTs = proposed[c]; 
                      cDeps = {c2 \in DOMAIN estimate[p] : estimate[p][c2].ts \prec cTs}) {
                  \* Notify the command leader of the ack:
                  phase1Ack := [phase1Ack EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, pred |-> cDeps]>>]; 
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>];
                  time := [time EXCEPT ![p] = NextTimeValue(p, cTs)];
              }
          }
    }
  
    \* Models replying to a proposal with a REJECT (also called NACK) message.
    macro RejectPropose(p) { 
        with (c \in DOMAIN proposed \ 
                (DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \union DOMAIN estimate[p])) {
            when \neg Blocked(self, c);
            when \exists c2 \in DOMAIN estimate[p] : Conflicts(p, c2, c); \* There is a conflict.
            with (  cStatus = "rejected";
                    \* The timestamp with which c was initially proposed: 
                    cTs = Max({info.ts : info \in Image(estimate[p])}); 
                    cDeps = DOMAIN estimate[p] ) {
                \* Notify the command leader of the reject:
                phase1Reject := [phase1Reject EXCEPT ![p] = @  ++ <<c, [ts |-> cTs, pred |-> cDeps]>>];
                \* Add the command to the local estimate:
                estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>];
                time := [time EXCEPT ![p] = NextTimeValue(p, cTs)];
                \* when time[p] \in Time;
            }   
        }
    }
    
    \* Models the passage of time.
    macro Tick(p) {
        time := [time EXCEPT ![p] = @+1];
        when time[p] \in 1..MaxTime;
    }
    
    \* Models a command-leader receiving a quorum of responses to its proposal in which at 
    \* least one process rejected the proposal, and then broadcasting a retry message.
    macro Retry(p) {
        with (c \in DOMAIN estimate[p] \ (DOMAIN retry \union DOMAIN stable); q \in Quorum) {
            when estimate[p][c].status \in {"pending","rejected"};
            when \A p2 \in q : c \in DOMAIN phase1Ack[p2] \union DOMAIN phase1Reject[p2];
            \* At least one node rejected the command:
            when \E p2 \in q : c \in DOMAIN phase1Reject[p2];
            with (  acked = {p2 \in q : c \in DOMAIN phase1Ack[p2]};
                    rejected = {p2 \in q : c \in DOMAIN phase1Reject[p2]};
                    pred = DOMAIN estimate[p]
                                \union UNION {phase1Ack[p2][c].pred : p2 \in acked} 
                                \union UNION {phase1Reject[p2][c].pred : p2 \in rejected};
                    tsm = Max({info.ts : info \in Image(estimate[p])}
                                \union {phase1Ack[p2][c].ts : p2 \in acked} 
                                \union {phase1Reject[p2][c].ts : p2 \in rejected});
                    ts = <<p, tsm[2]+1>>) {
                \* when ts \in TimeStamp;
                retry := retry ++ <<c, [ts |-> ts, pred |-> pred]>>;
                time := [time EXCEPT ![p] = ts[2]];
                \* when time[p] \in Time;
            }
        }
    }
    
    \* Models a process replying to a retry message.
    macro AckRetry(p) {
        with (c \in DOMAIN retry \ DOMAIN retryAck[p]) {
            when c \in DOMAIN estimate[p] => estimate[p][c].status \in {"pending","rejected"};
            with (  ts =  retry[c].ts;
                    pred = retry[c].pred \union {c2 \in DOMAIN estimate[p] : estimate[p][c2].ts \prec ts } ) {
                estimate := [estimate EXCEPT ![p] = @ ++ 
                    <<c, [ts |-> ts, status |-> "accepted", pred |-> pred]>>];
                retryAck := [retryAck EXCEPT ![p] = @ ++ <<c, [ts |-> ts, pred |-> pred]>>]
            }
        }
    }
    
    \* Note that sending stable messages in StableAfterPhase1 and StableAfterRetry is not needed to guarantee safety.
    
    \* Models a command-leader receiving a quorum of responses to its proposal message in which 
    \* all processes accepted the proposal, and then broadcasting a "stable" message.
    macro StableAfterPhase1(p) {
        with (c \in C \ (DOMAIN stable \union DOMAIN retry); q \in FastQuorum) {
            when \A p2 \in q : c \in DOMAIN phase1Ack[p2];
            with (  pred = UNION {phase1Ack[p2][c].pred : p2 \in q};
                    ts = proposed[c] ) {
                stable := stable ++ <<c, [ts |-> ts, pred |-> pred]>>;
            }
        }
    }

    \* Models a command-leader receiving a quorum of responses to its "retry" message in which 
    \* all processes accepted the proposal, and then broadcasting a "stable" message.
    macro StableAfterRetry(p) {
        with (c \in C \ DOMAIN stable, q \in Quorum) {
            when \A p2 \in q : c \in DOMAIN retryAck[p2];
            with (  pred = UNION { retryAck[p2][c].pred : p2 \in q };
                    ts = CHOOSE ts \in {retryAck[p2][c].ts : p2 \in q} : TRUE ) {
                stable := stable ++ <<c, [ts |-> ts, pred |-> pred]>>;
            }
        }
    }
    
    \* Models a process receiving a "stable" message.
    macro RcvStable(p) {
        with (c \in DOMAIN stable) {
            estimate := [estimate EXCEPT ![p] = 
                @ ++ <<c, [status |-> "stable", ts |-> stable[c].ts, pred |-> stable[c].pred]>>];
        }
    }
    
    process (proc \in P) {
        eventLoop: while (TRUE) {
                \* either { 
                    Propose(self, 1) \* }
                (* or { 
                    AckPropose(self) } 
                or { 
                    RejectPropose(self) } 
                or { 
                    Tick(self) } 
                or { 
                    Retry(self) } 
                or { 
                    AckRetry(self) } 
                or { 
                    StableAfterPhase1(self) } 
                or { 
                     StableAfterRetry(self) } 
                or { 
                    RcvStable(self) } *)
          }
      }
    } 
}

*) 
\* BEGIN TRANSLATION
VARIABLES time, seen, ballot, estimate, propose, stable, retry

(* define statement *)
Conflicts(p, b, c1, c2) ==
    /\ proposed[c2] \prec estimate[p][c1][b].ts
    /\ c2 \notin estimate[p][c1][b].pred

Blocks(p, b, c1, c2) ==
    /\ Conflicts(p,b,c1,c2)
    /\ estimate[p][c1][b].status \notin {"stable","accepted"}

Blocked(p, b, c) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, b, c2, c)

NextTimeValue(p, ts) == IF ts[2] > time[p] THEN ts[2] ELSE time[p]

FastDecisionPossible(c, b, q) ==
    q \in FastQuorum /\ \A p \in q : c \in DOMAIN estimate[p]
        /\ b \in DOMAIN estimate[p][c] /\ estimate[p][c][b].status = "pending"

RetryDecisionPossible(c, b, q) ==
    q \in Quorum /\ \A p \in q : c \in DOMAIN estimate[p] /\ b \in DOMAIN estimate[p][c]
        /\ estimate[p][c][b].status = "accepted"


Proposed(c, b) == \E p \in P : c \in DOMAIN propose[p] => b \in DOMAIN propose[p][c]


vars == << time, seen, ballot, estimate, propose, stable, retry >>

ProcSet == (P)

Init == (* Global variables *)
        /\ time = [p \in P |-> 1]
        /\ seen = [p \in P |-> {}]
        /\ ballot = [p \in P |-> <<>>]
        /\ estimate = [p \in P |-> <<>>]
        /\ propose = [p \in P |-> <<>>]
        /\ stable = [p \in P |-> <<>>]
        /\ retry = [p \in P |-> <<>>]

proc(self) == /\ \E c \in C:
                   /\ \neg Proposed(c, 1)
                   /\ propose' = [propose EXCEPT ![self] = @ ++ <<c, @[c] ++ <<1, <<self,time[self]>> >> >>]
                   /\ ballot' = [ballot EXCEPT ![self] = @ ++ <<c, 1 >>]
                   /\ time' = [time EXCEPT ![self] = @ + 1]
                   /\ time'[self] \in 1..MaxTime
              /\ UNCHANGED << seen, estimate, stable, retry >>

Next == (\E self \in P: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TimeStamp == P \times Time 
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : TimeStamp, pred : SUBSET C]
CmdInfoWithStat == [ts : TimeStamp, pred : SUBSET C, status: Status]

(***************************************************************************)
(* An invariant describing the type of the different variables.  Note that *)
(* we extensively use maps (also called functions) keyed by commands.  The *)
(* set of keys of a map m is noted DOMAIN m.                               *)
(***************************************************************************)
TypeInvariant ==
    /\ time \in [P -> Nat]
    /\ \E D \in SUBSET C : \E bs \in [D -> SUBSET Ballot] : 
            /\  DOMAIN propose = D 
            /\  \A c \in D : propose[c] \in [bs[c] -> TimeStamp]
    /\ ballot \in [P -> [C -> Ballot]]
    /\ \forall p \in P :
        /\ \E D \in SUBSET C : \E bs \in [D -> SUBSET Ballot] : 
                /\  DOMAIN estimate[p] = D
                /\  \A c \in D : estimate[p][c] \in [bs[c] -> CmdInfoWithStat]
    

RemoveHigherTs(ts, pred) == {c \in pred : stable[c].ts < ts}

(***************************************************************************)
(* An intuition: even if two different quorums q1 and q2 have different    *)
(* dependency sets for c, removing the commands that will be commited with *)
(* a higher ts yields the same dep set.                                    *)
(*                                                                         *)
(* If c2 is a disagreement point between two fast quorums q1 and q2 for    *)
(* which c1 is pending, then less than a maj has seen c2 before c1 (eq., a *)
(* maj has seen c1 before c2).  Moreover, if c2.ts < c1.ts, then c2 will   *)
(* be rejected, and thus commited with a higher ts than c1, and thus is no *)
(* real disagreement between q1 and q2.                                    *)
(*                                                                         *)
(* If c2 is a disagreement point between two classic quorums q1 and q2 for *)
(* which c1 is accepted (i.e.  after a retry), then c2.ts < c1.ts (by the  *)
(* retryAck action) and c2 has been seen by less than a quorum.  Thus \neg *)
(* FastDecisionPossible(c2).  c2.ts < c1.ts implies that c2 was not seen   *)
(* be the fast quorum that caused c1's retry.  c2 will be rejected         *)
(* anywhere and is thus not a real disagreement betwee q1 and q2.          *)
(*                                                                         *)
(* So any two quorums, on the fast or slow path, will yield the same final *)
(* dependency set.  Therefore we can use the structure of Paxos.           *)
(*                                                                         *)
(* Now we have to ensure that for any two conflicting commands c1 and c2,  *)
(* c1 depends on c2 or vice versa.                                         *)
(*                                                                         *)
(* Another invariant: if c1 is accepted, then any other command accepted   *)
(* or stable with a higher timestamp has c1 in its pred (Inv3).            *)
(***************************************************************************)



=============================================================================
\* Modification History
\* Last modified Fri Mar 18 10:07:31 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
