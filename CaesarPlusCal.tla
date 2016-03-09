--------------------------- MODULE CaesarPlusCal ---------------------------

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

Time == Nat

(***************************************************************************)
(* An ordering relation among pairs of the form <<pid, timestamp>>         *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    
(***********

--algorithm Caesar {

    variables 
        time  = [p \in P |-> 1],
        estimate = [p \in P |-> <<>>],
        proposed = <<>>,
        phase1Ack = [p \in P |-> <<>>],
        phase1Reject = [p \in P |-> <<>>],
        stable = <<>>,
        retry = <<>>,
        retryAck = [p \in P |-> <<>>]

    define {

        Conflicts(p, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
            /\ proposed[c2] \prec estimate[p][c1].ts
            /\ c2 \notin estimate[p][c1].pred
        
        Blocks(p, c1, c2) == \* c1 must be in estimate[p] and c2 must be in proposed for this definition to make sense
            /\ Conflicts(p,c1,c2)
            /\ estimate[p][c1].status \notin {"stable","accepted"}
        
        Blocked(p, c) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c2, c)
        
        NextTimeValue(p, ts) == IF ts[2] > time[p] THEN ts[2] ELSE time[p]

        }
 
    \* Models broadcasting a proposal.
    macro Propose(p) {
        with (c \in C \ DOMAIN proposed) {
            proposed :=  proposed ++ <<c, <<p,time[p]>>>>;
            time := [time EXCEPT ![p] = @ + 1];
            when time[p] \in 1..MaxTime;
        }
    }

    \* Models replying to a proposal with an ACK message.   
    macro AckPropose(p) {
          with (c \in DOMAIN proposed \ 
                  (DOMAIN phase1Ack[p] \union DOMAIN phase1Reject[p] \union DOMAIN estimate[p])) {
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
                  \* when time[p] \in Time;
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
                    pred = retry[c].pred 
                        \union {c2 \in DOMAIN estimate[p] : estimate[p][c2].ts \prec ts } ) {
                estimate := [estimate EXCEPT ![p] = @ ++ 
                    <<c, [ts |-> ts, status |-> "accepted", pred |-> pred]>>];
                retryAck := [retryAck EXCEPT ![p] = @ ++ <<c, [ts |-> ts, pred |-> pred]>>]
            }
        }
    }
    
    \* Models a command-leader receiving a quorum of responses to its proposal message in which 
    \* all processes accepted the proposal, and then broadcasting a "stable" message.
    macro StableAfterPhase1(p) {
        with (c \in C \ (DOMAIN stable \union DOMAIN retry); q \in Quorum) {
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
                either { 
                    Propose(self) }
                or { 
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
                    RcvStable(self) }
          }
      }
    } 
}

*) 
\* BEGIN TRANSLATION
VARIABLES time, estimate, proposed, phase1Ack, phase1Reject, stable, retry, 
          retryAck

(* define statement *)
Conflicts(p, c1, c2) ==
    /\ proposed[c2] \prec estimate[p][c1].ts
    /\ c2 \notin estimate[p][c1].pred

Blocks(p, c1, c2) ==
    /\ Conflicts(p,c1,c2)
    /\ estimate[p][c1].status \notin {"stable","accepted"}

Blocked(p, c) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c2, c)

NextTimeValue(p, ts) == IF ts[2] > time[p] THEN ts[2] ELSE time[p]


vars == << time, estimate, proposed, phase1Ack, phase1Reject, stable, retry, 
           retryAck >>

ProcSet == (P)

Init == (* Global variables *)
        /\ time = [p \in P |-> 1]
        /\ estimate = [p \in P |-> <<>>]
        /\ proposed = <<>>
        /\ phase1Ack = [p \in P |-> <<>>]
        /\ phase1Reject = [p \in P |-> <<>>]
        /\ stable = <<>>
        /\ retry = <<>>
        /\ retryAck = [p \in P |-> <<>>]

proc(self) == \/ /\ \E c \in C \ DOMAIN proposed:
                      /\ proposed' = proposed ++ <<c, <<self,time[self]>>>>
                      /\ time' = [time EXCEPT ![self] = @ + 1]
                      /\ time'[self] \in Time
                 /\ UNCHANGED <<estimate, phase1Ack, phase1Reject, stable, retry, retryAck>>
              \/ /\ \E c \in     DOMAIN proposed \
                             (DOMAIN phase1Ack[self] \union DOMAIN phase1Reject[self] \union DOMAIN estimate[self]):
                      /\ \neg Blocked(self, c)
                      /\ \forall c2 \in DOMAIN estimate[self] : \neg Conflicts(self, c2, c)
                      /\ LET cStatus == "pending" IN
                           LET cTs == proposed[c] IN
                             LET cDeps == {c2 \in DOMAIN estimate[self] : estimate[self][c2].ts \prec cTs} IN
                               /\ phase1Ack' = [phase1Ack EXCEPT ![self] = @ ++ <<c, [ts |-> cTs, pred |-> cDeps]>>]
                               /\ estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>]
                               /\ time' = [time EXCEPT ![self] = NextTimeValue(self, cTs)]
                 /\ UNCHANGED <<proposed, phase1Reject, stable, retry, retryAck>>
              \/ /\ \E c \in     DOMAIN proposed \
                             (DOMAIN phase1Ack[self] \union DOMAIN phase1Reject[self] \union DOMAIN estimate[self]):
                      /\ \neg Blocked(self, c)
                      /\ \exists c2 \in DOMAIN estimate[self] : Conflicts(self, c2, c)
                      /\ LET cStatus == "rejected" IN
                           LET cTs == Max({info.ts : info \in Image(estimate[self])}) IN
                             LET cDeps == DOMAIN estimate[self] IN
                               /\ phase1Reject' = [phase1Reject EXCEPT ![self] = @  ++ <<c, [ts |-> cTs, pred |-> cDeps]>>]
                               /\ estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> cTs, status |-> cStatus, pred |-> cDeps]>>]
                               /\ time' = [time EXCEPT ![self] = NextTimeValue(self, cTs)]
                 /\ UNCHANGED <<proposed, phase1Ack, stable, retry, retryAck>>
              \/ /\ time' = [time EXCEPT ![self] = @+1]
                 /\ time'[self] \in Time
                 /\ UNCHANGED <<estimate, proposed, phase1Ack, phase1Reject, stable, retry, retryAck>>
              \/ /\ \E c \in DOMAIN estimate[self] \ (DOMAIN retry \union DOMAIN stable):
                      \E q \in Quorum:
                        /\ estimate[self][c].status \in {"pending","rejected"}
                        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2] \union DOMAIN phase1Reject[p2]
                        /\ \E p2 \in q : c \in DOMAIN phase1Reject[p2]
                        /\ LET acked == {p2 \in q : c \in DOMAIN phase1Ack[p2]} IN
                             LET rejected == {p2 \in q : c \in DOMAIN phase1Reject[p2]} IN
                               LET pred == DOMAIN estimate[self]
                                                \union UNION {phase1Ack[p2][c].pred : p2 \in acked}
                                                \union UNION {phase1Reject[p2][c].pred : p2 \in rejected} IN
                                 LET tsm == Max({info.ts : info \in Image(estimate[self])}
                                                  \union {phase1Ack[p2][c].ts : p2 \in acked}
                                                  \union {phase1Reject[p2][c].ts : p2 \in rejected}) IN
                                   LET ts == <<self, tsm[2]+1>> IN
                                     /\ retry' = retry ++ <<c, [ts |-> ts, pred |-> pred]>>
                                     /\ time' = [time EXCEPT ![self] = ts[2]]
                 /\ UNCHANGED <<estimate, proposed, phase1Ack, phase1Reject, stable, retryAck>>
              \/ /\ \E c \in DOMAIN retry \ DOMAIN retryAck[self]:
                      /\ c \in DOMAIN estimate[self] => estimate[self][c].status \in {"pending","rejected"}
                      /\ LET ts == retry[c].ts IN
                           LET pred ==    retry[c].pred
                                       \union {c2 \in DOMAIN estimate[self] : estimate[self][c2].ts \prec ts } IN
                             /\ estimate' =         [estimate EXCEPT ![self] = @ ++
                                            <<c, [ts |-> ts, status |-> "accepted", pred |-> pred]>>]
                             /\ retryAck' = [retryAck EXCEPT ![self] = @ ++ <<c, [ts |-> ts, pred |-> pred]>>]
                 /\ UNCHANGED <<time, proposed, phase1Ack, phase1Reject, stable, retry>>
              \/ /\ \E c \in C \ (DOMAIN stable \union DOMAIN retry):
                      \E q \in Quorum:
                        /\ \A p2 \in q : c \in DOMAIN phase1Ack[p2]
                        /\ LET pred == UNION {phase1Ack[p2][c].pred : p2 \in q} IN
                             LET ts == proposed[c] IN
                               stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
                 /\ UNCHANGED <<time, estimate, proposed, phase1Ack, phase1Reject, retry, retryAck>>
              \/ /\ \E c \in C \ DOMAIN stable:
                      \E q \in Quorum:
                        /\ \A p2 \in q : c \in DOMAIN retryAck[p2]
                        /\ LET pred == UNION { retryAck[p2][c].pred : p2 \in q } IN
                             LET ts == CHOOSE ts \in {retryAck[p2][c].ts : p2 \in q} : TRUE IN
                               stable' = stable ++ <<c, [ts |-> ts, pred |-> pred]>>
                 /\ UNCHANGED <<time, estimate, proposed, phase1Ack, phase1Reject, retry, retryAck>>
              \/ /\ \E c \in DOMAIN stable:
                      estimate' =         [estimate EXCEPT ![self] =
                                  @ ++ <<c, [status |-> "stable", ts |-> stable[c].ts, pred |-> stable[c].pred]>>]
                 /\ UNCHANGED <<time, proposed, phase1Ack, phase1Reject, stable, retry, retryAck>>

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
    /\ \E D \in SUBSET C : proposed \in [D -> TimeStamp]
    /\ \forall p \in P :
        /\ \E D \in SUBSET C : estimate[p] \in [D -> CmdInfoWithStat]
        /\ \E D \in SUBSET C : phase1Ack[p] \in [D -> CmdInfo]
        /\ \E D \in SUBSET C : phase1Reject[p] \in [D -> CmdInfo]
        /\ \E D \in SUBSET C : retryAck[p] \in [D -> CmdInfo]
    /\ \E D \in SUBSET C : stable \in [D -> CmdInfo]
    /\ \E D \in SUBSET C : retry \in [D -> CmdInfo]
    
Inv1 == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ stable[c1].ts \prec stable[c2].ts =>
    c1 \in stable[c2].pred
    
(* Model-checked: 70M states, diameter 33, 3 nodes, 3 commands, MaxTime=2; 33 minutes on whitewhale *)

=============================================================================
\* Modification History
\* Last modified Wed Mar 09 14:42:12 EST 2016 by nano
\* Created Wed Mar 09 08:50:42 EST 2016 by nano
