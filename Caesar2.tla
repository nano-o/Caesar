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
CONSTANTS N, MaxTime, Quorum, FastQuorum, NumBallots, NumCmds

ASSUME NumCmds \in Nat /\ NumCmds > 0

C == 0..(NumCmds-1)

ASSUME N \in Nat /\ N > 0

P ==  0..(N-1) 

Time == 1..MaxTime

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == 0..(NumBallots-1)

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourth quorums.                              *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}


(***************************************************************************)
(* An ordering relation among pairs of the form <<c, timestamp>>         *)
(***************************************************************************)
ts1 \prec ts2 == 
    IF ts1[2] = ts2[2]
    THEN ts1[1] < ts2[1]
    ELSE ts1[2] < ts2[2] 

Max(xs) ==  CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    
(***********

--algorithm Caesar {

    variables
        ballot = [p \in P |-> [c \in C |-> 0]], \* map an acceptor p to a command c to a ballot b, indicating that the acceptor p is in ballot b for command c.
        estimate = [p \in P |-> <<>>], \* the estimate of acceptor p for command c in ballot ballot[p][c].
        propose = <<>>, \* maps a pair <<c,b>> to a timestamp t, indicating that the proposal for command c in ballot b is timestamp t.
        stable = <<>>, \* maps a c to a set of dependencies ds and a timestamp t, indicating that c has been committed with timestamp t and dependencies ds. 
        retry = <<>>, \* maps a pair <<c,b>> to a set of dependencies ds and a timestamp t, indicating that c is to be retried with timestamp t and dependencies ds. 

    define {
        
        Conflicts(p, c1, t1, c2) ==
            /\ <<c1,t1>> \prec <<c2, estimate[p][c2].ts>>
            /\ c1 \notin estimate[p][c2].pred
        
        Blocks(p, c1, t1, c2) ==
            /\ Conflicts(p, c1, t1, c2)
            /\ estimate[p][c2].status \notin {"stable","accepted"}
        
        Blocked(p, c, t) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c, t, c2)
        
        }
 
    \* Models making a proposal in a ballot.
    macro Propose(c, b, t) {
        \* has not been proposed before in this ballot:
        when \neg <<c,b>> \in DOMAIN propose;
        propose := propose ++ <<<<c,b>>, t>>
    }

    \* Models replying to a proposal with an ACK message.  
    macro AckPropose(p) {
        with (c \in C) {
            with (bal = ballot[p][c], t = propose[<<c, ballot[p][c]>>]) {
                when <<c, bal>> \in DOMAIN propose;
                when \neg Blocked(self, c, t);
                when \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with ( ds = {c2 \in DOMAIN estimate[p] : <<c2, estimate[p][c2].ts>> \prec <<c,t>>} ) { 
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>];
                }
            }
        }
    }
    
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "pending";
            with (  ds = UNION {estimate[p2][c].pred : p2 \in q};
                    t = propose[<<c,b>>] ) {
                stable := stable ++ <<c, [ts |-> t, pred |-> ds]>>;
            }
        }
    }
  
    process (leader \in C \times Ballot) {
        ldr:    while (TRUE) {
                    either {
                        with (t \in Time) { \* use an arbitrary timestamp.
                            Propose(self[1], self[2], t); 
                        }
                    } or {
                        FastDecision(self[1], self[2]);
                    }
                }
    }
    
    process (acc \in P) {
        acc:    while (TRUE) {
                    AckPropose(self);
                }
    }
    
}

*) 
\* BEGIN TRANSLATION
\* Label acc of process acc at line 125 col 17 changed to acc_
VARIABLES ballot, estimate, propose, stable, retry

(* define statement *)
Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, estimate[p][c2].ts>>
    /\ c1 \notin estimate[p][c2].pred

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ estimate[p][c2].status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c, t, c2)


vars == << ballot, estimate, propose, stable, retry >>

ProcSet == (C \times Ballot) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> <<>>]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>

leader(self) == /\ \/ /\ \E t \in Time:
                           /\ \neg <<(self[1]),(self[2])>> \in DOMAIN propose
                           /\ propose' = propose ++ <<<<(self[1]),(self[2])>>, t>>
                      /\ UNCHANGED stable
                   \/ /\ \E q \in FastQuorum:
                           /\ \A p2 \in q : ballot[p2][(self[1])] = (self[2]) /\ (self[1]) \in DOMAIN estimate[p2] /\ estimate[p2][(self[1])].status = "pending"
                           /\ LET ds == UNION {estimate[p2][(self[1])].pred : p2 \in q} IN
                                LET t == propose[<<(self[1]),(self[2])>>] IN
                                  stable' = stable ++ <<(self[1]), [ts |-> t, pred |-> ds]>>
                      /\ UNCHANGED propose
                /\ UNCHANGED << ballot, estimate, retry >>

acc(self) == /\ \E c \in C:
                  LET bal == ballot[self][c] IN
                    LET t == propose[<<c, ballot[self][c]>>] IN
                      /\ <<c, bal>> \in DOMAIN propose
                      /\ \neg Blocked(self, c, t)
                      /\ \forall c2 \in DOMAIN estimate[self] : \neg Conflicts(self, c, t, c2)
                      /\ LET ds == {c2 \in DOMAIN estimate[self] : <<c2, estimate[self][c2].ts>> \prec <<c,t>>} IN
                           estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>]
             /\ UNCHANGED << ballot, propose, stable, retry >>

Next == (\E self \in C \times Ballot: leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TimeStamp == P \times Time 
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : Time, pred : SUBSET C]
CmdInfoWithStat == [ts : Time, pred : SUBSET C, status: Status]

(***************************************************************************)
(* An invariant describing the type of the different variables.  Note that *)
(* we extensively use maps (also called functions) keyed by commands.  The *)
(* set of keys of a map m is noted DOMAIN m.                               *)
(***************************************************************************)
TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P : \E D \in SUBSET C : estimate[p] \in [D -> CmdInfoWithStat \union {<<>>}]
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> Time]
    /\  \E D \in SUBSET C : stable \in [D -> CmdInfo]
    /\  \E D \in SUBSET (C \times Ballot) : retry \in [D -> CmdInfo]
    
Agreement == \A c1,c2 \in DOMAIN stable : c1 # c2 /\ <<c1, stable[c1].ts>> \prec <<c2, stable[c2].ts>> =>
    c1 \in stable[c2].pred

=============================================================================
\* Modification History
\* Last modified Fri Mar 18 11:48:59 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
