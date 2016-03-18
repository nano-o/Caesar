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

GT(c, xs) ==  
    LET max == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    IN IF max[1] < c THEN <<c, max[2]>> ELSE <<c, max[2]+1>> 
    
(***********

--algorithm Caesar {

    variables
        ballot = [p \in P |-> [c \in C |-> 0]], \* map an acceptor p to a command c to a ballot b, indicating that the acceptor p is in ballot b for command c.
        estimate = [p \in P |-> <<>>], \* maps an acceptor p and a command c to the estimate of acceptor p for command c in ballot ballot[p][c].
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
        
        \* A timestamp (of the form <<c,t>>) greater than the greatest timestamp seen by p. 
        GTReceived(p, c) == 
            LET ts == {<<c2, estimate[p][c2].ts>> : c2 \in DOMAIN estimate[p]}
            IN GT(c, ts)
        
        CmdsWithLowerT(p, c, t) == {c2 \in DOMAIN estimate[p] : <<c2, estimate[p][c2].ts>> \prec <<c,t>>}
        
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
                when ballot[p][c] = bal /\ c \notin DOMAIN estimate[p];
                when \neg Blocked(self, c, t);
                when \forall c2 \in DOMAIN estimate[p] : \neg Conflicts(p, c, t, c2); \* There is no conflict.
                with ( ds = CmdsWithLowerT(p, c, t) ) { 
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>];
                }
            }
        }
    }
    
    \* Models replying to a proposal with an ACK message.  
    macro RejectPropose(p) {
        with (c \in C) {
            with (bal = ballot[p][c], t = propose[<<c, ballot[p][c]>>]) {
                when <<c, bal>> \in DOMAIN propose;
                when ballot[p][c] = bal /\ c \notin DOMAIN estimate[p];
                when \neg Blocked(self, c, t);
                when \exists c2 \in DOMAIN estimate[p] : Conflicts(p, c, t, c2); \* There is a conflict.
                with (  ds = DOMAIN estimate[p]; t2 = GTReceived(p, c) ) {
                  \* Add the command to the local estimate:
                  estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>];
                }
            }
        }
    }
    
    macro Retry(c, b) {
        with (q \in Quorum) {
            when <<c,b>> \notin DOMAIN retry;
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2];
            when \E p2 \in q : estimate[p2][c].status = "rejected";
            with (ds = UNION {estimate[p2][c].pred : p2 \in q}, t = GT(c, {<<c, estimate[p2][c].ts>> : p2 \in q})) {
                retry := retry ++ <<<<c,b>>, [ts |-> t[2], pred |-> ds]>>;
            }
        }
    }
    
    macro RetryAck(p) {
        with (c \in C) {
            with (bal = ballot[p][c]) {
                when <<c, bal>> \in DOMAIN retry;
                when c \in DOMAIN estimate[p] => estimate[p][c].status \in {"pending", "rejected"};
                with (info = retry[<<c, ballot[p][c]>>]; t = info.ts; ds = info.pred \cup CmdsWithLowerT(p, c, t) ) {
                    estimate := [estimate EXCEPT ![p] = @ ++ <<c, [ts |-> t, status |-> "accepted", pred |-> ds]>>];
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
     
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "accepted";
            with (  ds = UNION {estimate[p2][c].pred : p2 \in q};
                    t = retry[<<c,b>>].ts ) {
                stable := stable ++ <<c, [ts |-> t, pred |-> ds]>>;
            }
        }
    }
    
    macro LearnStable(p) {
        with (c \in DOMAIN stable \cap DOMAIN estimate[p]) {
            when estimate[p][c].ts = stable[c].ts /\ estimate[p][c].pred = stable[c].pred;
            estimate := [estimate EXCEPT ![p] = [@ EXCEPT ![c] = [@ EXCEPT !.status = "stable"]]];
        }
    }
  
    process (leader \in C \times Ballot) {
        ldr:    while (TRUE) {
                    with (c = self[1], b = self[2]) {
                        either {
                            with (t \in Time) { \* use an arbitrary timestamp.
                                Propose(c, b, t); 
                            }
                        } or {
                            FastDecision(c, b);
                        } or {
                            Retry(c, b);
                        } or {
                            SlowDecision(c, b);
                        }
                    }
                }
    }
    
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        AckPropose(self);
                    } or {
                        RejectPropose(self);
                    } or {
                        LearnStable(self);
                    } or {
                        RetryAck(self);
                    }
                }
    }
    
}

*) 
\* BEGIN TRANSLATION
\* Label acc of process acc at line 197 col 17 changed to acc_
VARIABLES ballot, estimate, propose, stable, retry

(* define statement *)
Conflicts(p, c1, t1, c2) ==
    /\ <<c1,t1>> \prec <<c2, estimate[p][c2].ts>>
    /\ c1 \notin estimate[p][c2].pred

Blocks(p, c1, t1, c2) ==
    /\ Conflicts(p, c1, t1, c2)
    /\ estimate[p][c2].status \notin {"stable","accepted"}

Blocked(p, c, t) == \exists c2 \in DOMAIN estimate[p] : Blocks(p, c, t, c2)


GTReceived(p, c) ==
    LET ts == {<<c2, estimate[p][c2].ts>> : c2 \in DOMAIN estimate[p]}
    IN GT(c, ts)

CmdsWithLowerT(p, c, t) == {c2 \in DOMAIN estimate[p] : <<c2, estimate[p][c2].ts>> \prec <<c,t>>}


vars == << ballot, estimate, propose, stable, retry >>

ProcSet == (C \times Ballot) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ estimate = [p \in P |-> <<>>]
        /\ propose = <<>>
        /\ stable = <<>>
        /\ retry = <<>>

leader(self) == /\ LET c == self[1] IN
                     LET b == self[2] IN
                       \/ /\ \E t \in Time:
                               /\ \neg <<c,b>> \in DOMAIN propose
                               /\ propose' = propose ++ <<<<c,b>>, t>>
                          /\ UNCHANGED <<stable, retry>>
                       \/ /\ \E q \in FastQuorum:
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "pending"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} IN
                                    LET t == propose[<<c,b>>] IN
                                      stable' = stable ++ <<c, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, retry>>
                       \/ /\ \E q \in Quorum:
                               /\ <<c,b>> \notin DOMAIN retry
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2]
                               /\ \E p2 \in q : estimate[p2][c].status = "rejected"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} IN
                                    LET t == GT(c, {<<c, estimate[p2][c].ts>> : p2 \in q}) IN
                                      retry' = retry ++ <<<<c,b>>, [ts |-> t[2], pred |-> ds]>>
                          /\ UNCHANGED <<propose, stable>>
                       \/ /\ \E q \in Quorum:
                               /\ \A p2 \in q : ballot[p2][c] = b /\ c \in DOMAIN estimate[p2] /\ estimate[p2][c].status = "accepted"
                               /\ LET ds == UNION {estimate[p2][c].pred : p2 \in q} IN
                                    LET t == retry[<<c,b>>].ts IN
                                      stable' = stable ++ <<c, [ts |-> t, pred |-> ds]>>
                          /\ UNCHANGED <<propose, retry>>
                /\ UNCHANGED << ballot, estimate >>

acc(self) == /\ \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          LET t == propose[<<c, ballot[self][c]>>] IN
                            /\ <<c, bal>> \in DOMAIN propose
                            /\ ballot[self][c] = bal /\ c \notin DOMAIN estimate[self]
                            /\ \neg Blocked(self, c, t)
                            /\ \forall c2 \in DOMAIN estimate[self] : \neg Conflicts(self, c, t, c2)
                            /\ LET ds == CmdsWithLowerT(self, c, t) IN
                                 estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t, status |-> "pending", pred |-> ds]>>]
                \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          LET t == propose[<<c, ballot[self][c]>>] IN
                            /\ <<c, bal>> \in DOMAIN propose
                            /\ ballot[self][c] = bal /\ c \notin DOMAIN estimate[self]
                            /\ \neg Blocked(self, c, t)
                            /\ \exists c2 \in DOMAIN estimate[self] : Conflicts(self, c, t, c2)
                            /\ LET ds == DOMAIN estimate[self] IN
                                 LET t2 == GTReceived(self, c) IN
                                   estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t2[2], status |-> "rejected", pred |-> ds]>>]
                \/ /\ \E c \in DOMAIN stable \cap DOMAIN estimate[self]:
                        /\ estimate[self][c].ts = stable[c].ts /\ estimate[self][c].pred = stable[c].pred
                        /\ estimate' = [estimate EXCEPT ![self] = [@ EXCEPT ![c] = [@ EXCEPT !.status = "stable"]]]
                \/ /\ \E c \in C:
                        LET bal == ballot[self][c] IN
                          /\ <<c, bal>> \in DOMAIN retry
                          /\ c \in DOMAIN estimate[self] => estimate[self][c].status \in {"pending", "rejected"}
                          /\ LET info == retry[<<c, ballot[self][c]>>] IN
                               LET t == info.ts IN
                                 LET ds == info.pred \cup CmdsWithLowerT(self, c, t) IN
                                   estimate' = [estimate EXCEPT ![self] = @ ++ <<c, [ts |-> t, status |-> "accepted", pred |-> ds]>>]
             /\ UNCHANGED << ballot, propose, stable, retry >>

Next == (\E self \in C \times Ballot: leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

TimeStamp == P \times Time 
   
Status == {"pending","stable","accepted","rejected"}

CmdInfo == [ts : Nat, pred : SUBSET C]
CmdInfoWithStat == [ts : Nat, pred : SUBSET C, status: Status]

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
\* Last modified Fri Mar 18 18:04:57 EDT 2016 by nano
\* Created Thu Mar 17 21:48:45 EDT 2016 by nano
