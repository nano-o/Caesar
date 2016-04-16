---------------------- MODULE AbstractLeaderlessPaxos ----------------------

EXTENDS Naturals, FiniteSets, TLC, Sequences, Integers

(***************************************************************************)
(* Adding a key-value mapping (kv[1] is the key, kv[2] the value) to a map *)
(***************************************************************************)
f ++ kv == [x \in DOMAIN f \union {kv[1]} |-> IF x = kv[1] THEN kv[2] ELSE f[x]]

(***************************************************************************)
(* The image of a map                                                      *)
(***************************************************************************)
Image(f) == {f[x] : x \in DOMAIN f}

(***************************************************************************)
(* Ballots are of the form <<b,i>>, where b is the main ballot number and  *)
(* i the sub-ballot number.  Ballots can be compared:                      *)
(***************************************************************************)
bal1 \prec bal2 == 
    IF bal1[1] = bal2[1]
    THEN bal1[2] < bal2[2]
    ELSE bal1[1] < bal2[1]

bal1 \preceq bal2 ==
    bal1 \prec bal2 \/ bal1 = bal2

CONSTANTS P, Quorum, FastQuorum, NumBallots, C

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == (0..(NumBallots-1)) \times {1,2} \* We have two sub-ballots

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

(***************************************************************************)
(* Majority quorums and three fourths quorums.                             *)
(***************************************************************************)
MajQuorums == {Q \in SUBSET P : 2 * Cardinality(Q) > Cardinality(P)}
ThreeFourthQuorums == 
    {Q \in SUBSET P : 4 * Cardinality(Q) > 3 * Cardinality(P)}

(***************************************************************************)
(* The maximum ballot in a set of ballots.                                 *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x # y => y \prec x
    
(***********

--algorithm LeaderlessPaxos {

    variables
        ballot = [p \in P |-> [c \in C |-> <<0,1>>]],
        vote = [p \in P |-> [c \in C |-> <<>>]],
        joinBallot = {},
        propose = <<>>

    define {
        
        (*******************************************************************)
        (* Weak dependencies are to be confirmed at execution time.        *)
        (* Strong dependencies not.  A weak dependency is confirmed when   *)
        (* the target command does not have a strong dependency in the     *)
        (* other direction.  In some sense the target command is helping   *)
        (* the source command to figure out whether the weak dependency is *)
        (* correct or not.  Weak dependencise allow commands not to miss   *)
        (* each other, because a leader always computes the set of weak    *)
        (* dependencies as the union of the dependencies of a quorum.      *)
        (*******************************************************************)
        
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> [strong : SUBSET C, weak : SUBSET C]]
            /\  joinBallot \subseteq (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> [strong : SUBSET C, weak : SUBSET C]]
        
        \* TRUE if c was seen in ballot B.
        SeenAt(c, bal, p) == bal \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == 
            LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
                IF bals # {}
                THEN Max(bals)
                ELSE <<-1,-1>>
        
        \* The estimate for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, b, p) : p \in q}
            IN Max(bals \ {b})
            
        PossibleFastDeps(c, b, q) ==
            {ds \in SUBSET C : \E q2 \in FastQuorum : 
                \A p \in q2 \cap q :
                    /\  <<b,1>> \in DOMAIN vote[p][c]  
                    /\  vote[p][c][<<b,1>>].weak = ds}
            
        Cmd(leader) == leader[1]
        Bal(leader) == leader[2]
        
        Phase1Bals == (0..NumBallots-1) \times {1}
        Phase2Bals == (0..NumBallots-1) \times {2}
        
        Phase1SeenCmds(p) == {c \in C : \E bal \in Phase1Bals : bal \in DOMAIN vote[p][c]}
        Phase2SeenCmds(p, c) == {c2 \in C : \E bal \in Phase2Bals : 
            bal \in DOMAIN vote[p][c2] /\ c \notin vote[p][c2][bal]}
        
        Decided(c, deps) ==
            \/  \E b \in Phase1Bals : \E q \in FastQuorum :
                    \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
            \/  \E b \in Phase2Bals  : \E q \in Quorum :
                    \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
                    
        Decisions == {d \in C \times [strong : SUBSET C, weak : SUBSET C] : Decided(d[1],d[2])}

        (***************************************************************************)
        (* A few simple invariants.                                                *)
        (***************************************************************************)
        Inv1 == \A p \in P : \A c \in C : LastBal(c, Max(Ballot), p) \preceq ballot[p][c]
        
        Inv3 == \A p \in P : \A c \in C :
            LET b == LastBal(c, Max(Ballot), p)
            IN  <<-1,-1>> \prec b => b \in DOMAIN vote[p][c]
            
        Inv2 == \A prop \in Image(propose) : prop.strong \subseteq prop.weak
        
        \* in sub-round 1, the set of weak dependencies is always empty.
        Inv4 == \A x \in DOMAIN propose : x[2][2] = 1 => propose[x].weak = {}        
        
        (*******************************************************************)
        (* The main correctness properties are GraphInvariant and          *)
        (* Agreement.  Their conjunction shoud imply correct State Machine *)
        (* Replication.                                                    *)
        (*******************************************************************)
        
        \* The set of dependency records such that weak dependencies are a subset of strong dependencies.
        Deps == UNION {
            [   strong : {strong}, 
                weak : {strong \cup x : x \in SUBSET (C \ strong)}  ] : 
            strong \in SUBSET C}
        
        (*******************************************************************)
        (* Commands see each other                                         *)
        (*******************************************************************)
        GraphInvariant == \A c1, c2 \in C : \A deps1, deps2 \in Deps :
            /\  Decided(c1, deps1)
            /\  Decided(c2, deps2)
            /\ c1 # c2 
            /\ c2 \notin deps1.strong 
            /\ c1 \notin deps2.strong
            => c2 \in deps1.weak \/ c1 \in deps2.weak
            
        (*******************************************************************)
        (* Main correctness property                                       *)
        (*******************************************************************)
        
        (*******************************************************************)
        (* A given process may now only about a subset of the decisions.   *)
        (* This is the set of all possible local view that processes may   *)
        (* have.                                                           *)
        (*******************************************************************)
        LocalViews == 
            UNION {{view \in [D -> [strong : SUBSET C, weak : SUBSET C]] : 
                    \A c \in D : Decided(c, view[c])} : 
                D \in SUBSET C}
        
        (*******************************************************************)
        (* CanExec(c, view) is true when the full dependency graph of c is *)
        (* given by the view.                                              *)
        (*******************************************************************)
        RECURSIVE CanExecRec(_,_,_)
        CanExec(c, view) == CanExecRec(c, {c}, view)

        CanExecRec(c, seen, view) ==
            /\  c \in DOMAIN view
            /\  LET deps == view[c]
                IN \A c2 \in deps.strong \cup deps.weak : 
                    \/  c2 \in seen
                    \/  CanExecRec(c2, seen \cup {c2}, view)
        
        (*******************************************************************)
        (* A weak dependency is confirmed if it is not contradicted by a   *)
        (* strong dependency in the other direction.                       *)
        (*******************************************************************)
        Confirmed(c, weakDep, view) == c \notin view[weakDep].strong
        
        (*******************************************************************)
        (* The set of final dependencies of a command is the union of the  *)
        (* strong dependencies and the set of confirmed weak dependencies. *)
        (*******************************************************************)
        FinalDeps(c, view) == view[c].strong \cup {w \in view[c].weak : Confirmed(c, w, view)}
        
        (*******************************************************************)
        (* Agreement stipulates that for every command c and view v1 and   *)
        (* v2, if c is executable in both, then its final dependencies are *)
        (* the same.                                                       *)
        (*******************************************************************)
        Agreement == \A v1,v2 \in LocalViews : v1 # v2 =>
            \A c \in DOMAIN v1 \cap DOMAIN v2 : CanExec(c, v1) /\ CanExec(c, v2) =>
                FinalDeps(c, v2) = FinalDeps(c, v2)
            
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
 
    (***********************************************************************)
    (* Phase1 can only be triggered when all values are safe.              *)
    (***********************************************************************)
    macro Phase1(c, b) {
        with (bal = <<b,1>>) {
            propose := propose ++ <<<<c,bal>>, [strong |-> {}, weak |-> {}]>>;
        }
    }
    
    macro Phase1Reply(p) {
        with (c \in C; bal \in Phase1Bals) {
            when <<c, bal>> \in DOMAIN propose /\ ballot[p][c] \preceq bal;
            when LastBal(c, bal, p) \prec bal; \* p has not participated yet in this ballot. 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @ ++ <<bal, 
                [strong |-> propose[<<c, bal>>].strong, 
                 weak |-> (Phase1SeenCmds(p) \cup propose[<<c, bal>>].strong) \ {c}]>> ]];
            \* A response to a phase1Bal means joining phase2:
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = <<bal[1], 2>>]];
        }
    }
    
    macro Phase2(c, b) {
        with (q \in Quorum; bal = <<b,2>>) {
            when \A p \in q : bal \preceq ballot[p][c];
            with (  ps = {p \in q : <<bal[1],1>> \in DOMAIN vote[p][c]} ) {
                when ps = q; \* If there's no q like this then the ballot is over.
                with (  depsUnion = UNION {vote[p][c][<<bal[1],1>>].weak : p \in q};
                        fastDeps = PossibleFastDeps(c, bal[1], q)) {
                    assert Cardinality(fastDeps) <= 1; \* sanity check.
                    if (fastDeps # {}) { \* if c could have been decided fast:
                        with (ds \in fastDeps) {
                            propose := propose ++ <<<<c, bal>>, [strong |-> ds, weak |-> depsUnion (*\ ds*)]>>;
                        }
                    } else { \* no fast decision could have happened:
                        propose := propose ++ <<<<c, bal>>, [strong |-> depsUnion, weak |-> depsUnion]>>;
                    }
                }
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; bal \in Phase2Bals) {
            when <<c, bal>> \in DOMAIN propose /\ ballot[p][c] \preceq bal;
            when LastBal(c, bal, p) \prec bal; \* p has not participated yet in this ballot. 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = 
                @ ++ <<bal, propose[<<c, bal>>]>>]];
            \* Join ballot if not already there.
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = <<bal[1], 2>>]];
        }
    }
    
    macro Recover(c, b) { \* We always re-propose in sub-ballot 1 of major ballot b.
        with (q \in Quorum; bal = <<b,1>>) {
            when \A p \in q : bal \preceq ballot[p][c];
            with (mbal = MaxBal(c, bal, q)) {
                if (mbal[2] = 1) { \* Only phase 1 was started.
                    with (  ps = {p \in q : mbal \in DOMAIN vote[p][c]};
                            fastDeps = PossibleFastDeps(c, mbal[1], q) ) {
                        if (fastDeps # {}) { \* if c could have been decided fast:
                            with ( ds \in fastDeps ) {
                                propose := propose ++ <<<<c,bal>>, [strong |-> ds, weak |-> {}]>>;
                            }
                        } else { \* no fast decision could have happened:
                            \* when FALSE;
                            propose := propose ++ <<<<c,bal>>, [strong |-> {}, weak |-> {}]>>;
                        }
                    }
                } else if (mbal[2] = 2) { \* phase 2 was started.
                    \* when FALSE;
                    with (p \in {p \in P : LastBal(c, <<b-1,2>>, p) = mbal}) { \* <<b-2,2>> is the highest ballot strictly inferior to <<b,1>>.
                        propose := propose ++ <<<<c, <<b,2>>>>, vote[p][c][mbal]>>;
                    }
                } else if (mbal[2] = -1) {
                    \* when FALSE;
                    propose := propose ++ <<<<c,bal>>, [strong |-> {}, weak |-> {}]>>;
                }
            }
        }
    }
        
    macro StartBallot(c, b) {
        assert b > 0; \* Only start ballots greater than 0; 0 is started by default.
        joinBallot := joinBallot \cup {<<c,<<b,1>>>>};
    }
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (jb \in joinBallot; c = jb[1]; bal = jb[2]) {
            when ballot[p][c] \prec bal;
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = bal]];
        }
    }
    
    process (initLeader \in C) {
        propose:    Phase1(self, 0);
        phase2:     Phase2(self, 0);
    }
    
    process (recoveryLeader \in (C \times (1..NumBallots-1))) {
        start:      StartBallot(self[1], self[2]);
        recover:    Recover(self[1], self[2]);
        phase2:     Phase2(self[1], self[2]);
    }
    
    \* Acceptors:
    process (acc \in P) {
        acc:    while (TRUE) {
                    either {
                        Phase1Reply(self);
                    } or {
                        Phase2Reply(self);
                    } or {
                        JoinBallot(self);
                    }
                }
    }
    (***********************************************************************)
    (* Model-cheked with 5 accs, 2 commands, 1 recovery, 2 fast quorums, 3 *)
    (* classic quorums, and symmetry sets (43M states, depth 39, 11 hours  *)
    (* on whitewhale).                                                     *)
    (***********************************************************************)
}

*)
\* BEGIN TRANSLATION
\* Label propose of process initLeader at line 216 col 14 changed to propose_
\* Label phase2 of process initLeader at line 234 col 14 changed to phase2_
\* Label acc of process acc at line 318 col 17 changed to acc_
VARIABLES ballot, vote, joinBallot, propose, pc

(* define statement *)
TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> [strong : SUBSET C, weak : SUBSET C]]
    /\  joinBallot \subseteq (C \times Ballot)
    /\  \E D \in SUBSET (C \times Ballot) : propose \in [D -> [strong : SUBSET C, weak : SUBSET C]]


SeenAt(c, bal, p) == bal \in DOMAIN vote[p][c]


LastBal(c, max, p) ==
    LET bals == {b \in DOMAIN vote[p][c] : b \preceq max} IN
        IF bals # {}
        THEN Max(bals)
        ELSE <<-1,-1>>


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b, p) : p \in q}
    IN Max(bals \ {b})

PossibleFastDeps(c, b, q) ==
    {ds \in SUBSET C : \E q2 \in FastQuorum :
        \A p \in q2 \cap q :
            /\  <<b,1>> \in DOMAIN vote[p][c]
            /\  vote[p][c][<<b,1>>].weak = ds}

Cmd(leader) == leader[1]
Bal(leader) == leader[2]

Phase1Bals == (0..NumBallots-1) \times {1}
Phase2Bals == (0..NumBallots-1) \times {2}

Phase1SeenCmds(p) == {c \in C : \E bal \in Phase1Bals : bal \in DOMAIN vote[p][c]}
Phase2SeenCmds(p, c) == {c2 \in C : \E bal \in Phase2Bals :
    bal \in DOMAIN vote[p][c2] /\ c \notin vote[p][c2][bal]}

Decided(c, deps) ==
    \/  \E b \in Phase1Bals : \E q \in FastQuorum :
            \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps
    \/  \E b \in Phase2Bals  : \E q \in Quorum :
            \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b] = deps

Decisions == {d \in C \times [strong : SUBSET C, weak : SUBSET C] : Decided(d[1],d[2])}




Inv1 == \A p \in P : \A c \in C : LastBal(c, Max(Ballot), p) \preceq ballot[p][c]

Inv3 == \A p \in P : \A c \in C :
    LET b == LastBal(c, Max(Ballot), p)
    IN  <<-1,-1>> \prec b => b \in DOMAIN vote[p][c]

Inv2 == \A prop \in Image(propose) : prop.strong \subseteq prop.weak


Inv4 == \A x \in DOMAIN propose : x[2][2] = 1 => propose[x].weak = {}








Deps == UNION {
    [   strong : {strong},
        weak : {strong \cup x : x \in SUBSET (C \ strong)}  ] :
    strong \in SUBSET C}




GraphInvariant == \A c1, c2 \in C : \A deps1, deps2 \in Deps :
    /\  Decided(c1, deps1)
    /\  Decided(c2, deps2)
    /\ c1 # c2
    /\ c2 \notin deps1.strong
    /\ c1 \notin deps2.strong
    => c2 \in deps1.weak \/ c1 \in deps2.weak










LocalViews ==
    UNION {{view \in [D -> [strong : SUBSET C, weak : SUBSET C]] :
            \A c \in D : Decided(c, view[c])} :
        D \in SUBSET C}





RECURSIVE CanExecRec(_,_,_)
CanExec(c, view) == CanExecRec(c, {c}, view)

CanExecRec(c, seen, view) ==
    /\  c \in DOMAIN view
    /\  LET deps == view[c]
        IN \A c2 \in deps.strong \cup deps.weak :
            \/  c2 \in seen
            \/  CanExecRec(c2, seen \cup {c2}, view)





Confirmed(c, weakDep, view) == c \notin view[weakDep].strong





FinalDeps(c, view) == view[c].strong \cup {w \in view[c].weak : Confirmed(c, w, view)}






Agreement == \A v1,v2 \in LocalViews : v1 # v2 =>
    \A c \in DOMAIN v1 \cap DOMAIN v2 : CanExec(c, v1) /\ CanExec(c, v2) =>
        FinalDeps(c, v2) = FinalDeps(c, v2)


vars == << ballot, vote, joinBallot, propose, pc >>

ProcSet == (C) \cup ((C \times (1..NumBallots-1))) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> <<0,1>>]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ joinBallot = {}
        /\ propose = <<>>
        /\ pc = [self \in ProcSet |-> CASE self \in C -> "propose_"
                                        [] self \in (C \times (1..NumBallots-1)) -> "start"
                                        [] self \in P -> "acc_"]

propose_(self) == /\ pc[self] = "propose_"
                  /\ LET bal == <<0,1>> IN
                       propose' = propose ++ <<<<self,bal>>, [strong |-> {}, weak |-> {}]>>
                  /\ pc' = [pc EXCEPT ![self] = "phase2_"]
                  /\ UNCHANGED << ballot, vote, joinBallot >>

phase2_(self) == /\ pc[self] = "phase2_"
                 /\ \E q \in Quorum:
                      LET bal == <<0,2>> IN
                        /\ \A p \in q : bal \preceq ballot[p][self]
                        /\ LET ps == {p \in q : <<bal[1],1>> \in DOMAIN vote[p][self]} IN
                             /\ ps = q
                             /\ LET depsUnion == UNION {vote[p][self][<<bal[1],1>>].weak : p \in q} IN
                                  LET fastDeps == PossibleFastDeps(self, bal[1], q) IN
                                    /\ Assert(Cardinality(fastDeps) <= 1, 
                                              "Failure of assertion at line 240, column 21 of macro called at line 307, column 21.")
                                    /\ IF fastDeps # {}
                                          THEN /\ \E ds \in fastDeps:
                                                    propose' = propose ++ <<<<self, bal>>, [strong |-> ds, weak |-> depsUnion         ]>>
                                          ELSE /\ propose' = propose ++ <<<<self, bal>>, [strong |-> depsUnion, weak |-> depsUnion]>>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, joinBallot >>

initLeader(self) == propose_(self) \/ phase2_(self)

start(self) == /\ pc[self] = "start"
               /\ Assert((self[2]) > 0, 
                         "Failure of assertion at line 294, column 9 of macro called at line 311, column 21.")
               /\ joinBallot' = (joinBallot \cup {<<(self[1]),<<(self[2]),1>>>>})
               /\ pc' = [pc EXCEPT ![self] = "recover"]
               /\ UNCHANGED << ballot, vote, propose >>

recover(self) == /\ pc[self] = "recover"
                 /\ \E q \in Quorum:
                      LET bal == <<(self[2]),1>> IN
                        /\ \A p \in q : bal \preceq ballot[p][(self[1])]
                        /\ LET mbal == MaxBal((self[1]), bal, q) IN
                             IF mbal[2] = 1
                                THEN /\ LET ps == {p \in q : mbal \in DOMAIN vote[p][(self[1])]} IN
                                          LET fastDeps == PossibleFastDeps((self[1]), mbal[1], q) IN
                                            IF fastDeps # {}
                                               THEN /\ \E ds \in fastDeps:
                                                         propose' = propose ++ <<<<(self[1]),bal>>, [strong |-> ds, weak |-> {}]>>
                                               ELSE /\ propose' = propose ++ <<<<(self[1]),bal>>, [strong |-> {}, weak |-> {}]>>
                                ELSE /\ IF mbal[2] = 2
                                           THEN /\ \E p \in {p \in P : LastBal((self[1]), <<(self[2])-1,2>>, p) = mbal}:
                                                     propose' = propose ++ <<<<(self[1]), <<(self[2]),2>>>>, vote[p][(self[1])][mbal]>>
                                           ELSE /\ IF mbal[2] = -1
                                                      THEN /\ propose' = propose ++ <<<<(self[1]),bal>>, [strong |-> {}, weak |-> {}]>>
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED propose
                 /\ pc' = [pc EXCEPT ![self] = "phase2"]
                 /\ UNCHANGED << ballot, vote, joinBallot >>

phase2(self) == /\ pc[self] = "phase2"
                /\ \E q \in Quorum:
                     LET bal == <<(self[2]),2>> IN
                       /\ \A p \in q : bal \preceq ballot[p][(self[1])]
                       /\ LET ps == {p \in q : <<bal[1],1>> \in DOMAIN vote[p][(self[1])]} IN
                            /\ ps = q
                            /\ LET depsUnion == UNION {vote[p][(self[1])][<<bal[1],1>>].weak : p \in q} IN
                                 LET fastDeps == PossibleFastDeps((self[1]), bal[1], q) IN
                                   /\ Assert(Cardinality(fastDeps) <= 1, 
                                             "Failure of assertion at line 240, column 21 of macro called at line 313, column 21.")
                                   /\ IF fastDeps # {}
                                         THEN /\ \E ds \in fastDeps:
                                                   propose' = propose ++ <<<<(self[1]), bal>>, [strong |-> ds, weak |-> depsUnion         ]>>
                                         ELSE /\ propose' = propose ++ <<<<(self[1]), bal>>, [strong |-> depsUnion, weak |-> depsUnion]>>
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << ballot, vote, joinBallot >>

recoveryLeader(self) == start(self) \/ recover(self) \/ phase2(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E bal \in Phase1Bals:
                           /\ <<c, bal>> \in DOMAIN propose /\ ballot[self][c] \preceq bal
                           /\ LastBal(c, bal, self) \prec bal
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @ ++ <<bal,
                                      [strong |-> propose[<<c, bal>>].strong,
                                       weak |-> (Phase1SeenCmds(self) \cup propose[<<c, bal>>].strong) \ {c}]>> ]]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = <<bal[1], 2>>]]
                 \/ /\ \E c \in C:
                         \E bal \in Phase2Bals:
                           /\ <<c, bal>> \in DOMAIN propose /\ ballot[self][c] \preceq bal
                           /\ LastBal(c, bal, self) \prec bal
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] =
                                      @ ++ <<bal, propose[<<c, bal>>]>>]]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = <<bal[1], 2>>]]
                 \/ /\ \E jb \in joinBallot:
                         LET c == jb[1] IN
                           LET bal == jb[2] IN
                             /\ ballot[self][c] \prec bal
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = bal]]
                    /\ vote' = vote
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << joinBallot, propose >>

acc(self) == acc_(self)

Next == (\E self \in C: initLeader(self))
           \/ (\E self \in (C \times (1..NumBallots-1)): recoveryLeader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat Apr 16 17:02:35 EDT 2016 by nano
\* Created Sat Apr 16 17:01:27 EDT 2016 by nano
