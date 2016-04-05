---------------------------- MODULE EPaxosLight ----------------------------

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
(* P is the set of acceptors.  MaxTime bounds the timestamp that can be    *)
(* assigned to proposals, but not to retries.  CmdId(c) must assign a      *)
(* natural number to a command.  It is used to break time in timestamps.   *)
(***************************************************************************)
CONSTANTS P, Quorum, FastQuorum, NumBallots, C, CmdId(_)

ASSUME \A c \in C : 
    /\  CmdId(c) \in Nat 
    /\  \A c2 \in C : c # c2 => CmdId(c) # CmdId(c2)

ASSUME NumBallots \in Nat /\ NumBallots >= 1

Ballot == 0..(NumBallots-1)

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
(* The maximum element in a set.                                           *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : x >= y
    
(***********

--algorithm EPaxosLight {

    variables
        ballot = [p \in P |-> [c \in C |-> 0]],
        vote = [p \in P |-> [c \in C |-> <<>>]],
        phase1 = {},
        phase2 = <<>>,
        committed = <<>>,
        joinBallot = {}

    define {
        
        Status == {"pending1", "accepted"}
        CmdInfo == [status : Status, deps : SUBSET C]
        
        (*******************************************************************)
        (* An invariant describing the type of the different variables.    *)
        (* Note that we extensively use maps (also called functions) keyed *)
        (* by pairs <c,b>, where c is a command and b a ballot, and where  *)
        (* the set of keys of the map dynamically grows.  The set of keys  *)
        (* of a map m is noted DOMAIN m.                                   *)
        (*******************************************************************)
        TypeInvariant ==
            /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
            /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> CmdInfo]
            /\  phase1 \in SUBSET (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : phase2 \in [D -> SUBSET C]
            /\  joinBallot \subseteq (C \times Ballot)
            /\  \E D \in SUBSET (C \times Ballot) : committed \in [D -> SUBSET C]
    
        \* All the commands ever seen by p in any ballot.
        SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}
        
        \* TRUE if c was seen in ballot b at p.
        SeenAt(c, b, p) == b \in DOMAIN vote[p][c]
        
        \* The highest c-ballot in which p participated.
        LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b <= max} IN
            IF bals # {}
            THEN Max(bals)
            ELSE -1
        
        \* The estimate for c on p in the highest c-ballot in which p participated. 
        MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]
        
        \* Given a quorum q, the maximum ballot strictly less than b in which an acceptor in q has participated.
        MaxBal(c, b, q) == 
            LET bals == {LastBal(c, b-1, p) : p \in q}
            IN Max(bals)
        
        ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]
            
        (***************************************************************************)
        (* A few simple invariants.                                                *)
        (***************************************************************************)
        Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)
        
        Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in phase1 => <<c,b>> \in joinBallot
        
        Inv3 == \A p \in P : \A c \in C : 
            LET b == LastBal(c, Max(Ballot), p)
            IN  b >= 0 => b \in DOMAIN vote[p][c]
        
        (*******************************************************************)
        (* The main correctness properties are GraphInvariant and          *)
        (* Agreement.  Their conjunction shoud imply correct State Machine *)
        (* Replication.                                                    *)
        (*******************************************************************)
                
        GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
            /\ <<c1,b1>> \in DOMAIN committed 
            /\ <<c2,b2>> \in DOMAIN committed
            /\ c1 # c2 
            =>  \/  c2 \in committed[<<c1,b1>>]
                \/  c1 \in committed[<<c2,b2>>]
        
        Agreement == \A c \in C : \A b1,b2 \in Ballot : 
            /\ <<c,b1>> \in DOMAIN committed
            /\ <<c,b2>> \in DOMAIN committed 
            => committed[<<c,b1>>] = committed[<<c,b2>>]

        Cmd(leader) == leader[1]
        Bal(leader) == leader[2]
        
    }
    
    (***********************************************************************)
    (* Finally, the algorithm:                                             *)
    (***********************************************************************)
 
    macro Phase1(c, b) {
        when <<c,b>> \notin phase1;
        phase1 := phase1 \cup {<<c,b>>}
    }
    
    macro Phase1Reply(p) {
        with (c \in C; b \in Ballot) { 
            when <<c, b>> \in phase1;
            when b >= ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]]; \* Join the ballot if lagging.
            when LastBal(c, b, p) < b; \* p has not participated yet in this ballot.
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                ++ <<b, [status |-> "pending1", deps |-> SeenCmds(p)]>>]];
            
        }
    }
    
    macro FastDecision(c, b) {
        with (q \in FastQuorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1";
            with (ds \in {ds \in SUBSET C : \A p \in q : vote[p][c][b].deps = ds}) {
                committed := committed ++ <<<<c,b>>, ds>>;
            }
        }
    }
    
    macro Phase2(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1";
            with (ds = UNION {vote[p][c][b].deps : p \in q}) {
                phase2 := phase2 ++ <<<<c,b>>, ds>>;
            }
        }
    }
    
    macro Phase2Reply(p) {
        with (c \in C; b \in Ballot) { 
            when <<c, b>> \in DOMAIN phase2;
            when b >= ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]]; \* Join the ballot if lagging.
            when b \notin DOMAIN vote[p][c] \/ (b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "pending1"); 
            vote := [vote EXCEPT ![p] = [@ EXCEPT ![c] = @
                ++ <<b, [status |-> "accepted", deps |-> phase2[<<c,b>>] ]>>]];
            
        }
    }
    macro SlowDecision(c, b) {
        with (q \in Quorum) {
            when \A p \in q : b \in DOMAIN vote[p][c] /\ vote[p][c][b].status = "accepted";
            with (ds \in {ds \in SUBSET C : \A p \in q : vote[p][c][b].deps = ds}) {
                committed := committed ++ <<<<c,b>>, ds>>;
            }
        }
    }
    
    macro StartBallot(c, b) {
        assert b > 0; \* Only start ballots greater than 0; 0 is started by default.
        joinBallot := joinBallot \cup {<<c,b>>};
    }
    
    macro JoinBallot(p) { \* Note that every process is in the first ballot by default.
        with (ball \in joinBallot; c = ball[1], b = ball[2]) {
            when b > ballot[p][c];
            ballot := [ballot EXCEPT ![p] = [@ EXCEPT ![c] = b]];
        }
    }
    
    macro Recover(c, b) {
        when <<c,b>> \in joinBallot;
        with (q \in Quorum) {
            when \A p \in q : ballot[p][c] >= b;
            with (mb = MaxBal(c, b, q); ps = {p \in q : mb \in DOMAIN vote[p][c]}) {
                when ps # {}; \* TODO: we exclude the case in which we should do phase 1.
                phase2 := phase2 ++ <<<<c,b>>, UNION {vote[p][c][mb].deps : p \in ps}>>;
            }   
        }
    }
    
    \* Workflow of a decision:
    procedure Decide(com, bal) {
        decide:     either  {
        decideFast:     FastDecision(com, bal);
                    } or {
        retry:          Phase2(com, bal);
        decideSlow:     SlowDecision(com, bal);
                        return; }
    }
    
    \* The work flow of a leader:
    process (leader \in (C \times Ballot)) {
        leader:         either {
        bal0:               when self[2] = 0;
        bal0phase1:         Phase1(self[1], self[2]);
                            either  {
        decideFast:             FastDecision(self[1], self[2]);
                            } or {
        bal0retry:              Phase2(self[1], self[2]);
        bal0decideSlow:         SlowDecision(self[1], self[2]);
                            }
                        } or {
                            when self[2] > 0;
        startBal:           StartBallot(self[1], self[2]);
        recover:            Recover(self[1], self[2]);
        decided:            SlowDecision(self[1], self[2]);
                        }
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
    
}

*)
\* BEGIN TRANSLATION
\* Label decideFast of procedure Decide at line 156 col 14 changed to decideFast_
\* Label leader of process leader at line 228 col 25 changed to leader_
\* Label acc of process acc at line 247 col 17 changed to acc_
CONSTANT defaultInitValue
VARIABLES ballot, vote, phase1, phase2, committed, joinBallot, pc, stack

(* define statement *)
Status == {"pending1", "accepted"}
CmdInfo == [status : Status, deps : SUBSET C]








TypeInvariant ==
    /\  \A p \in P, c \in C : ballot[p][c] \in Ballot
    /\  \A p \in P, c \in C : \E D \in SUBSET Ballot : vote[p][c] \in [D -> CmdInfo]
    /\  phase1 \in SUBSET (C \times Ballot)
    /\  \E D \in SUBSET (C \times Ballot) : phase2 \in [D -> SUBSET C]
    /\  joinBallot \subseteq (C \times Ballot)
    /\  \E D \in SUBSET (C \times Ballot) : committed \in [D -> SUBSET C]


SeenCmds(p) == {c \in C : DOMAIN vote[p][c] # {}}


SeenAt(c, b, p) == b \in DOMAIN vote[p][c]


LastBal(c, max, p) == LET bals == {b \in DOMAIN vote[p][c] : b <= max} IN
    IF bals # {}
    THEN Max(bals)
    ELSE -1


MaxVote(c, p) == vote[p][c][LastBal(c, Max(Ballot), p)]


MaxBal(c, b, q) ==
    LET bals == {LastBal(c, b-1, p) : p \in q}
    IN Max(bals)

ParticipatedIn(b, c, p) == b \in DOMAIN vote[p][c]




Inv1 == \A p \in P : \A c \in C : ballot[p][c] >= LastBal(c, Max(Ballot), p)

Inv2 == \A c \in C, b \in Ballot \ {0} : <<c,b>> \in phase1 => <<c,b>> \in joinBallot

Inv3 == \A p \in P : \A c \in C :
    LET b == LastBal(c, Max(Ballot), p)
    IN  b >= 0 => b \in DOMAIN vote[p][c]







GraphInvariant == \A c1, c2 \in C : \A b1, b2 \in Ballot :
    /\ <<c1,b1>> \in DOMAIN committed
    /\ <<c2,b2>> \in DOMAIN committed
    /\ c1 # c2
    =>  \/  c2 \in committed[<<c1,b1>>]
        \/  c1 \in committed[<<c2,b2>>]

Agreement == \A c \in C : \A b1,b2 \in Ballot :
    /\ <<c,b1>> \in DOMAIN committed
    /\ <<c,b2>> \in DOMAIN committed
    => committed[<<c,b1>>] = committed[<<c,b2>>]

Cmd(leader) == leader[1]
Bal(leader) == leader[2]

VARIABLES com, bal

vars == << ballot, vote, phase1, phase2, committed, joinBallot, pc, stack, 
           com, bal >>

ProcSet == ((C \times Ballot)) \cup (P)

Init == (* Global variables *)
        /\ ballot = [p \in P |-> [c \in C |-> 0]]
        /\ vote = [p \in P |-> [c \in C |-> <<>>]]
        /\ phase1 = {}
        /\ phase2 = <<>>
        /\ committed = <<>>
        /\ joinBallot = {}
        (* Procedure Decide *)
        /\ com = [ self \in ProcSet |-> defaultInitValue]
        /\ bal = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in (C \times Ballot) -> "leader_"
                                        [] self \in P -> "acc_"]

decide(self) == /\ pc[self] = "decide"
                /\ \/ /\ pc' = [pc EXCEPT ![self] = "decideFast_"]
                   \/ /\ pc' = [pc EXCEPT ![self] = "retry"]
                /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                                joinBallot, stack, com, bal >>

decideFast_(self) == /\ pc[self] = "decideFast_"
                     /\ \E q \in FastQuorum:
                          /\ \A p \in q : bal[self] \in DOMAIN vote[p][com[self]] /\ vote[p][com[self]][bal[self]].status = "pending1"
                          /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][com[self]][bal[self]].deps = ds}:
                               committed' = committed ++ <<<<com[self],bal[self]>>, ds>>
                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                     /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot, 
                                     stack, com, bal >>

retry(self) == /\ pc[self] = "retry"
               /\ \E q \in Quorum:
                    /\ \A p \in q : bal[self] \in DOMAIN vote[p][com[self]] /\ vote[p][com[self]][bal[self]].status = "pending1"
                    /\ LET ds == UNION {vote[p][com[self]][bal[self]].deps : p \in q} IN
                         phase2' = phase2 ++ <<<<com[self],bal[self]>>, ds>>
               /\ pc' = [pc EXCEPT ![self] = "decideSlow"]
               /\ UNCHANGED << ballot, vote, phase1, committed, joinBallot, 
                               stack, com, bal >>

decideSlow(self) == /\ pc[self] = "decideSlow"
                    /\ \E q \in Quorum:
                         /\ \A p \in q : bal[self] \in DOMAIN vote[p][com[self]] /\ vote[p][com[self]][bal[self]].status = "accepted"
                         /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][com[self]][bal[self]].deps = ds}:
                              committed' = committed ++ <<<<com[self],bal[self]>>, ds>>
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ com' = [com EXCEPT ![self] = Head(stack[self]).com]
                    /\ bal' = [bal EXCEPT ![self] = Head(stack[self]).bal]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot >>

Decide(self) == decide(self) \/ decideFast_(self) \/ retry(self)
                   \/ decideSlow(self)

leader_(self) == /\ pc[self] = "leader_"
                 /\ \/ /\ pc' = [pc EXCEPT ![self] = "bal0"]
                    \/ /\ self[2] > 0
                       /\ pc' = [pc EXCEPT ![self] = "startBal"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                                 joinBallot, stack, com, bal >>

bal0(self) == /\ pc[self] = "bal0"
              /\ self[2] = 0
              /\ pc' = [pc EXCEPT ![self] = "bal0phase1"]
              /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                              joinBallot, stack, com, bal >>

bal0phase1(self) == /\ pc[self] = "bal0phase1"
                    /\ <<(self[1]),(self[2])>> \notin phase1
                    /\ phase1' = (phase1 \cup {<<(self[1]),(self[2])>>})
                    /\ \/ /\ pc' = [pc EXCEPT ![self] = "decideFast"]
                       \/ /\ pc' = [pc EXCEPT ![self] = "bal0retry"]
                    /\ UNCHANGED << ballot, vote, phase2, committed, 
                                    joinBallot, stack, com, bal >>

decideFast(self) == /\ pc[self] = "decideFast"
                    /\ \E q \in FastQuorum:
                         /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "pending1"
                         /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                              committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot, 
                                    stack, com, bal >>

bal0retry(self) == /\ pc[self] = "bal0retry"
                   /\ \E q \in Quorum:
                        /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "pending1"
                        /\ LET ds == UNION {vote[p][(self[1])][(self[2])].deps : p \in q} IN
                             phase2' = phase2 ++ <<<<(self[1]),(self[2])>>, ds>>
                   /\ pc' = [pc EXCEPT ![self] = "bal0decideSlow"]
                   /\ UNCHANGED << ballot, vote, phase1, committed, joinBallot, 
                                   stack, com, bal >>

bal0decideSlow(self) == /\ pc[self] = "bal0decideSlow"
                        /\ \E q \in Quorum:
                             /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "accepted"
                             /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                                  committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << ballot, vote, phase1, phase2, 
                                        joinBallot, stack, com, bal >>

startBal(self) == /\ pc[self] = "startBal"
                  /\ Assert((self[2]) > 0, 
                            "Failure of assertion at line 194, column 9 of macro called at line 239, column 29.")
                  /\ joinBallot' = (joinBallot \cup {<<(self[1]),(self[2])>>})
                  /\ pc' = [pc EXCEPT ![self] = "recover"]
                  /\ UNCHANGED << ballot, vote, phase1, phase2, committed, 
                                  stack, com, bal >>

recover(self) == /\ pc[self] = "recover"
                 /\ <<(self[1]),(self[2])>> \in joinBallot
                 /\ \E q \in Quorum:
                      /\ \A p \in q : ballot[p][(self[1])] >= (self[2])
                      /\ LET mb == MaxBal((self[1]), (self[2]), q) IN
                           LET ps == {p \in q : mb \in DOMAIN vote[p][(self[1])]} IN
                             /\ ps # {}
                             /\ phase2' = phase2 ++ <<<<(self[1]),(self[2])>>, UNION {vote[p][(self[1])][mb].deps : p \in ps}>>
                 /\ pc' = [pc EXCEPT ![self] = "decided"]
                 /\ UNCHANGED << ballot, vote, phase1, committed, joinBallot, 
                                 stack, com, bal >>

decided(self) == /\ pc[self] = "decided"
                 /\ \E q \in Quorum:
                      /\ \A p \in q : (self[2]) \in DOMAIN vote[p][(self[1])] /\ vote[p][(self[1])][(self[2])].status = "accepted"
                      /\ \E ds \in {ds \in SUBSET C : \A p \in q : vote[p][(self[1])][(self[2])].deps = ds}:
                           committed' = committed ++ <<<<(self[1]),(self[2])>>, ds>>
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ UNCHANGED << ballot, vote, phase1, phase2, joinBallot, 
                                 stack, com, bal >>

leader(self) == leader_(self) \/ bal0(self) \/ bal0phase1(self)
                   \/ decideFast(self) \/ bal0retry(self)
                   \/ bal0decideSlow(self) \/ startBal(self)
                   \/ recover(self) \/ decided(self)

acc_(self) == /\ pc[self] = "acc_"
              /\ \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ <<c, b>> \in phase1
                           /\ b >= ballot[self][c]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ LastBal(c, b, self) < b
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                      ++ <<b, [status |-> "pending1", deps |-> SeenCmds(self)]>>]]
                 \/ /\ \E c \in C:
                         \E b \in Ballot:
                           /\ <<c, b>> \in DOMAIN phase2
                           /\ b >= ballot[self][c]
                           /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                           /\ b \notin DOMAIN vote[self][c] \/ (b \in DOMAIN vote[self][c] /\ vote[self][c][b].status = "pending1")
                           /\ vote' =     [vote EXCEPT ![self] = [@ EXCEPT ![c] = @
                                      ++ <<b, [status |-> "accepted", deps |-> phase2[<<c,b>>] ]>>]]
                 \/ /\ \E ball \in joinBallot:
                         LET c == ball[1] IN
                           LET b == ball[2] IN
                             /\ b > ballot[self][c]
                             /\ ballot' = [ballot EXCEPT ![self] = [@ EXCEPT ![c] = b]]
                    /\ vote' = vote
              /\ pc' = [pc EXCEPT ![self] = "acc_"]
              /\ UNCHANGED << phase1, phase2, committed, joinBallot, stack, 
                              com, bal >>

acc(self) == acc_(self)

Next == (\E self \in ProcSet: Decide(self))
           \/ (\E self \in (C \times Ballot): leader(self))
           \/ (\E self \in P: acc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Tue Apr 05 14:35:54 EDT 2016 by nano
\* Created Tue Apr 05 09:07:07 EDT 2016 by nano
