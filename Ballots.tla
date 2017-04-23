------------------------------ MODULE Ballots ------------------------------

EXTENDS FiniteSets, Naturals, Integers

CONSTANT NumBallots, SubBallots

(***************************************************************************)
(* Ballots are of the form <<b,i>>, where b is the main ballot number and  *)
(* i the sub-ballot number.  Ballots are totally ordered:                  *)
(***************************************************************************)
MajorBallot == 0..(NumBallots-1)
Ballot == MajorBallot \times SubBallots

ASSUME NumBallots \in Nat /\ NumBallots >= 1

bal1 \prec bal2 == 
    IF bal1[1] = bal2[1]
    THEN bal1[2] < bal2[2]
    ELSE bal1[1] < bal2[1]

bal1 \preceq bal2 ==
    bal1 \prec bal2 \/ bal1 = bal2
    
(***************************************************************************)
(* The maximum element in a set of ballots.                                *)
(***************************************************************************)
Max(xs) == CHOOSE x \in xs : \A y \in xs : y \preceq x

(***************************************************************************)
(* Bot is not a ballot, but Bot \prec b holds for any ballot b.            *)
(***************************************************************************)
Bot == <<-1, 3>> 

(***************************************************************************)
(* The predecessor of a ballot.  Note that Pred(<<0,1>>) = Bot.            *)
(***************************************************************************)
Pred(b) == CASE 
    b[2] = 1 -> <<b[1]-1,3>>
[]  b[2] = 2 -> <<b[1],1>>
[]  b[2] = 3 -> <<b[1],2>>

Maj(b) == b[1]
Phase(b) == b[2]

=============================================================================
\* Modification History
\* Last modified Tue May 03 08:54:58 EDT 2016 by nano
\* Created Mon May 02 21:17:10 EDT 2016 by nano
