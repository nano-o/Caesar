------------------------------ MODULE Quorums ------------------------------

EXTENDS FiniteSets, Naturals, Integers

CONSTANT Quorum, FastQuorum, P

ASSUME \A Q \in Quorum : Q \subseteq P
ASSUME \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME \A Q1,Q2 \in FastQuorum : \A Q3 \in Quorum : Q1 \cap Q2 \cap Q3 # {}

=============================================================================
\* Modification History
\* Last modified Mon May 02 21:17:13 EDT 2016 by nano
\* Created Mon May 02 21:03:00 EDT 2016 by nano
