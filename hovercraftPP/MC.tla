---- MODULE MC ----
EXTENDS hovercraft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4, r5
----

\* MV CONSTANT definitions Value
const_1749331507207271000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_1749331507207272000 == 
{r1, r2, r3, r4, r5}
----

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1749331507207273000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_1749331507207274000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_1749331507207275000 == 
5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1749331507207276000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Sat Jun 07 23:25:07 CEST 2025 by Ludovic
