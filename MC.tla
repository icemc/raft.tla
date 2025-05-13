---- MODULE MC ----
EXTENDS hovercraft, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4
----

\* MV CONSTANT definitions Value
const_174707136905241000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_174707136905242000 == 
{r1, r2, r3, r4}
----

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_174707136905243000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:6MaxBecomeLeader
const_174707136905244000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:12MaxClientRequests
const_174707136905245000 == 
5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_174707136905246000 ==
MyConstraint
----
=============================================================================
\* Modification History
\* Created Mon May 12 19:36:09 CEST 2025 by Ludovic
