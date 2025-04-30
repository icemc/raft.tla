--------------------------- MODULE raftModelPerf ---------------------------

EXTENDS raftSpec

\*instrumentation and performance invariants

\* A leader's maxc should remain under MaxClientRequests
MaxCInv == (\E i \in Server : state[i] = Leader) => maxc <= MaxClientRequests

\* No server can become leader more than MaxBecomeLeader times
LeaderCountInv == \E i \in Server : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

\* No server can have a term exceeding MaxTerm
MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

\* Check lower bound for message counts on committed entries ----
\* For any entry that has been marked as committed, verify that either the number
\* of AppendEntries requests sent OR the number of successful acknowledgments received
\* is at least the minimum number of followers required to form a majority.
\* will fail when an entry was sent twice to a follower and no response was acked yet, which is normal
EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Server) - 1
        MinFollowersForMajority == Cardinality(Server) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

\* Check that committed entries received acknowledgments from a majority of followers.
EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Server)
        \* Minimum number of *followers* needed (in addition to the leader)
        \* to reach a majority for committing an entry.
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in Server : commitIndex[i] /= 1 \*
    
FollowersAppendEntry == \E i,j \in Server : i /= j /\ state[i] = Follower /\ state[j] = Follower /\ Len(log[i]) = 1 /\ Len(log[j]) = 1 \* Verifies that at least one follower appends an entry

MessageSent == messages = <<>>

\*Modify LeaderCommited == \E i \in Server : commitIndex[i] /= 1
\*and run with MySpec OR

\*Use the following modified Init with MyNext for finding an error trace with LeaderCommited == \E i \in Server : commitIndex[i] /= 2 violated
(*

/\  commitIndex = [r1 |-> 1, r2 |-> 1, r3 |-> 1]
/\  currentTerm = [r1 |-> 2, r2 |-> 2, r3 |-> 2]
/\  entryCommitStats = ( <<1, 2>> :> [committed |-> TRUE, sentCount |-> 1, ackCount |-> 1] @@
  <<2, 2>> :> [committed |-> FALSE, sentCount |-> 1, ackCount |-> 0] )
/\  leaderCount = [r1 |-> 1, r2 |-> 0, r3 |-> 0]
/\  log = [ r1 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r2 |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
  r3 |-> <<[term |-> 2, value |-> "v1"]>> ]
/\  matchIndex = [ r1 |-> [r1 |-> 0, r2 |-> 1, r3 |-> 0],
  r2 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0],
  r3 |-> [r1 |-> 0, r2 |-> 0, r3 |-> 0] ]
/\  maxc = 2
/\  messages = ( [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r1",
    msource |-> "r2",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 2 ] :>
      1 @@
  [ mdest |-> "r1",
    msource |-> "r3",
    mtype |-> AppendEntriesResponse,
    mterm |-> 2,
    msuccess |-> TRUE,
    mmatchIndex |-> 1 ] :>
      1 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 0 ] :>
      0 @@
  [ mdest |-> "r2",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 1,
    mprevLogTerm |-> 2,
    mentries |-> <<[term |-> 2, value |-> "v2"]>>,
    mcommitIndex |-> 1 ] :>
      0 @@
  [ mdest |-> "r3",
    msource |-> "r1",
    mtype |-> AppendEntriesRequest,
    mterm |-> 2,
    mlog |-> <<[term |-> 2, value |-> "v1"], [term |-> 2, value |-> "v2"]>>,
    mprevLogIndex |-> 0,
    mprevLogTerm |-> 0,
    mentries |-> <<[term |-> 2, value |-> "v1"]>>,
    mcommitIndex |-> 1 ] :>
      0 )
/\  nextIndex = [ r1 |-> [r1 |-> 1, r2 |-> 2, r3 |-> 1],
  r2 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1],
  r3 |-> [r1 |-> 1, r2 |-> 1, r3 |-> 1] ]
/\  state = [r1 |-> Leader, r2 |-> Follower, r3 |-> Follower]
/\  votedFor = [r1 |-> Nil, r2 |-> "r1", r3 |-> "r1"]
/\  voterLog = [r1 |-> [r1 |-> <<>>], r2 |-> <<>>, r3 |-> <<>>]
/\  votesGranted = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]
/\  votesResponded = [r1 |-> {"r1"}, r2 |-> {}, r3 |-> {}]

*)

=============================================================================
\* Created by Ovidiu-Cristian Marcu
