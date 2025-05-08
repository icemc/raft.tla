------------------------------ MODULE raftSpec ------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\* Modified by Ovidiu Marcu. Simplified model and performance invariants added.
\* Modified further to track message counts for entry commitment.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS raftActionsSolution

\* Receive a message.
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)
       \/ /\ m.mtype = NewSwitchRequest
          /\ HandleNewSwitchRequest(i, j, m)
       \/ /\ m.mtype = RecoveryRequest
          /\ HandleRecoveryRequest(i, j, m)

\* Defines how the variables may transition.
Next == 
           \/ \E i \in Server : Timeout(i)
\*           \/ \E i \in Server : Restart(i)
           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
           \/ \E i \in Server : BecomeLeader(i)
           \/ \E i \in Server, v \in Value : state[i] = Leader /\ SwitchClientRequest(i, v)
           \/ \E i \in Server : AdvanceCommitIndex(i)
           \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                    msg.mtype \in {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {AppendEntriesRequest}} : DuplicateMessage(m)
\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*                    msg.mtype \in {RequestVoteRequest}} : DropMessage(m)

\*MyNext == 
\*\*           \/ \E i \in Server : Timeout(i)
\*\*           \/ \E i \in Server : Restart(i)
\*\*           \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
\*\*           \/ \E i \in Server : BecomeLeader(i)
\*           \/ \E i \in Server : state[i] /= Switch /\ AdvanceCommitIndex(i)
\*           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
\*                    msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
\*           \/ \E s \in Server: \E v \in unorderRequest[s], w \in DOMAIN switchBuffer: state[s] = Leader /\ w = v /\ ~(\E l \in DOMAIN log[s]: log[s][l] = switchBuffer[v]) /\ LeaderReceivesRequest(s, v)
\*                 
\*           \/ \E v \in DOMAIN switchBuffer, s \in Server: state[s] /= Switch /\ ~(<<switchBuffer[v].value, switchBuffer[v].term>> \in switchSentRecord[s]) /\ SwitchSendRequest(switchBuffer[v], s) 
\*           \/ \E i,j \in Server : i /= j /\ state[i] /= Switch /\ state[j] /= Switch  /\ AppendEntries(i, j)
\*           \/ \E v \in Value : SwitchClientRequest(v)
\*\*           \/ \E i \in Server, v \in Value : state[i] = Leader /\ ClientRequest(i, v)
\*          
\*           
\*\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*\*                    msg.mtype \in {AppendEntriesRequest}} : DuplicateMessage(m)
\*\*           \/ \E m \in {msg \in ValidMessage(messages) : 
\*\*                    msg.mtype \in {RequestVoteRequest}} : DropMessage(m)


\*MyNext == 
\*           \/ \E v \in Value, s \in Servers: state[s] = Leader /\ SwitchClientRequest(s, v)
\*           
\*           \/ \E v \in DOMAIN switchBuffer, s \in Servers: ~(<<switchBuffer[v].value, switchBuffer[v].term>> \notin switchSentRecord[s]) /\ SwitchSendRequest(switchBuffer[v], s) 
\*           
\*           \/ \E s \in Servers: \E v \in unorderRequest[s], w \in DOMAIN switchBuffer: state[s] = Leader /\ w = v /\ ~(\E l \in DOMAIN log[s]: log[s][l] = switchBuffer[v]) /\ LeaderReceivesRequest(s, v)
\*                 
\*           \/ \E i \in Servers: AdvanceCommitIndex(i)
\*           
\*           \/ \E i,j \in Servers: i /= j  /\ AppendEntries(i, j)
\*           
\*           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
\*                    msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
                    
MyNext == 
           \/ \E v \in Value, s \in Servers: state[s] = Leader /\ SwitchClientRequest(s, v)
           
           \/ \E v \in DOMAIN switchBuffer, s \in Servers: SwitchClientRequestReplicate(s, v) 
           
           \/ \E s \in Servers, v \in DOMAIN switchBuffer: state[s] = Leader  /\ LeaderIngressHovercRaftRequest(s, v)
                 
           \/ \E i \in Servers: AdvanceCommitIndex(i)
           
           \/ \E i,j \in Servers: i /= j  /\ AppendEntries(i, j)
           
           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                    msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)
           
          

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

MySpec == MyInit /\ [][MyNext]_vars

\* -------------------- Invariants --------------------

MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* Every (index, term) pair determines a log prefix.
\* From page 8 of the Raft paper: "If two logs contain an entry with the same index and term, then the logs are identical in all preceding entries."
LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* The committed entries in every log are a prefix of the
\* leader's log up to the leader's term (since a next Leader may already be
\* elected without the old leader stepping down yet)
LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])
            
    
\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Server :
        \/ CheckIsPrefix(Committed(i),Committed(j)) 
        \/ CheckIsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv) 

=============================================================================
\* Created by Ovidiu-Cristian Marcu
