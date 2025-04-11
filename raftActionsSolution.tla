---------------------------- MODULE raftActionsSolution ----------------------------

EXTENDS raftInit

----
\* Define state transitions

\* Modified to allow Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars elections, maxc, leaderCount, entryCommitStats
Restart(i) ==
    /\ state[i] = Leader \* limit restart to leaders todo mc
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, switchVars>>

\* Modified to restrict Timeout to just Followers
\* Server i times out and starts a new election. Follower -> Candidate
Timeout(i) == /\ state[i] \in {Follower} \*, Candidate
              /\ currentTerm[i] < MaxTerm
              /\ state' = [state EXCEPT ![i] = Candidate]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars, switchVars>>

\* Modified to restrict Leader transitions, bounded by MaxBecomeLeader
\* Candidate i transitions to leader. Candidate -> Leader
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, switchVars>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

\***************************** REQUEST VOTE **********************************************
\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype        |-> RequestVoteResponse,
                 mterm        |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 \* mlog is used just for the `elections' history variable for
                 \* the proof. It would not exist in a real implementation.
                 mlog         |-> log[i],
                 msource      |-> i,
                 mdest        |-> j],
                 m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars, switchVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

\***************************** AppendEntries **********************************************

\* Modified. Leader i receives a client request to add v to the log. up to MaxClientRequests.
(* ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests 
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>
*)
    
\* Modified. Switch receives a client request to foward to leader i and other followers. up to MaxClientRequests.
\* Implicitly adding new entry to Leader log and fowarding the request to the followers. In a real system we would also foward the request to the Leader and let it do the processing
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests 
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v, payload |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
        \* Foward request to all Servers. However entry is already added to Leaders log (though not commited).
        \* This simulates the fact that the Leader has already received the request and added it to its log, while followers are still to add it to their log
        /\ switchCache' = [s \in Server |-> Append(switchCache[s], entry)] 
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>
 

\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry. It was up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0  \* Only proceed if the leader has entries to send
    /\ nextIndex[i][j] <= Len(log[i])  \*  Only proceed if there are entries to send to this follower
    /\ matchIndex[i][j] < nextIndex[i][j] \* Only send if follower hasn't already acknowledged this index
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex]
           
           \* Build the metadata to be sent (remove payload).
           entries == << [term |-> entry.term, value |-> entry.value] >>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE 0
                          
           \* Send up to 1 entry, constrained by the end of the log.
           \* lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           \* entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
           
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries, \* This now only contains metadata information and not the entire request
                
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}), \* lastEntry}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats         
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, switchVars>>

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                       /\ \/ m.mentries = << >>
                          \/ /\ m.mentries /= << >>
                             /\ Len(log[i]) >= index
                             /\ log[i][index].term = m.mentries[1].term
                          \* This could make our commitIndex decrease (for
                          \* example if we process an old, duplicated request),
                          \* but that doesn't really affect anything.
                       /\ commitIndex' = [commitIndex EXCEPT ![i] =
                                              m.mcommitIndex]   
\*                       /\ commitIndex' = [commitIndex EXCEPT ![i] = 
\*                                            IF commitIndex[i] < m.mcommitIndex THEN 
\*                                                Min({m.mcommitIndex, Len(log[i])}) 
\*                                            ELSE 
\*                                                commitIndex[i]]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log>>
                   \/ \* conflict: remove 1 entry (simplified from original spec - assumes entry length 1)
                      \* since we do not send empty entries, we have to provide a larger set of values to ensure some progress
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1) \* Truncate log
                          IN log' = [log EXCEPT ![i] = newLog]
\*                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
\*                                          log[i][index2]]
\*                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ \E k \in DOMAIN switchCache[i] :  m.mentries[1].term = switchCache[i][k].term /\ m.mentries[1].value = switchCache[i][k].value 
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entries == SelectSeq(switchCache[i], LAMBDA entry: entry.term = m.mentries[1].term /\ entry.value = m.mentries[1].value)
                          IN log' = IF    entries /= << >> THEN log \* NO RPC was sent from switch to Server i with these values 
                                    ELSE  [log EXCEPT ![i] = Append(log[i], Head(entries))] \* Add this entry to log, this includes the payload
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchVars>> \* entryCommitStats unchanged on followers

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET \*newMatchIndex == IF matchIndex[i][j] > m.mmatchIndex THEN matchIndex[i][j] ELSE m.mmatchIndex
                 newMatchIndex == m.mmatchIndex
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN \*/\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = newMatchIndex + 1]
                /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                \*/\ matchIndex' = [matchIndex EXCEPT ![i][j] = newMatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats                     
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, switchVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server :
                                         matchIndex[i][k] >= index}
           \* The maximum indexes for which a quorum agrees
           agreeIndexes == {index \in 1..Len(log[i]) :
                                Agree(index) \in Quorum}
           \* New value for commitIndex'[i]
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN
                  Max(agreeIndexes)
              ELSE
                  commitIndex[i]
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           \* Identify the keys in entryCommitStats corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : key[1] \in committedIndexes }           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          \* Update the 'committed' flag for the relevant entries in entryCommitStats
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] \* Update record
                   ELSE entryCommitStats[key] ]                             \* Keep old record       
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, switchVars>>

\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

=============================================================================
\* Created by Ovidiu-Cristian Marcu
