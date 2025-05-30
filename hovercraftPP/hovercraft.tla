------------------------------ MODULE hovercraft ------------------------------
\*
\* Based on the formal specification for the Raft consensus algorithm.
\* We introduce the Hovercraft Switch&NetAgg components and verify safety properties.
\* We track message counts for advancing entry commit index.
\* Modified by Ovidiu Marcu.
\* Original Raft Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

\*In standard Raft the leader is the central hub.
\*A client sends a request only to the leader.
\*The leader must then replicate the entire request payload to all followers
\*The leader gathers acknowledgments from Followers, commits the entry, applies it, 
\*and sends a response to the client.
\*Bottleneck: The leader's network bandwidth and processing power for sending 
\*the full payload to every follower becomes a limiting factor as the 
\*cluster size (N) or request size increases. 
\*Throughput is limited by Leader_Bandwidth / ((N-1) * Request_Payload_Size).

\*We introduce a "Switch" abstraction (representing mechanisms like IP Multicast 
\*or a dedicated middlebox/programmable switch as used in the HovercRaft paper)
\*First Requirement: Client sends via Switch.
\*The Switch's responsibility is to deliver the request payload to all server 
\*nodes (Leader and Followers) "simultaneously".
\*Second Requirement: Leader orders via entry Metadata
\*The leader still receives the client request payload 
\*(via the Switch, just like followers).
\*Leader's primary role shifts from ordering and payload replication to just ordering.
\*The leader sends only a fixed-size metadata message to the followers.
\*This decouples the ordering traffic from the request payload size. 
\*The leader's outbound traffic for consensus becomes (N-1) * Metadata_Size, 
\*which is much smaller than replicating the full payload.
\*Third Requirement: Followers match payload and Metadata
\*Followers receive the raw request payloads directly from the Switch. 
\*Since network delivery (especially multicast) might lose data, 
\*followers must buffer these incoming requests temporarily.
\*When a follower receives the ordering metadata message from the leader, 
\*it uses the identifier in the metadata to find the corresponding payload 
\*in its temporary buffer.
\*Once matched, the follower places the request payload into its replicated log 
\*at the correct index specified by the leader's metadata.
\*Next, we introduce the NetAgg component of HovercRaft++.
\*The leader sends one message to NetAgg to delegate metadata ordering.
\*Once NetAgg receives acks from half the followers, he will send AggCommit to 
\*inform servers they can advance commit index.

\* Bonus exercise
\* We consider the network is perfect while the Switch and NetAgg will never fail.
\* However, Servers, followers and leaders can crash.
\* Enable Servers crashes and leader election and verify the safety properties.
\* Point to point recovery between Follower and Leader is partially addressed.
\* Even given perfect network and Switch/NetAgg not crashing, we need to consider point
\* to point recovery and implement it ; eg, Follower crashes, he is losing
\* messages from Switch, he will not be able to validate client requests from NetAgg.

EXTENDS Naturals, FiniteSets, Sequences, TLC

\************************* CONSTANTS *******************************************

\* The set of server IDs including the Switch and NetAgg
CONSTANTS Server

\* The set of client requests that can go into the log
\* Request -> Switch -> Leader -> NetAgg -> Followers
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, Switch, NetAgg

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

CONSTANTS AppendEntriesNetAggRequest, AppendEntriesNetAggResponse,
          AggCommit

\* For instrumentation to limit model state space
CONSTANTS MaxClientRequests

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

\************************* VARIABLES *******************************************

\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another. This is a function mapping Message to Nat.
VARIABLE messages

\* Counter for how many times each server has become leader
VARIABLE leaderCount

\* maximum client requests so far
VARIABLE maxc

\* variable for tracking entry commit message counts
\* Maps <<logIndex, logTerm>> to a record tracking message counts.
\* [ sentCount |-> Nat,   \* AppendEntriesRequests sent for the entry
\*   ackCount  |-> Nat,   \* AppendEntriesResponses received for this entry
\*   committed |-> Bool ] \* Flag indicating if the entry is committed
VARIABLE entryCommitStats

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

\* index into Server's Switch
VARIABLE switchIndex

\* Storage for requests received by the switch before they're replicated
\* Maps <<value, term>> to the full payload entry
VARIABLE switchBuffer

\* Each server's buffer of unordered requests received from the Switch
\* Maps from Server to a set of <<value, term>> pairs pending ordering
VARIABLE unorderedRequests

\* Records which <<value, term>> pairs the Switch has sent to each server.
\* Maps Server ID -> Set of <<Value, Term>> pairs.
VARIABLE switchSentRecord

\* New HovercRaft variables
hovercraftVars == <<switchBuffer, unorderedRequests, 
                    switchIndex, switchSentRecord>>

\* NetAgg variables
VARIABLE netAggIndex          \* Index of the NetAgg server
VARIABLE netAggMatchIndex     \* NetAgg's view of follower match indices
VARIABLE netAggPendingEntries \* Entries pending aggregation at NetAgg
VARIABLE netAggCommitIndex    \* NetAgg's view of commit index

netAggVars == <<netAggIndex, netAggMatchIndex, netAggPendingEntries, 
                netAggCommitIndex>>

\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm

\* The server's state (Follower, Candidate, or Leader).
VARIABLE state

\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor

serverVars == <<currentTerm, state, votedFor>>

\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry.
VARIABLE log

\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex

logVars == <<log, commitIndex>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded

\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted

\* A history variable used in the proof. This would not be present in an
\* implementation.
\* Function from each server that voted for this candidate in its currentTerm
\* to that voter's log.
VARIABLE voterLog

candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex

\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex

leaderVars == <<nextIndex, matchIndex>>

\* The set of server IDs excluding the current Switch server.
\*Servers == Server \ {switchIndex} \* see MyInit

VARIABLE Servers

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, 
          instrumentationVars, hovercraftVars, netAggVars, Servers>>

\************************* HELPERS *********************************************

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        msgs
    ELSE
        msgs @@ (m :> 1)

WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

min(a, b) == IF a < b THEN a ELSE b

ValidMessage(msgs) ==
    { m \in DOMAIN messages : msgs[m] > 0 }

\* The prefix of the log of server i that has been committed up to term x
CommittedTermPrefix(i, x) ==
\* Only if log of i is non-empty, and if there exists an entry up to the term x
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN
\* then, we use the subsequence up to the maximum committed term of the leader
      LET maxTermIndex ==
          CHOOSE y \in DOMAIN log[i] :
            /\ log[i][y].term <= x
            /\ \A z \in DOMAIN log[i] : log[i][z].term <= x  => y >= z
      IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    \* Otherwise the prefix is the empty tuple
    ELSE << >>

CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A i \in 1..Len(seq1) : seq1[i] = seq2[i]

\* The prefix of the log of server i that has been committed
Committed(i) ==
    IF commitIndex[i] = 0
    THEN << >>
    ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Servers: currentTerm[i] <= MaxTerm 
                 /\ Len(log[i]) <= MaxClientRequests ) 
                 /\ (\A m \in DOMAIN messages: messages[m] <= 1)

\*Symmetry == Permutations(Servers)

\************************* INIT ************************************************

InitHistoryVars == voterLog  = [i \in Servers |-> [j \in {} |-> <<>>]]

InitServerVars == /\ currentTerm = [i \in Servers |-> 1]
                  /\ state       = [i \in Servers |-> Follower]
                  /\ votedFor    = [i \in Servers |-> Nil]

InitCandidateVars == /\ votesResponded = [i \in Servers |-> {}]
                     /\ votesGranted   = [i \in Servers |-> {}]

\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Servers |-> [j \in Servers |-> 1]]
                  /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]

InitLogVars == /\ log          = [i \in Servers |-> << >>]
               /\ commitIndex  = [i \in Servers |-> 0]
               
InitHovercraftVars == 
    /\ switchBuffer = [vt \in {} |-> << >>]
    /\ unorderedRequests = [s \in Server |-> {}]
    /\ switchSentRecord = [s \in Server |-> {}]
               
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxc = 0
        /\ leaderCount = [i \in Servers |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> 
                   [ sentCount |-> 0, 
                     ackCount |-> 0, 
                     committed |-> FALSE ] ]
        /\ InitHovercraftVars
        /\ switchIndex = 4
        /\ Servers = Server \ {switchIndex}

\*used to start from a state with a Leader
\*we only verify normal case excluding leader election
MyInit ==
    LET ServerSet5 == CHOOSE S \in SUBSET(Server) : Cardinality(S) = 5
        TheSwitchId == CHOOSE s \in ServerSet5 : TRUE
        TempSet == ServerSet5 \ {TheSwitchId}
        TheNetAggId == CHOOSE n \in TempSet : TRUE
        TempSet2 == TempSet \ {TheNetAggId}
        TheLeaderId == CHOOSE l \in TempSet2 : TRUE
        FollowerIds == TempSet2 \ {TheLeaderId}

        TheState == [ s \in Server |->
                        IF s = TheSwitchId THEN Switch
                        ELSE IF s = TheNetAggId THEN NetAgg
                        ELSE IF s = TheLeaderId THEN Leader
                        ELSE IF s \in FollowerIds THEN Follower
                        ELSE Follower
                    ]
        TheSwitchIndex == TheSwitchId
        TheNetAggIndex == TheNetAggId
        TheServersSet == Server \ {TheSwitchIndex, TheNetAggIndex}
        Voters == TheServersSet \ {TheLeaderId}
    IN
    \* Constraint: Ensure Server has enough elements
    /\ Cardinality(Server) >= 5
    /\ PrintT("MyInit: switchIndex=" \o ToString(TheSwitchIndex))
    /\ PrintT("MyInit: netAggIndex=" \o ToString(TheNetAggIndex))
    /\ PrintT("MyInit: Leader is=" \o ToString(TheLeaderId))
    /\ PrintT("MyInit: Servers=" \o ToString(TheServersSet))
\*    /\ PrintT("MyInit: state[switchIndex]=" \o ToString(TheState[TheSwitchIndex]))
\*    /\ PrintT("MyInit: state[LeaderId]=" \o ToString(TheState[TheLeaderId]))
\*    /\ PrintT("MyInit: switchBuffer Domain=" \o ToString(DOMAIN [vt \in {} |-> {}]))

    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = TheLeaderId THEN 1 ELSE 0]
    /\ log = [s \in Server |-> << >>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = TheState
    /\ votedFor = [s \in Server |-> 
                   IF s = TheLeaderId THEN Nil ELSE TheLeaderId]
    /\ voterLog = [s \in Server |-> 
                   IF s = TheLeaderId THEN 
                   [ v \in Voters |-> <<>> ] ELSE [ v \in {} |-> <<>> ] ]
    /\ votesGranted = [s \in Server |-> 
                       IF s = TheLeaderId THEN Voters ELSE {}]
    /\ votesResponded = [s \in Server |-> 
                         IF s = TheLeaderId THEN Voters ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> 
                           [ sentCount |-> 0, 
                             ackCount |-> 0, 
                             committed |-> FALSE ] ]
    /\ switchBuffer = [vt \in {} |-> {}]
    /\ unorderedRequests = [s \in Server |-> {}]
    /\ switchSentRecord = [s \in Server |-> {}] 
    /\ switchIndex = TheSwitchIndex
    \* NetAgg initialization
    /\ netAggIndex = TheNetAggIndex
    /\ netAggMatchIndex = [s \in TheServersSet |-> 0]
    /\ netAggPendingEntries = {}
    /\ netAggCommitIndex = 0
    /\ Servers = TheServersSet

\***********************Define state transitions********************************

\* Modified to limit Restarts only for Leaders
\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* Also persists messages and instrumentation vars
Restart(i) ==
    /\ state[i] = Leader
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = {}]
    /\ switchSentRecord' = [switchSentRecord EXCEPT ![i] = {}]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, 
                   switchIndex, switchBuffer, Servers, netAggVars>>

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
              /\ UNCHANGED <<messages, leaderVars, logVars, 
                             instrumentationVars, hovercraftVars, Servers, netAggVars>>

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
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, 
                   logVars, maxc, entryCommitStats, hovercraftVars, Servers, netAggVars>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ state[i] \notin {Switch, NetAgg} /\ state[j] \notin {Switch, NetAgg}
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]    
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

\***************************** REQUEST VOTE ***********************************

\* Message handlers
\* i = recipient, j = sender, m = message

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    /\ state[i] = Candidate 
    /\ state[j] \notin {Switch, NetAgg}
    /\ j \notin votesResponded[i]
    /\ Send([mtype         |-> RequestVoteRequest,
             mterm         |-> currentTerm[i],
             mlastLogTerm  |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource       |-> i,
             mdest         |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

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
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, 
                      instrumentationVars, hovercraftVars, Servers, netAggVars>>

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
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

\***************************** AppendEntries **********************************

\* Old raft. Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ maxc < MaxClientRequests 
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : 
             log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, 
                       ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, 
                   commitIndex, leaderCount, hovercraftVars, Servers, netAggVars>>

\* Leader i ingests a request v that has been replicated to its unordered set.
LeaderIngestHovercRaftRequest(i, vt) ==
    /\ state[i] = Leader
    /\ vt \in unorderedRequests[i]      \* Request ID is pending for the leader
    /\ vt \in DOMAIN switchBuffer       \* Full request data exists in switch buffer to reduce payload duplication 
    /\ maxc < MaxClientRequests
    /\ LET entryFromBuffer == switchBuffer[vt]
           v == vt[1]  \* Extract value from <<value, term>> pair
           \* Use leader's current term, keep value and payload from buffer
           newEntry == [term |-> currentTerm[i], 
                        value |-> v, 
                        payload |-> entryFromBuffer.payload]
           entryExists == \E k \in DOMAIN log[i] : 
                          log[i][k].value = v /\ log[i][k].term = newEntry.term
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], newEntry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, newEntry.term>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxc' = IF entryExists THEN maxc ELSE maxc + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, 
                                   ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
        /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \ {vt}]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, 
                   commitIndex, leaderCount, switchIndex, switchBuffer, 
                   Servers, switchSentRecord, netAggVars>>


\* Client sends a request to the Switch, which buffers it, 
\* not yet replicated to servers
\* s is the Switch, i is the leader, v is the request value 
\* (along with term will represent a request ID in this model)
SwitchClientRequest(s, i, v) ==
    /\ state[s] = Switch  \* Only the switch server can process client requests
    /\ state[i] = Leader
    /\ LET vt == <<v, currentTerm[i]>>  \* Create <<value, term>> pair
       IN
       /\ vt \notin DOMAIN switchBuffer  \* Only process new requests
       /\ LET entryWithPayload == [term |-> currentTerm[i], 
                                   value |-> v, payload |-> v]
          IN
          /\ switchBuffer' = switchBuffer @@ (vt :> entryWithPayload)
          /\ unorderedRequests' = 
             [unorderedRequests EXCEPT ![s] = unorderedRequests[s] \cup {vt}]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, 
                   leaderCount, entryCommitStats, switchIndex, maxc, 
                   Servers, switchSentRecord, netAggVars>>

\* The Switch replicates vt to one server 'i' from Servers.
\* Prevents resending the same <<v, term>> pair to the same server 'i'.
SwitchClientRequestReplicate(s, i, vt) ==
    /\ state[s] = Switch  \* Only the switch server can replicate requests
    /\ state[i] \notin {Switch, NetAgg} \* Target server is not the switch
    /\ vt \in unorderedRequests[s] \* Request must be pending at the switch
    /\ vt \notin switchSentRecord[i]  \* Ensure this specific v/term pair hasn't been sent to i yet
    /\ vt \notin unorderedRequests[i] \* Check that the target doesn't already have it pending
    /\ unorderedRequests' = [unorderedRequests EXCEPT ![i] = @ \cup {vt}]
    /\ switchSentRecord' = 
       [switchSentRecord EXCEPT ![i] = @ \cup {vt}]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   leaderCount, entryCommitStats, switchIndex, switchBuffer, 
                   maxc, Servers, netAggVars>>

\* The Switch replicates vt to ALL servers at once (except those that already have it).
\* This reduces state space by avoiding intermediate states where only some servers have received the request.
SwitchClientRequestReplicateAll(s, vt) ==
    /\ state[s] = Switch  \* Only the switch server can replicate requests
    /\ vt \in unorderedRequests[s] \* Request must be pending at the switch
    /\ LET \* Find all servers that haven't received this v/term pair yet
           targetServers == {i \in Server : state[i] \notin {Switch, NetAgg} /\ vt \notin switchSentRecord[i]}
       IN
       /\ targetServers /= {}  \* At least one server needs the request
       /\ unorderedRequests' = [i \in Server |->
            IF i \in targetServers 
            THEN unorderedRequests[i] \cup {vt}
            ELSE unorderedRequests[i]]
       /\ switchSentRecord' = [i \in Server |->
            IF i \in targetServers
            THEN switchSentRecord[i] \cup {vt}
            ELSE switchSentRecord[i]]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars,
                   leaderCount, entryCommitStats, switchIndex, switchBuffer, 
                   maxc, Servers, netAggVars>>

\* Modified. Leader i sends j an AppendEntries request containing exactly 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\* Sending empty entries is done for telling followers Leader is alive.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0  
    \* Only proceed if the leader has entries to send
    /\ nextIndex[i][j] <= Len(log[i])  
    \*  Only proceed if there are entries to send to this follower
    /\ matchIndex[i][j] < nextIndex[i][j] 
    \* Only send if follower hasn't already acknowledged this index
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex]
           entryMetadata == [term |-> entry.term, value |-> entry.value]
           entries == << entryMetadata >>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           \* lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           \* entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
           
       IN Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}),
                msource        |-> i,
                mdest          |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats 
               /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats         
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, 
                   leaderCount, hovercraftVars, Servers, netAggVars>>

\* Leader i sends AppendEntries to NetAgg instead of directly to followers
AppendEntriesToNetAgg(i) ==
    /\ state[i] = Leader
    /\ state[netAggIndex] = NetAgg
    /\ Len(log[i]) > 0
    /\ LET nextIndexMin == Min({nextIndex[i][j] : j \in Servers \ {i}})
       IN nextIndexMin <= Len(log[i])
    /\ LET entryIndex == Min({nextIndex[i][j] : j \in Servers \ {i}})
           entry == log[i][entryIndex]
           entryMetadata == [term |-> entry.term, value |-> entry.value]
           entries == << entryMetadata >>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE 0
       IN Send([mtype          |-> AppendEntriesNetAggRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                mentryIndex    |-> entryIndex,
                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}),
                msource        |-> i,
                mdest          |-> netAggIndex])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, netAggVars, Servers, netAggVars>>

\* NetAgg receives AppendEntries from leader and forwards to all followers; atomic for now
NetAggForwardAppendEntries(m, f) ==
    /\ state[f] = Follower
    /\ m.mdest = netAggIndex
    /\ m.mtype = AppendEntriesNetAggRequest
    /\ LET leaderId == m.msource           \* Original leader for context
           followers == Servers \ {leaderId}
       IN /\ Send([mtype          |-> AppendEntriesRequest,
                     mterm          |-> m.mterm,
                     mprevLogIndex  |-> m.mprevLogIndex,
                     mprevLogTerm   |-> m.mprevLogTerm,
                     mentries       |-> m.mentries,
                     mlog           |-> m.mlog,         \* Keep original leader's log for history/proof if needed
                     mcommitIndex   |-> m.mcommitIndex,
                     msource        |-> netAggIndex,    \* <<< CHANGED: Source is NetAgg
                     mdest          |-> f,
                     moriginalLeader |-> leaderId ])    \* Optional: Pass original leader if needed by follower
          /\ netAggPendingEntries' = netAggPendingEntries \cup
                {[entryIndex |-> m.mentryIndex,
                  entryTerm  |-> m.mentries[1].term,
                  leaderId   |-> leaderId,    \* Still track original leader
                  ackCount   |-> 0,           \* Will be replaced by acksFrom
                  acksFrom   |-> {} ]}        \* <<< ADDED: Initialize set of ACKing followers
\*    /\ Discard(m) \* Discard the AppendEntriesNetAggRequest
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars,
                   instrumentationVars, hovercraftVars,
                   netAggIndex, netAggMatchIndex, netAggCommitIndex, Servers>>

\* NetAgg receives AppendEntries from leader and forwards to ALL followers atomically
NetAggForwardAppendEntriesAll(m) ==
    /\ m.mdest = netAggIndex
    /\ m.mtype = AppendEntriesNetAggRequest
    /\ LET leaderId == m.msource
           followers == Servers \ {leaderId}  \* All servers except the leader
           \* Create the set of messages to send to all followers
           followerMessages == { [ mtype          |-> AppendEntriesRequest,
                                  mterm          |-> m.mterm,
                                  mprevLogIndex  |-> m.mprevLogIndex,
                                  mprevLogTerm   |-> m.mprevLogTerm,
                                  mentries       |-> m.mentries,
                                  mlog           |-> m.mlog,
                                  mcommitIndex   |-> m.mcommitIndex,
                                  msource        |-> netAggIndex,
                                  mdest          |-> f,
                                  moriginalLeader |-> leaderId ]
                                : f \in followers }
           \* Remove the processed message and add all new messages
           RemainingActiveMessages == ValidMessage(WithoutMessage(m, messages))
       IN
       /\ messages' = [ msgRec \in RemainingActiveMessages \cup followerMessages |-> 1 ]
       /\ netAggPendingEntries' = netAggPendingEntries \cup
             {[entryIndex |-> m.mentryIndex,
               entryTerm  |-> m.mentries[1].term,
               leaderId   |-> leaderId,
               ackCount   |-> 0,
               acksFrom   |-> {} ]}
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars,
                   instrumentationVars, hovercraftVars,
                   netAggIndex, netAggMatchIndex, netAggCommitIndex, Servers>>

\* NetAgg receives AppendEntries response from follower
NetAggHandleAppendEntriesResponse(m) ==
    /\ m.mtype = AppendEntriesResponse
    /\ m.mdest = netAggIndex   \* Message is for NetAgg
    /\ m.msuccess              \* Process successful ACKs
    /\ \E pending \in netAggPendingEntries :
        /\ m.msource \in (Servers \ {pending.leaderId})  \* Response is from a follower (in Servers) of the leader for this pending entry
        /\ m.mmatchIndex >= pending.entryIndex           \* Follower acknowledged this entry (or beyond)
        /\ m.msource \notin pending.acksFrom             \* This is a new ACK from this follower for this item
        /\ LET updatedPending == [pending EXCEPT !.acksFrom = @ \cup {m.msource} ]
               RequiredFollowerAcks == Cardinality(Servers) \div 2 \* Leader has one, need this many more from followers
           IN
           /\ netAggMatchIndex' = [netAggMatchIndex EXCEPT ![m.msource] = m.mmatchIndex]
           /\ IF Cardinality(updatedPending.acksFrom) >= RequiredFollowerAcks
              THEN \* Majority reached, send AGG_COMMIT to all Raft Servers
                   LET AggCommitMsgsSet == { [ mtype        |-> AggCommit,
                                               mcommitIndex |-> pending.entryIndex,
                                               msource      |-> netAggIndex,
                                               mdest        |-> srv ]
                                             : srv \in Servers } \* Send to all Raft servers
                       \* Messages that were valid, excluding the one we just processed
                       RemainingActiveMessages == ValidMessage(WithoutMessage(m, messages))
                   IN
                   /\ messages' = [ msgRec \in RemainingActiveMessages \cup AggCommitMsgsSet |-> 1 ]
                       \* This creates the new message bag:
                       \* - 'm' is effectively removed (as it's not in RemainingActiveMessages).
                       \* - All messages in AggCommitMsgsSet are added (or kept if already there by chance).
                       \* - All other previously active messages are preserved.
                       \* - All messages in the resulting bag have count 1, respecting MyConstraint.
                   /\ netAggPendingEntries' = netAggPendingEntries \ {pending} \* Remove committed entry from pending
                   /\ netAggCommitIndex' = Max({netAggCommitIndex, pending.entryIndex})
                   /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars,
                                  instrumentationVars, hovercraftVars, netAggIndex, Servers>>
              ELSE \* Majority not yet reached
                   /\ Discard(m) \* This defines messages' = WithoutMessage(m, messages)
                   /\ netAggPendingEntries' = (netAggPendingEntries \ {pending}) \cup {updatedPending} \* Update with new ACK
                   /\ UNCHANGED netAggCommitIndex
                   /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars,
                                  instrumentationVars, hovercraftVars, netAggIndex, Servers,
                                  netAggMatchIndex >>



\* Server receives AGG_COMMIT from NetAgg
HandleAggCommit(i, m) ==
    /\ m.mtype = AggCommit
    /\ m.mdest = i
    /\ state[i] \in {Leader, Follower}
    /\ LET receivedCommitIndex == m.mcommitIndex  \* Added for clarity
           currentLogLen == Len(log[i])          \* Added: get current log length
           newAdvancedCommitIndex == Max({commitIndex[i], receivedCommitIndex}) \* Renamed & Logic: advance if m.mcommitIndex is higher
           newCommitIndex == Min({newAdvancedCommitIndex, currentLogLen})     \* Modified: cap at current log length
           
           committedIndexes == { k \in Nat : /\ k > commitIndex[i]
                                             /\ k <= newCommitIndex }
           keysToUpdate == IF state[i] = Leader 
                          THEN { key \in DOMAIN entryCommitStats : 
                                 key[1] \in committedIndexes }
                          ELSE {}
       IN
       /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
       /\ entryCommitStats' = IF state[i] = Leader
                              THEN [ key \in DOMAIN entryCommitStats |->
                                     IF key \in keysToUpdate
                                     THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] 
                                     ELSE entryCommitStats[key] ]
                              ELSE entryCommitStats
       /\ IF state[i] = Leader
          THEN /\ nextIndex' = [nextIndex EXCEPT ![i] = 
                                 [j \in Server |-> 
                                   IF j \in Servers \ {i} 
                                   THEN Max({nextIndex[i][j], newCommitIndex + 1})
                                   ELSE nextIndex[i][j]]]
               /\ matchIndex' = [matchIndex EXCEPT ![i] = 
                                 [j \in Server |-> 
                                   IF j \in Servers \ {i}
                                   THEN Max({matchIndex[i][j], newCommitIndex})
                                   ELSE matchIndex[i][j]]]
          ELSE UNCHANGED <<nextIndex, matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, log, maxc, leaderCount,
                   hovercraftVars, netAggVars, Servers, netAggVars>>
                                      
\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
        rejectHovercraftMismatchCondition == 
            /\ m.mentries /= << >>  \* There must be an entry to check
            /\ LET entry == m.mentries[1]
                   v == entry.value 
                   msgTerm == entry.term 
               IN 
               \lnot ( /\ <<v, msgTerm>> \in unorderedRequests[i]      
                        /\ <<v, msgTerm>> \in DOMAIN switchBuffer
                        /\ switchBuffer[<<v, msgTerm>>].term = msgTerm )
\*        respondTo == IF j = netAggIndex 
\*                     THEN netAggIndex \*should be j in hovercraft/Switch
\*                     ELSE j
        respondTo == IF m.msource = netAggIndex /\ ~logOk
                       THEN CHOOSE l \in Servers : state[l] = Leader
                       ELSE m.msource
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ rejectHovercraftMismatchCondition
             /\ Reply([mtype           |-> AppendEntriesResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mmatchIndex     |-> 0,
                       msource         |-> i,
                       mdest           |-> respondTo],
                       m)
             /\ UNCHANGED <<serverVars, logVars, unorderedRequests>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, 
                            unorderedRequests>>
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
\*               /\ commitIndex' = [commitIndex EXCEPT ![i] = 
\*                                    IF commitIndex[i] < m.mcommitIndex THEN 
\*                                        Min({m.mcommitIndex, Len(log[i])}) 
\*                                    ELSE 
\*                                        commitIndex[i]]
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> respondTo],
                                 m)
                       /\ UNCHANGED <<serverVars, log, unorderedRequests>>
                   \/ \* conflict: remove 1 entry 
\*                       (simplified from original spec - assumes entry length 1)
                      \* ATTENTION since we do not send empty entries, 
\*                   we have to provide a larger set of Values to ensure progress
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET newLog == SubSeq(log[i], 1, index - 1)
                          IN log' = [log EXCEPT ![i] = newLog] \* Truncate log
                       /\ UNCHANGED <<serverVars, commitIndex, messages, 
                                      unorderedRequests>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ \lnot rejectHovercraftMismatchCondition
                       /\ LET \* mark unorderedRequests done
                           entryMetadata == m.mentries[1]
                           v == entryMetadata.value
                           msgTerm == entryMetadata.term
                           vt == <<v, msgTerm>>
                           fullEntryFromCache == switchBuffer[vt]
                           entryForLocalLog == [ term  |-> entryMetadata.term, 
                                       value |-> entryMetadata.value, 
                                       payload |-> fullEntryFromCache.payload ]
                          IN
                          /\ log' = [log EXCEPT ![i] = 
                             Append(log[i], entryForLocalLog)]
                          /\ unorderedRequests' = 
                            [unorderedRequests EXCEPT ![i] = 
                             @ \ {vt}]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, 
           switchBuffer, switchIndex, switchSentRecord, Servers, netAggVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ LET
                 newMatchIndex == m.mmatchIndex
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>> \* Invalid index or empty log
             IN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
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
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, hovercraftVars, Servers, netAggVars>>

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
           \* Identify the keys in entryCommitStats 
           \* corresponding to newly committed entries
           keysToUpdate == { key \in DOMAIN entryCommitStats : 
                             key[1] \in committedIndexes }           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ entryCommitStats' =
               [ key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [ entryCommitStats[key] EXCEPT !.committed = TRUE ] 
                   ELSE entryCommitStats[key] ]                                   
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, 
                   leaderCount, hovercraftVars, Servers, netAggVars>>

\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, 
                   instrumentationVars, hovercraftVars, Servers, netAggVars>>

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

MySwitchPlusPlusNext == 
   \* Switch actions (client request handling)
   \/ \E i \in Servers, v \in Value : 
        state[i] = Leader /\ SwitchClientRequest(switchIndex, i, v)
        
\*   \/ \E i \in Servers,v \in DOMAIN switchBuffer : 
\*        SwitchClientRequestReplicate(switchIndex, i, v)

   \/ \E v \in DOMAIN switchBuffer : 
        SwitchClientRequestReplicateAll(switchIndex, v)

   \/ \E i \in Servers, v \in DOMAIN switchBuffer : 
        state[i] = Leader /\ LeaderIngestHovercRaftRequest(i, v)
   
   \* NetAgg path: Leader sends to NetAgg instead of direct AppendEntries
   \/ \E i \in Servers : 
        state[i] = Leader /\ AppendEntriesToNetAgg(i)
   
   \* NetAgg forwards and collects
\*   \/ \E f \in Servers, m \in {msg \in ValidMessage(messages) : 
\*        msg.mtype = AppendEntriesNetAggRequest} : NetAggForwardAppendEntries(m, f)

   \/ \E m \in {msg \in ValidMessage(messages) : 
        msg.mtype = AppendEntriesNetAggRequest} : NetAggForwardAppendEntriesAll(m)

   \* Regular message handling (for AppendEntries from NetAgg to followers)
   \/ \E m \in {msg \in ValidMessage(messages) : 
        msg.mtype \in {AppendEntriesRequest}} : 
        Receive(m)


   \/ \E m \in {msg \in ValidMessage(messages) : 
        msg.mtype = AppendEntriesResponse /\ 
        msg.mdest = netAggIndex} :
        NetAggHandleAppendEntriesResponse(m)
   
   \* Handle AGG_COMMIT
   \/ \E i \in Servers, m \in {msg \in ValidMessage(messages) : 
        msg.mtype = AggCommit} : m.mdest = i /\ HandleAggCommit(i, m)
   
   \* Handle AppendEntriesResponse failing messages that go to leader
   \* to be enabled for point to point recovery todo!
\*   \/ \E m \in {msg \in ValidMessage(messages) : 
\*        msg.mtype = AppendEntriesResponse /\ 
\*        msg.mdest \in Servers /\ state[msg.mdest] = Leader} :
\*        Receive(m)
      
   \* Leader doesn't use AdvanceCommitIndex in HovercRaft++
   \* Commit advancement happens via AGG_COMMIT
   
MySwitchPlusPlusSpec == MyInit /\ [][MySwitchPlusPlusNext]_vars


\* -------------------- Invariants --------------------

MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

\* Every (index, term) pair determines a log prefix.
\* From page 8 of the Raft paper: "If two logs contain an entry with the 
\*same index and term, then the logs are identical in all preceding entries."
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
THEOREM MySwitchPlusPlusSpec => ([]LogInv /\ []LeaderCompletenessInv 
                         /\ []LogMatchingInv /\ []MoreThanOneLeaderInv) 

\*instrumentation and performance invariants

\* Fake invariant: Checks if every server (including the Switch) 
\*has exactly one unordered request pending.
AllServersHaveOneUnorderedRequestInv ==
    \E s \in Servers :  Cardinality(unorderedRequests[s]) /= 2

\* A leader's maxc should remain under MaxClientRequests
MaxCInv == (\E i \in Server : state[i] = Leader) => maxc <= MaxClientRequests

\* No server can become leader more than MaxBecomeLeader times
LeaderCountInv == \E i \in Server : 
  (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

\* No server can have a term exceeding MaxTerm
MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

\* Check lower bound for message counts on committed entries
\* For any entry that has been marked as committed, 
\* verify that either the number of AppendEntries requests sent OR 
\* the number of successful acknowledgments received
\* is at least the minimum number of followers required to form a majority.
\* will fail when an entry was sent twice to a follower 
\* and no response was acked yet, which is normal
EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Servers) - 1
        MinFollowersForMajority == Cardinality(Servers) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= 
                MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= 
                MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

\* Check that committed entries received acknowledgments 
\* from a majority of followers.
EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Servers)
        \* Minimum number of followers needed (in addition to the leader)
        \* to reach a majority for committing an entry.
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

\* fake inv to obtain a trace
LeaderCommitted ==
    \E i \in Servers : commitIndex[i] /= 2

NetAggMatchProgress ==
    \E i \in Servers : state[i] = Follower /\ netAggMatchIndex[i] /= 2


NeverAdvancesRaftInv == \A i \in Servers : commitIndex[i] = 0

NoAppendEntriesNetAggRequestInFlightInv ==
    \A m_record \in DOMAIN messages :
        messages[m_record] = 0 \/ m_record.mtype /= AppendEntriesNetAggRequest

NoAggCommitInFlightInv ==
    \A m_record \in DOMAIN messages :
        m_record.mtype /= AppendEntriesResponse


NoAEFromNetAggToFollowersInv ==
    LET LeaderId == CHOOSE l \in Servers : state[l] = Leader
    IN
    \A m_record \in DOMAIN messages :
        \/ messages[m_record] = 0
        \/ m_record.mtype /= AppendEntriesRequest
        \/ m_record.msource /= LeaderId  \* AE should appear to come from actual leader
        \/ m_record.mdest = netAggIndex
        \/ m_record.mdest = switchIndex
        \/ m_record.mdest = LeaderId     \* AE shouldn't go from Leader to Leader
        
=============================================================================