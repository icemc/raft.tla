--------------------------- MODULE hovercraft_024581674A ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of client requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, Switch

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse, RecoveryRequest

\* for instrumentation to limit model state space
CONSTANTS MaxClientRequests

\* Maximum times a server can become a leader
CONSTANTS MaxBecomeLeader

\* Maximum term number allowed in the model
CONSTANTS MaxTerm

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
\* [ sentCount |-> Nat,   \* AppendEntriesRequests sent for this entry
\*   ackCount  |-> Nat,   \* Successful AppendEntriesResponses received for this entry
\*   committed |-> Bool ] \* Flag indicating if the entry is committed
VARIABLE entryCommitStats

instrumentationVars == <<leaderCount, maxc, entryCommitStats>>

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
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
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

VARIABLES switchBuffer, switchIndex, switchSentRecord, unorderedRequest

hovercraftVars == <<switchBuffer, switchIndex, switchSentRecord, unorderedRequest>>


VARIABLE Servers

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>


\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Servers) : Cardinality(i) * 2 > Cardinality(Servers)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        msgs
       \* [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2 ]
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

MyConstraint == (\A i \in Servers: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests ) 
                /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Symmetry == Permutations(Server)

\* new bag of messages with one more m in it. the following from orig spec necessary for Drop
\*WithMessage(m, msgs) ==
\*    IF m \in DOMAIN msgs THEN
\*        [msgs EXCEPT ![m] = msgs[m] + 1]
\*    ELSE
\*        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\*WithoutMessage(m, msgs) ==
\*    IF m \in DOMAIN msgs THEN
\*        IF msgs[m] <= 1 THEN [i \in DOMAIN msgs \ {m} |-> msgs[i]]
\*        ELSE [msgs EXCEPT ![m] = msgs[m] - 1]
\*    ELSE
\*        msgs


InitHistoryVars == voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]
\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log          = [i \in Server |-> << >>]
               /\ commitIndex  = [i \in Server |-> 0]
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxc = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize new variable

\* MyInit remains unchanged for the core Raft state, entryCommitStats is handled in Init.
MyInit ==
    LET ServerIds == CHOOSE ids \in [1..4 -> Server] :
                        \A i, j \in 1..4 : i # j => ids[i] # ids[j]
        r1 == ServerIds[1]
        r2 == ServerIds[2]
        r3 == ServerIds[3]
        r4 == ServerIds[4]
    IN
    /\ switchIndex = r1
    /\ Servers = Server \ {r1}
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxc = 0
    /\ messages = [m \in {} |-> 0]  \* Start with empty messages
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |->
              CASE s = switchIndex -> Switch
              [] s = r2 -> Leader
              [] OTHER  -> Follower]
    /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
    /\ voterLog = [s \in Server |-> IF s = r2 THEN (r3 :> <<>> @@ r4 :> <<>>) ELSE <<>>]
    /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r3, r4} ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r3, r4} ELSE {}]
    /\ entryCommitStats = [ idx_term \in {} |-> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ] ] \* Initialize here too
    /\ switchSentRecord = [s \in Server |-> {} ]
    /\ unorderedRequest = [s \in Server |-> {} ]
    /\ switchBuffer = [i \in {} |-> [term: Nat, value: STRING, payload: STRING]]
\*    /\ PrintT("MyInit: serversWithoutSwitch=" \o ToString(SeversWithoutSwitch))
\*    /\ PrintT("MyInit: Quorum=" \o ToString(Quorum))

\* to be used directly in model Init the value
\*MyInit2 ==
\*    /\  commitIndex = (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  currentTerm = (r1 :> 2 @@ r2 :> 2 @@ r3 :> 2)
\*    /\  entryCommitStats = << >>
\*    /\  leaderCount = (r1 :> 1 @@ r2 :> 0 @@ r3 :> 0)
\*    /\  log = (r1 :> <<>> @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  matchIndex = ( r1 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r2 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) @@
\*      r3 :> (r1 :> 0 @@ r2 :> 0 @@ r3 :> 0) )
\*    /\  maxc = 0
\*    /\  messages = << >>
\*    /\  nextIndex = ( r1 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r2 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) @@
\*      r3 :> (r1 :> 1 @@ r2 :> 1 @@ r3 :> 1) )
\*    /\  state = (r1 :> Leader @@ r2 :> Follower @@ r3 :> Follower)
\*    /\  votedFor = (r1 :> Nil @@ r2 :> r1 @@ r3 :> r1)
\*    /\  voterLog = (r1 :> (r1 :> <<>>) @@ r2 :> <<>> @@ r3 :> <<>>)
\*    /\  votesGranted = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})
\*    /\  votesResponded = (r1 :> {r1} @@ r2 :> {} @@ r3 :> {})


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
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars, hovercraftVars, Servers>>

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
              /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

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
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxc, entryCommitStats, hovercraftVars, Servers>>

\* Modified up to MaxTerm; Back To Follower
\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

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
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

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
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

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
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

\***************************** AppendEntries **********************************************

\* Modified. Leader i receives a client request to add v to the log. up to MaxClientRequests.
SwitchClientRequest(i, v) == 
    /\ state[i] = Leader
    /\ \E s \in Server: state[s] = Switch
    \* Make sure prevoius requests have been served before serving new request (for debugging purposes)
    \* /\ \A i \in DOMAIN switchBuffer, s \in Servers: <<switchBuffer[i].value, switchBuffer[i].term>> \in switchSentRecord[s]
    /\ maxc < MaxClientRequests
    /\ LET 
           entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v, payload |-> v]
           entryExists == \E r \in DOMAIN switchBuffer: entry = switchBuffer[r]
      IN
           IF ~entryExists THEN
            /\ maxc' = maxc + 1
            /\ switchBuffer' = switchBuffer @@ (v :> entry)
           ELSE UNCHANGED <<maxc, switchBuffer>>
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, leaderCount, entryCommitStats, switchIndex, switchSentRecord, unorderedRequest, Servers>>


SwitchClientRequestReplicate(i, v) == 
    /\ state[i] = Leader \* Comment this out to send message to all servers
    /\ \E j \in DOMAIN switchBuffer: j = v \* Check if v is a valid switch request
    /\ ~(\E entry \in switchSentRecord[i]: entry = <<switchBuffer[v].value, switchBuffer[v].term>>)
    /\ switchSentRecord' = [switchSentRecord EXCEPT ![i] = switchSentRecord[i] \cup {<<switchBuffer[v].value, switchBuffer[v].term>>} ]
    /\ unorderedRequest' = [unorderedRequest EXCEPT ![i] = unorderedRequest[i] \cup {switchBuffer[v].value} ]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchIndex, switchBuffer, Servers>> 

\* Leader Receives request from switch and appends it to its log. This will trigger Append Entries to be sent
LeaderIngressHovercRaftRequest(i, v) == 
    /\ state[i] = Leader
    /\ \E j \in DOMAIN switchBuffer: v = j \* Check if v is a valid switch request
    /\ \E j \in unorderedRequest[i] : v = j \* Check if leader server has already received request v from switch
    /\ ~(\E j \in DOMAIN log[i] : log[i][j] = switchBuffer[v])
\*    TODO add enabling condition that checks if value v has been sent to all servers (check switchSentRecords)
\*    /\ \A s \in Server: (state[s] = Switch) \/ (state[s] /= Switch /\ v \in unorderedRequest[s])
    /\ LET entryTerm == switchBuffer[v].term
           entry == switchBuffer[v]
\*           entryExist == \E j \in DOMAIN log[i] : log[i][j] = switchBuffer[v]
           newLog == Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ unorderedRequest' = [unorderedRequest EXCEPT ![i] = @ \ {v}]
        /\ entryCommitStats' =
              IF newEntryIndex > 0 \* Only add stats for truly new entries
              THEN entryCommitStats @@ (newEntryKey :> [ sentCount |-> 0, ackCount |-> 0, committed |-> FALSE ])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount, maxc, switchBuffer, switchIndex, switchSentRecord, Servers>>


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
           entries == << [term |-> entry.term, value |-> entry.value] >>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN
                              log[i][prevLogIndex].term
                          ELSE 0 
           message == [mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries, \* This now only contains metadata information and not the entire request
                
                \* mlog is used as a history variable for the proof.
                \* It would not exist in a real implementation.
\*                mlog           |-> log[i],
                mcommitIndex   |-> Min({commitIndex[i], entryIndex}), \* lastEntry}),
                msource        |-> i,
                mdest          |-> j]
           \* Send up to 1 entry, constrained by the end of the log.
           \* lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           \* entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
           
       IN Send(message)
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats         
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxc, leaderCount, hovercraftVars, Servers>>  

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
             /\ UNCHANGED <<serverVars, logVars, unorderedRequest>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, unorderedRequest>>
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
\*                       /\ commitIndex' = [commitIndex EXCEPT ![i] = @ + 1]     
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
                       /\ UNCHANGED <<serverVars, log, unorderedRequest>>
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
                       /\ UNCHANGED <<serverVars, commitIndex, messages, unorderedRequest>>

                   \/ \* no conflict but server i can't find request in its unorder requests list. Send recovery message to Server j
                       /\ m.mentries /= << >>
                       \* request not found in servers unordered request list
                       /\ ~(\E k \in unorderedRequest[i]: k = m.mentries[1].value)                      
                       /\ LET message == [mtype     |-> RecoveryRequest,
                                          mterm          |-> currentTerm[i],
                                          mentries       |-> m.mentries,
                                          msource         |-> i,
                                          mdest           |-> j]
                          IN Send(message)
                          \* Do not discard the append entries request
                       /\ UNCHANGED <<serverVars, commitIndex, log, unorderedRequest>>
                       
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ \E k \in unorderedRequest[i]: k = m.mentries[1].value
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ LET entryId == CHOOSE id \in DOMAIN switchBuffer: switchBuffer[id].term = m.mentries[1].term /\ switchBuffer[id].value = m.mentries[1].value 
                              entry == switchBuffer[entryId]
                          IN /\ log' = [log EXCEPT ![i] = Append(log[i], entry)] \* Add this entry to log, this includes the payload
                             /\ unorderedRequest' = [unorderedRequest EXCEPT ![i] = @ \ {m.mentries[1].value}]
                       /\ UNCHANGED <<serverVars, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchBuffer, switchIndex, switchSentRecord, Servers>> \* entryCommitStats unchanged on followers

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
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxc, leaderCount, hovercraftVars, Servers>>

\* Server i receives RecoveryRequest message from server j
HandleRecoveryRequest(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ m.mtype = RecoveryRequest
    /\ m.mentries /= << >>
    /\ \E entry \in DOMAIN switchBuffer: entry = m.mentries[1].value \* Check that this entry has been received by switch
    /\ Discard(m)
    /\ unorderedRequest' = [unorderedRequest EXCEPT ![j] = unorderedRequest[j] \cup {switchBuffer[m.mentries[1].value].value} ] \* Snoop the value request from switchBuffer

    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchBuffer, switchIndex, switchSentRecord, Servers>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Servers :
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
        \*   /\ PrintT("AdvanceCommitIndex: newCommitIndex=" \o ToString(newCommitIndex))       
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxc, leaderCount, hovercraftVars, Servers>>

\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, hovercraftVars, Servers>>

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

                  
MyNext == 
           \/ \E v \in Value, s \in Servers: state[s] = Leader /\ SwitchClientRequest(s, v)
           
           \/ \E v \in DOMAIN switchBuffer, s \in Servers: SwitchClientRequestReplicate(s, v) 
           
           \/ \E s \in Servers, v \in DOMAIN switchBuffer: state[s] = Leader  /\ LeaderIngressHovercRaftRequest(s, v)
                 
           \/ \E i \in Servers: AdvanceCommitIndex(i)
           
           \/ \E i,j \in Servers: i /= j  /\ AppendEntries(i, j)
           
           \/ \E m \in {msg \in ValidMessage(messages) : \* to visualize possible messages
                    msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse, RecoveryRequest}} : Receive(m)
           
          

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
    \A i, j \in Servers : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

\* The committed entries in every log are a prefix of the
\* leader's log up to the leader's term (since a next Leader may already be
\* elected without the old leader stepping down yet)
LeaderCompletenessInv ==
    \A i \in Servers :
        state[i] = Leader =>
        \A j \in Servers : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])
            
    
\* Committed log entries should never conflict between servers
LogInv ==
    \A i, j \in Servers :
        \/ CheckIsPrefix(Committed(i),Committed(j)) 
        \/ CheckIsPrefix(Committed(j),Committed(i))

\* Note that LogInv checks for safety violations across space
\* This is a key safety invariant and should always be checked
THEOREM Spec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv) 

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
    \E i \in Servers : commitIndex[i] /= 1 \*
    
\*FollowersAppendEntry == \E i,j \in Server : i /= j /\ state[i] = Follower /\ state[j] = Follower /\ Len(log[i]) = 1 /\ Len(log[j]) = 1 \* Verifies that at least one follower appends an entry

FollowersAppendEntry == \A i \in Servers: (state[i] = Follower /\ Len(log[i]) > 0) \/ state[i] /= Follower

ServersAppendEntry == \E i \in Servers: Len(log[i]) = 0 /\ state[i] /= Switch

MessageSent == \A i,j \in DOMAIN messages: 
    \/ Cardinality(DOMAIN messages) < 7 
\*    \/  /\ Cardinality(DOMAIN messages) >= 2
\*        /\ j /= i 
\*        /\  \/ (i.mtype = AppendEntriesResponse /\ messages[i] /= 0) 
\*            \/ (j.mtype = AppendEntriesResponse /\ messages[j] /= 0) 
\*\*            \/ (i.mtype = AppendEntriesRequest /\ j.mtype = AppendEntriesRequest)


AllMessagesNotConsumed == messages = <<>> \/ Cardinality(DOMAIN messages) < 8 \/ \E m \in DOMAIN messages: messages[m] /= 0


\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3, r4
----

\* MV CONSTANT definitions Value
const_1748418873615241000 == 
{v1, v2}
----

\* MV CONSTANT definitions Server
const_1748418873615242000 == 
{r1, r2, r3, r4}
----

\* CONSTANT definitions @modelParameterConstants:3MaxTerm
const_1748418873615243000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:7MaxBecomeLeader
const_1748418873615244000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:14MaxClientRequests
const_1748418873615245000 == 
5
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_17481887456891071000 ==
MyConstraint
----

=============================================================================
\* Created by Ludovic Temgoua Abanda N.


