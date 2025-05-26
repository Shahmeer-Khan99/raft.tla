--------------------------------- MODULE raftModelPerf_ShahmeerSHAKIR_0241514719 ---------------------------------
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Server node identifiers in the Raft cluster
CONSTANTS Server

\* Possible values for client requests in the log
CONSTANTS Value

\* Possible server states in the protocol
CONSTANTS Follower, Candidate, Leader, Switch

\* Special constant representing empty/nil value
CONSTANTS Nil

\* RPC message types for protocol communication
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse

\* Model parameter: Maximum client requests to process
CONSTANTS MaxClientRequests

\* Model parameter: Maximum leadership terms per server
CONSTANTS MaxBecomeLeader

\* Model parameter: Upper bound for term numbers
CONSTANTS MaxTerm

\* Network messages currently in transit between servers
VARIABLE messages

\* Count of leadership terms for each server
VARIABLE leaderCount

\* Current maximum client requests processed
VARIABLE maxClient

\* Statistics tracking for log entry commitment
VARIABLE entryCommitStats

\* Grouped instrumentation variables
instrumentationVars == <<leaderCount, maxClient, entryCommitStats>>

\* Core Raft server state variables
VARIABLE currentTerm  \* Current election term
VARIABLE state       \* Server's current role
VARIABLE votedFor    \* Candidate voted for in current term
serverVars == <<currentTerm, state, votedFor>>

\* Log replication variables
VARIABLE log          \* Sequence of log entries
VARIABLE commitIndex  \* Index of highest committed entry
logVars == <<log, commitIndex>>

\* Election-specific variables
VARIABLE votesResponded  \* Servers that responded to votes
VARIABLE votesGranted    \* Servers that granted votes
VARIABLE voterLog        \* Logs of voting servers
candidateVars == <<votesResponded, votesGranted, voterLog>>

\* Leader-specific replication tracking
VARIABLE nextIndex   \* Next log entry to send
VARIABLE matchIndex  \* Highest replicated entry
leaderVars == <<nextIndex, matchIndex>>

\* Complete set of protocol variables
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

\* Index of the current switch node
VARIABLE switchIndex

\* Buffer for client requests
VARIABLE requestBuffer

\* Per-server pending requests
VARIABLE unprocessedRequests

\* Tracks delivered (value,term) pairs
VARIABLE deliveryTracker

\* HovercRaft switch variables
switchVars == <<requestBuffer, unprocessedRequests, switchIndex, deliveryTracker>>

\* Complete system state
systemState == <<vars, switchVars>>

\* Definition of a quorum (majority)
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* Returns term of last log entry (0 if empty)
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper: Adds message to network
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN msgs
    ELSE msgs @@ (m :> 1)

\* Helper: Removes message from network
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0 ]
    ELSE msgs

\* Action: Send message
Send(m) == messages' = WithMessage(m, messages)

\* Action: Remove message
Discard(m) == messages' = WithoutMessage(m, messages)

\* Action: Atomic reply
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* Math helpers
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
Max(s) == CHOOSE x \in s : \A y \in s : x >= y
min(a, b) == IF a < b THEN a ELSE b

\* Valid messages in network
ValidMessage(msgs) == { m \in DOMAIN messages : msgs[m] > 0 }

\* Committed log prefix up to term x
CommittedTermPrefix(i, x) ==
    IF Len(log[i]) /= 0 /\ \E y \in DOMAIN log[i] : log[i][y].term <= x
    THEN LET maxTermIndex == CHOOSE y \in DOMAIN log[i] :
            /\ log[i][y].term <= x
            /\ \A z \in DOMAIN log[i] : log[i][z].term <= x => y >= z
         IN SubSeq(log[i], 1, min(maxTermIndex, commitIndex[i]))
    ELSE << >>

\* Checks if seq1 is prefix of seq2
CheckIsPrefix(seq1, seq2) ==
    /\ Len(seq1) <= Len(seq2)
    /\ \A i \in 1..Len(seq1) : seq1[i] = seq2[i]

\* Returns committed portion of log
Committed(i) ==
    IF commitIndex[i] = 0 THEN << >> ELSE SubSeq(log[i],1,commitIndex[i])

MyConstraint == (\A i \in Server: currentTerm[i] <= MaxTerm /\ Len(log[i]) <= MaxClientRequests) 
                /\ (\A m \in DOMAIN messages: messages[m] <= 1)

Symmetry == Permutations(Server)

InitHistoryVars == voterLog = [i \in Server |-> [j \in {} |-> <<>>]]
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state = [i \in Server |-> Follower]
                  /\ votedFor = [i \in Server |-> Nil]
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted = [i \in Server |-> {}]
InitLeaderVars == /\ nextIndex = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]
InitLogVars == /\ log = [i \in Server |-> << >>]
               /\ commitIndex = [i \in Server |-> 0]
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ maxClient = 0
        /\ leaderCount = [i \in Server |-> 0]
        /\ entryCommitStats = [idx_term \in {} |-> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE]]

MyInit ==
    LET ServerIds == CHOOSE ids \in {seq \in [1..4 -> Server] :
        /\ seq[1] # seq[2]
        /\ seq[1] # seq[3]
        /\ seq[1] # seq[4]
        /\ seq[2] # seq[3]
        /\ seq[2] # seq[4]
        /\ seq[3] # seq[4]
     }: TRUE
        r1 == ServerIds[1]
        r2 == ServerIds[2]
        r3 == ServerIds[3]
        r4 == ServerIds[4]
    IN
    /\ commitIndex = [s \in Server |-> 0]
    /\ currentTerm = [s \in Server |-> 2]
    /\ leaderCount = [s \in Server |-> IF s = r2 THEN 1 ELSE 0]
    /\ switchIndex = r1
    /\ log = [s \in Server |-> <<>>]
    /\ matchIndex = [s \in Server |-> [t \in Server |-> 0]]
    /\ maxClient = 0
    /\ messages = [m \in {} |-> 0]
    /\ nextIndex = [s \in Server |-> [t \in Server |-> 1]]
    /\ state = [s \in Server |-> IF s = r2 THEN Leader ELSE (IF s = r1 THEN Switch ELSE Follower)]
    /\ requestBuffer = [x \in {} |-> [term |-> 0, value |-> "", payload |-> ""]]
    /\ deliveryTracker = [s \in Server |-> {}]
    /\ unprocessedRequests = [s \in Server |-> {}]
    /\ votedFor = [s \in Server |-> IF s = r2 THEN Nil ELSE r2]
    /\ voterLog = [s \in Server |-> IF s = r2 THEN (r1 :> <<>> @@ r3 :> <<>>) ELSE <<>>]
    /\ votesGranted = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ votesResponded = [s \in Server |-> IF s = r2 THEN {r1, r3} ELSE {}]
    /\ entryCommitStats = [idx_term \in {} |-> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE]]

Restart(i) ==
    /\ state[i] = Leader
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex' = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, instrumentationVars>>

Timeout(i) ==
    /\ state[i] \in {Follower}
    /\ currentTerm[i] < MaxTerm
    /\ state' = [state EXCEPT ![i] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog' = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ UNCHANGED <<messages, leaderVars, logVars, instrumentationVars>>

BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ leaderCount[i] < MaxBecomeLeader
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ leaderCount' = [leaderCount EXCEPT ![i] = leaderCount[i] + 1]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, maxClient, entryCommitStats>>

UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ m.mterm < MaxTerm
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state' = [state EXCEPT ![i] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ Send([mtype |-> RequestVoteRequest,
             mterm |-> currentTerm[i],
             mlastLogTerm |-> LastTerm(log[i]),
             mlastLogIndex |-> Len(log[i]),
             msource |-> i,
             mdest |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

HandleRequestVoteRequest(i, j, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[i])
                 \/ /\ m.mlastLogTerm = LastTerm(log[i])
                    /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 /\ votedFor[i] \in {Nil, j}
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
          \/ ~grant /\ UNCHANGED votedFor
       /\ Reply([mtype |-> RequestVoteResponse,
                 mterm |-> currentTerm[i],
                 mvoteGranted |-> grant,
                 mlog |-> log[i],
                 msource |-> i,
                 mdest |-> j], m)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

HandleRequestVoteResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] = voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog, switchVars>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, instrumentationVars, switchVars>>

DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars, switchVars>>

ClientRequest(i,v) ==
    /\ state[i] = Leader
    /\ maxClient < MaxClientRequests 
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxClient' = IF entryExists THEN maxClient ELSE maxClient + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0
              THEN entryCommitStats @@ (newEntryKey :> [sentCount |-> 0, ackCount |-> 0, committed |-> FALSE])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount>>

SwitchClientRequestReplicate(i, v) ==
    /\ ~(<<v, requestBuffer[v].term>> \in deliveryTracker[i])
    /\ deliveryTracker' = [deliveryTracker EXCEPT ![i] = deliveryTracker[i] \cup {<<v, requestBuffer[v].term>>}]
    /\ unprocessedRequests' = [unprocessedRequests EXCEPT ![i] = unprocessedRequests[i] \cup {v}]
    /\ UNCHANGED <<vars, requestBuffer, switchIndex>>

LeaderIngestHovercRaftRequest(i, v) ==
    /\ maxClient < MaxClientRequests
    /\ v \in DOMAIN requestBuffer
    /\ <<v, requestBuffer[v].term>> \in deliveryTracker[i]
    /\ LET entryTerm == currentTerm[i]
           entry == [term |-> entryTerm, value |-> v, payload |-> requestBuffer[v].payload]
           entryExists == \E j \in DOMAIN log[i] : log[i][j].value = v /\ log[i][j].term = entryTerm
           newLog == IF entryExists THEN log[i] ELSE Append(log[i], entry)
           newEntryIndex == Len(log[i]) + 1
           newEntryKey == <<newEntryIndex, entryTerm>>
       IN
        /\ log' = [log EXCEPT ![i] = newLog]
        /\ maxClient' = IF entryExists THEN maxClient ELSE maxClient + 1
        /\ entryCommitStats' =
              IF ~entryExists /\ newEntryIndex > 0
              THEN entryCommitStats @@ (newEntryKey :> [sentCount |-> 0, ackCount |-> 1, committed |-> FALSE])
              ELSE entryCommitStats
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex, leaderCount, switchVars>>

SwitchClientRequest(i, v) ==
    /\ state[i] = Leader
    /\ ~(v \in DOMAIN requestBuffer)
    /\ requestBuffer' = requestBuffer @@ (v :> [term |-> currentTerm[switchIndex],
                                           value |-> v,
                                           payload |-> v])
    /\ unprocessedRequests' = [unprocessedRequests EXCEPT ![switchIndex] = unprocessedRequests[switchIndex] \cup {v}]
    /\ UNCHANGED <<vars, switchIndex, deliveryTracker>>

AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ Len(log[i]) > 0
    /\ nextIndex[i][j] <= Len(log[i])
    /\ matchIndex[i][j] < nextIndex[i][j]
    /\ LET entryIndex == nextIndex[i][j]
           entry == log[i][entryIndex]
           entries == <<[term |-> entry.term, value |-> entry.value]>>
           entryKey == <<entryIndex, entry.term>>
           prevLogIndex == entryIndex - 1
           prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
       IN Send([mtype |-> AppendEntriesRequest,
                mterm |-> currentTerm[i],
                mprevLogIndex |-> prevLogIndex,
                mprevLogTerm |-> prevLogTerm,
                mentries |-> entries,
                mlog |-> log[i],
                mcommitIndex |-> Min({commitIndex[i], entryIndex}),
                msource |-> i,
                mdest |-> j])
       /\ entryCommitStats' =
            IF entryKey \in DOMAIN entryCommitStats /\ ~entryCommitStats[entryKey].committed
            THEN [entryCommitStats EXCEPT ![entryKey].sentCount = @ + 1]
            ELSE entryCommitStats         
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, maxClient, leaderCount, switchVars>>

HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm = currentTerm[i]
                   /\ state[i] = Follower
                   /\ \lnot logOk
             /\ Reply([mtype |-> AppendEntriesResponse,
                       mterm |-> currentTerm[i],
                       msuccess |-> FALSE,
                       mmatchIndex |-> 0,
                       msource |-> i,
                       mdest |-> j], m)
             /\ UNCHANGED <<serverVars, logVars, switchVars>>
          \/ /\ m.mterm = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages, switchVars>>
          \/ /\ m.mterm = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ /\ \/ m.mentries = << >>
                      \/ /\ m.mentries /= << >>
                         /\ Len(log[i]) >= index
                         /\ log[i][index].term = m.mentries[1].term
                   /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]   
                   /\ LET entry == m.mentries[1]
                         v == entry.value
                      IN /\ entry.value \in unprocessedRequests[i]
                         /\ unprocessedRequests' = [unprocessedRequests EXCEPT ![i] = unprocessedRequests[i] \ {v}]
                   /\ Reply([mtype |-> AppendEntriesResponse,
                             mterm |-> currentTerm[i],
                             msuccess |-> TRUE,
                             mmatchIndex |-> m.mprevLogIndex + Len(m.mentries),
                             msource |-> i,
                             mdest |-> j], m)
                   /\ UNCHANGED <<serverVars, log, switchIndex, requestBuffer, deliveryTracker>>
                \/ /\ m.mentries /= << >>
                   /\ Len(log[i]) >= index
                   /\ log[i][index].term /= m.mentries[1].term
                   /\ LET newLog == SubSeq(log[i], 1, index - 1)
                      IN log' = [log EXCEPT ![i] = newLog]
                   /\ UNCHANGED <<serverVars, commitIndex, messages, switchVars>>
                \/ /\ m.mentries /= << >>
                   /\ Len(log[i]) = m.mprevLogIndex
                   /\ log' = [log EXCEPT ![i] = Append(log[i], [term |-> m.mentries[1].term, value |-> m.mentries[1].value, payload |-> requestBuffer[m.mentries[1].value].payload])]
                   /\ UNCHANGED <<serverVars, commitIndex, messages, switchVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, instrumentationVars, switchIndex, requestBuffer, deliveryTracker>>

HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess
          /\ LET newMatchIndex == m.mmatchIndex
                 entryKey == IF newMatchIndex > 0 /\ newMatchIndex <= Len(log[i])
                              THEN <<newMatchIndex, log[i][newMatchIndex].term>>
                              ELSE <<0, 0>>
             IN /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                /\ entryCommitStats' =
                     IF /\ entryKey /= <<0, 0>>
                        /\ entryKey \in DOMAIN entryCommitStats
                        /\ ~entryCommitStats[entryKey].committed
                     THEN [entryCommitStats EXCEPT ![entryKey].ackCount = @ + 1]
                     ELSE entryCommitStats                     
       \/ /\ \lnot m.msuccess
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex, entryCommitStats, switchVars>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, maxClient, leaderCount, switchVars>>

AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET Agree(index) == {i} \cup {k \in Server : matchIndex[i][k] >= index}
           agreeIndexes == {index \in 1..Len(log[i]) : Agree(index) \in Quorum}
           newCommitIndex ==
              IF /\ agreeIndexes /= {}
                 /\ log[i][Max(agreeIndexes)].term = currentTerm[i]
              THEN Max(agreeIndexes)
              ELSE commitIndex[i]
           committedIndexes == {k \in Nat : /\ k > commitIndex[i]
                                           /\ k <= newCommitIndex}
           keysToUpdate == {key \in DOMAIN entryCommitStats : key[1] \in committedIndexes}           
       IN /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
          /\ entryCommitStats' =
               [key \in DOMAIN entryCommitStats |->
                   IF key \in keysToUpdate
                   THEN [entryCommitStats[key] EXCEPT !.committed = TRUE]
                   ELSE entryCommitStats[key]]                             
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, maxClient, leaderCount, switchVars>>

DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, instrumentationVars>>

Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \/ UpdateTerm(i, j, m)
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

Next == 
    \/ \E i \in Server : Timeout(i)
    \/ \E i,j \in Server : i /= j /\ RequestVote(i, j)
    \/ \E i \in Server : BecomeLeader(i)
    \/ \E i \in Server, v \in Value : state[i] = Leader /\ ClientRequest(i, v)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
    \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype \in {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)

MyNext == 
    \/ \E i \in Server, v \in Value : state[i] = Leader /\ ClientRequest(i, v)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
    \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)

MySwitchNext == 
    \/ \E i \in Server, v \in Value : state[i] = Leader /\ SwitchClientRequest(i, v)
    \/ \E i \in Server, v \in DOMAIN requestBuffer : state[i] /= Switch /\ SwitchClientRequestReplicate(i, v)
    \/ \E i \in Server, v \in DOMAIN requestBuffer : state[i] = Leader /\ LeaderIngestHovercRaftRequest(i, v)
    \/ \E i \in Server : AdvanceCommitIndex(i)
    \/ \E i,j \in Server : i /= j /\ AppendEntries(i, j)
    \/ \E m \in {msg \in ValidMessage(messages) : msg.mtype \in {AppendEntriesRequest, AppendEntriesResponse}} : Receive(m)

MySwitchSpec == MyInit /\ [][MySwitchNext]_systemState

MoreThanOneLeaderInv ==
    \A i,j \in Server :
        (/\ currentTerm[i] = currentTerm[j]
         /\ state[i] = Leader
         /\ state[j] = Leader)
        => i = j

LogMatchingInv ==
    \A i, j \in Server : i /= j =>
        \A n \in 1..min(Len(log[i]), Len(log[j])) :
            log[i][n].term = log[j][n].term =>
            SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

LeaderCompletenessInv ==
    \A i \in Server :
        state[i] = Leader =>
        \A j \in Server : i /= j =>
            CheckIsPrefix(CommittedTermPrefix(j, currentTerm[i]),log[i])
            
LogInv ==
    \A i, j \in Server :
        \/ CheckIsPrefix(Committed(i),Committed(j)) 
        \/ CheckIsPrefix(Committed(j),Committed(i))

THEOREM MySwitchSpec => ([]LogInv /\ []LeaderCompletenessInv /\ []LogMatchingInv /\ []MoreThanOneLeaderInv) 

MaxCInv == (\E i \in Server : state[i] = Leader) => maxClient <= MaxClientRequests

LeaderCountInv == \E i \in Server : (state[i] = Leader => leaderCount[i] <= MaxBecomeLeader)

MaxTermInv == \A i \in Server : currentTerm[i] <= MaxTerm

EntryCommitMessageCountInv ==
    LET NumFollowers == Cardinality(Server) - 1
        MinFollowersForMajority == Cardinality(Server) \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN IF stats.committed
           THEN (stats.sentCount >= MinFollowersForMajority /\ stats.sentCount <= NumFollowers) 
                \/ (stats.ackCount >= MinFollowersForMajority /\ stats.ackCount <= NumFollowers)
           ELSE TRUE

EntryCommitAckQuorumInv ==
    LET NumServers == Cardinality(Server)
        MinFollowerAcksForMajority == NumServers \div 2
    IN \A key \in DOMAIN entryCommitStats :
        LET stats == entryCommitStats[key]
        IN stats.committed => (stats.ackCount >= MinFollowerAcksForMajority)

LeaderCommitted ==
    \E i \in (Server \ {switchIndex}) : commitIndex[i] /= 1

AllServersHaveOneUnorderedRequestInv ==
    \E s \in Server : Cardinality(unprocessedRequests[s]) /= 2

===============================================================================
