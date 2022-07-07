-------------------------------- MODULE Fast --------------------------------

EXTENDS Naturals, Bags, FiniteSets, Sequences, TLC, Integers

\* The set of server IDs
CONSTANTS Server, Client

\* The set of requests that can go into the log
CONSTANTS Value

\* Server states.
CONSTANTS Follower, Candidate, Leader, FastPrepare, Merge

\* Cliet states
CONSTANTS Normal, FastLeader

\* A reserved value.
CONSTANTS Nil

\* Message types:
CONSTANTS RequestVoteRequest, RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          PrepareToFastRequest, PrepareToFastResponse,
          FastWriteRequest, FastWriteResponse,
          MergeCollectRequest, MergeCollectResponse,
          MergeRequest, MergeResponse,
          RequestMergeRequest

----
\* Global variables

\* A bag of records representing requests and responses sent from one server
\* to another.
VARIABLE messages

----
\* The following variables are all per server (functions with domain Server).

\* The server's term number.
VARIABLE currentTerm
\* The server's state (Follower, Candidate, or Leader).
VARIABLE state
\* The candidate the server voted for in its current term, or
\* Nil if it hasn't voted for any.
VARIABLE votedFor
serverVars == <<currentTerm, state, votedFor>>


\* The client's state (Normal, FastLeader)
VARIABLE clientState
\* client leader's fast term number.
VARIABLE fastTerm
clientVars == <<clientState, fastTerm>>


\* A Sequence of log entries. The index into this sequence is the index of the
\* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
\* with index 1, so be careful not to use that!
VARIABLE log
\* The index of the latest entry in the log the state machine may apply.
VARIABLE commitIndex
\* The log has been committed
VARIABLE clientAppliedLog
logVars == <<log, commitIndex, clientAppliedLog>>

\* A sequence of log entries in clientLeader.
VARIABLE clientLog
\* variables used for client leader
VARIABLE fIndex
\* used to commit client log
VARIABLE clientLogResponded 

clientLogVars == <<clientLog, fIndex, clientLogResponded>>

VARIABLE votesClientGranted, mergeCollectResponded, mergeSyncResponded
VARIABLE raftLeader

fastVars == <<votesClientGranted, mergeCollectResponded, mergeSyncResponded, raftLeader>>

\* The following variables are used only on candidates:
\* The set of servers from which the candidate has received a RequestVote
\* response in its currentTerm.
VARIABLE votesResponded
\* The set of servers from which the candidate has received a vote in its
\* currentTerm.
VARIABLE votesGranted
candidateVars == <<votesResponded, votesGranted>>

\* The following variables are used only on leaders:
\* The next entry to send to each follower.
VARIABLE nextIndex
\* The latest entry that each follower has acknowledged is the same as the
\* leader's. This is used to calculate commitIndex on the leader.
VARIABLE matchIndex
leaderVars == <<nextIndex, matchIndex>>



\* End of per server variables.
----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) == msgs (+) SetToBag({m})

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) == msgs (-) SetToBag({m})

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

Min(s) == IF s = {} THEN -1 ELSE CHOOSE i \in s : \A j \in s : j \geq i
Max(s) == IF s = {} THEN -1 ELSE CHOOSE i \in s : \A j \in s : i \geq j

\* Define initial values for all variables

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
               /\ clientAppliedLog    = << >>
               /\ commitIndex  = [i \in Server |-> 0]
InitFastVars == 
    /\ votesClientGranted = [i \in Client |-> {}]
    /\ mergeCollectResponded = [i \in Server |-> {}]
    /\ mergeSyncResponded = [i \in Server |-> {}]
    /\ raftLeader = [i \in Client |-> Nil]
InitClientVars ==
    /\ clientState = [i \in Client |-> Normal]
    /\ fastTerm = [i \in Client |-> 1]
InitClientLogVars ==
    /\ fIndex  = [i \in Client |-> 1]
    /\ clientLog = [i \in Client |-> << >>]
    /\ clientLogResponded = [i \in Client |-> << >>]
    
Init == /\ messages = EmptyBag
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars
        /\ InitClientVars
        /\ InitClientLogVars
        /\ InitFastVars
        
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, clientAppliedLog, fastVars, clientVars, clientLogVars>>
\* Server i times out and starts a new election.
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state' = [state EXCEPT ![i] = Leader]
              /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ UNCHANGED <<messages, leaderVars, logVars, clientVars, fastVars,clientLogVars>>

\* Leader i does not get all the clientVoteResponse or client times out

                     
(*************************************)
(* This is the specification of Raft *)
(*************************************)
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
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>


\* Candidate i transitions to leader.
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] =
                         [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] =
                         [j \in Server |-> 0]]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars, clientVars, clientLogVars, fastVars>>


\* Leader i receives a client request to add v to the log.
ClientRequest(i, v) ==
    \/ /\ state[i] = Leader
       /\ LET entry == [term  |-> currentTerm[i],
                        entryType |-> 0,
                        value |-> v]
              newLog == Append(log[i], entry)
          IN  log' = [log EXCEPT ![i] = newLog]
       /\ UNCHANGED <<messages, serverVars, candidateVars,
                   leaderVars, commitIndex, clientAppliedLog, clientVars, clientLogVars, fastVars>>
    \/ /\ state[i] = FastPrepare
       /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
       /\ state' = [state EXCEPT ![i] = Merge]
       /\ mergeCollectResponded' = [mergeCollectResponded EXCEPT ![i] = {}]
       /\ mergeSyncResponded' = [mergeSyncResponded EXCEPT ![i] = {}]
       /\ UNCHANGED <<messages, votedFor, candidateVars, votedFor , raftLeader, 
                   leaderVars, logVars, clientVars, clientLogVars, votesClientGranted>>

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] \in {Leader, FastPrepare}
    /\ Len(log[i]) \geq 1
    /\ LET prevLogIndex == nextIndex[i][j] - 1
           \* The following upper bound on prevLogIndex is unnecessary
           \* but makes verification substantially simpler.
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
           \* Send up to 1 entry, constrained by the end of the log.
           lastEntry == Min({Len(log[i]), nextIndex[i][j]})
           entries == SubSeq(log[i], nextIndex[i][j], lastEntry)
       IN  Send([mtype          |-> AppendEntriesRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mentries       |-> entries,
                mcommitIndex   |-> Min({commitIndex[i], lastEntry}),
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader \/ state[i] = FastPrepare
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
                  \* no log commited
                  0
       IN \/ /\ newCommitIndex > commitIndex[i]
             /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
             /\ UNCHANGED <<clientAppliedLog>>
          \/ newCommitIndex = 0  /\ UNCHANGED << clientAppliedLog, commitIndex>>
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, clientVars, clientLogVars, fastVars>>

\* Message handlers
\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
HandleRequestVoteRequest(i,j,m) == 
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
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>> 



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
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, votedFor, leaderVars, logVars, clientVars, clientLogVars, fastVars>>
    
    
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
             /\ UNCHANGED <<serverVars, logVars, clientVars, clientLogVars>>
          \/ \* return to follower state
             /\ m.mterm = currentTerm[i]
             /\ state[i] \in {Candidate, FastPrepare, Merge}
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
                       /\ Reply([mtype           |-> AppendEntriesResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mmatchIndex     |-> m.mprevLogIndex +
                                                     Len(m.mentries),
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
                       /\ UNCHANGED <<serverVars, log, clientAppliedLog>>
                   \/ \* conflict: remove 1 entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) >= index
                       /\ log[i][index].term /= m.mentries[1].term
                       /\ LET new == [index2 \in 1..(Len(log[i]) - 1) |->
                                          log[i][index2]]
                          IN log' = [log EXCEPT ![i] = new]
                       /\ UNCHANGED <<serverVars, clientAppliedLog, commitIndex, messages>>
                   \/ \* no conflict: append entry
                       /\ m.mentries /= << >>
                       /\ Len(log[i]) = m.mprevLogIndex
                       /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries[1])]
                       /\ UNCHANGED <<serverVars, clientAppliedLog, commitIndex, messages>>
       /\ UNCHANGED <<candidateVars, leaderVars, clientVars, clientLogVars, fastVars>>
       
\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ \lnot m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] =
                               Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED <<matchIndex>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, clientVars, clientLogVars, fastVars>>


(*************************************)
(* This is the specification of Fast *)
(*************************************)

\* Leader i receives a client request to be the leader.
ClientVotesRequest(i) ==
    /\ state[i] = Leader
    /\ state'  = [state  EXCEPT ![i] = FastPrepare]
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars,
                   leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* Leader i sends ClientVotesRequest request to replica j.
\* when the log in all the servers are up to date
prepareToFast(i, j, k) ==
    /\ state[i] = FastPrepare
    /\ clientState[k] = Normal
    /\ i /= j
    /\ matchIndex[i][j] = Len(log[i])
    /\ LET prevLogIndex == matchIndex[i][j]
           \* The following upper bound on prevLogIndex is unnecessary
           \* but makes verification substantially simpler.
           prevLogTerm == IF prevLogIndex > 0 /\ prevLogIndex <= Len(log[i]) THEN
                              log[i][prevLogIndex].term
                          ELSE
                              0
       IN  /\ Send([mtype          |-> PrepareToFastRequest,
                mterm          |-> currentTerm[i],
                mprevLogIndex  |-> prevLogIndex,
                mprevLogTerm   |-> prevLogTerm,
                mclient        |-> k,
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* Server i receives an prepareToFast request from leader j with
\* m.mterm <= currentTerm[i]. 
HandlePrepareToFastRequest(i, j, m) ==
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
             /\ Reply([mtype           |-> PrepareToFastResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mclient         |-> m.mclient,
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
             /\ Reply([mtype           |-> PrepareToFastResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> TRUE,
                       mclient         |-> m.mclient,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<serverVars, logVars>>
       /\ UNCHANGED <<candidateVars, leaderVars, clientVars, clientLogVars, fastVars>>


\* Leader i receives a ClientRequestVote response from server j with
\* m.mterm = currentTerm[i].
HandlePrepareToFastResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ votesClientGranted' = [votesClientGranted EXCEPT ![m.mclient] =
                              votesClientGranted[m.mclient] \cup {j}]
          /\ UNCHANGED << mergeCollectResponded, mergeSyncResponded, serverVars, raftLeader>>
       \/ /\ \lnot m.msuccess \* not successful, just return to raft
          /\ state' = [state EXCEPT ![i] = Merge]
          /\ UNCHANGED <<votesClientGranted, fastVars>>
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, votedFor, leaderVars, candidateVars, logVars, clientVars, clientLogVars, mergeCollectResponded>>


\* Client i transitions to fast leader by leader k
ClientBecomeLeader(i, k) ==
    /\ clientState[i] = Normal
    /\ state[k] = FastPrepare
    /\ Cardinality(votesClientGranted[i]) = Cardinality(Server) - 1
    /\ clientState' = [clientState EXCEPT ![i] = FastLeader]
    /\ fastTerm' = [fastTerm EXCEPT ![i] = currentTerm[k]]
    /\ raftLeader' = [raftLeader EXCEPT ![i] = k]
    /\ UNCHANGED <<messages, serverVars, candidateVars, 
                              clientLogVars, logVars, leaderVars, votesClientGranted, mergeCollectResponded, mergeSyncResponded>>

\* client Leader i issue a request to add v to the log.
ClientLeaderRequest(i, v) ==
    /\ clientState[i] = FastLeader
    /\ Len(clientLog[i]) < 3
    /\ LET entry == [term  |-> fastTerm[i],
                     entryType |-> 1,
                     findex |-> fIndex[i],
                     client |-> i,
                     value |-> v]
           newLog == Append(clientLog[i], entry)
       IN  clientLog' = [clientLog EXCEPT ![i] = newLog]
    /\ clientLogResponded' = [clientLogResponded EXCEPT ![i] = Append(clientLogResponded[i],{})]
    /\ fIndex' = [fIndex EXCEPT ![i] = fIndex[i] + 1]
    \*/\ Send([mtype           |-> RequestMergeRequest,
      \*             mterm           |-> fastTerm[i],
        \*           msource         |-> i,
          \*         mdest           |-> raftLeader[i]])
    /\ UNCHANGED << messages, serverVars, candidateVars,
                   leaderVars, logVars, clientVars, fastVars>>
 

\* Client Leader i sends j an FastWrite request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
FastWrite(i, j) ==
    /\ clientState[i] = FastLeader
    /\ fIndex[i] \geq 2
    /\ LET commit(index) == Cardinality(clientLogResponded[i][index]) = Cardinality(Server)
           conflict(index1) == IF j = 1
                          THEN FALSE
                          ELSE \E x \in 1..(index1 - 1) : /\ clientLog[i][x].value = clientLog[i][index1].value
                                                     /\ \lnot commit(x)
           
       IN  \E k \in 1..(fIndex[i] - 1) : 
                /\ \lnot commit(k) 
                /\ \lnot conflict(k)
                /\ Send([mtype          |-> FastWriteRequest,
                         mterm          |-> fastTerm[i],
                         mfindex        |-> clientLog[i][k].findex,
                         mentries       |-> clientLog[i][k],
                         msource        |-> i,
                         mdest          |-> j])
                \*/\ Print("send fast write done", TRUE)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>


\* Server i receives an FastWrite request from client j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
HandleFastWriteRequest(i, j, m) ==
    LET conflict == IF Len(log[i]) = 0
                    THEN FALSE
                    ELSE \E y \in 1..Len(log[i]) : 
                                     /\ \A commitlog \in 1..Len(clientAppliedLog) : clientAppliedLog[commitlog] /= log[i][y]
                                     /\ log[i][y].entryType = 1
                                     /\ log[i][y].value = m.mentries.value
                                     /\ log[i][y].client /= m.msource
        have == IF Len(log[i]) = 0
                THEN FALSE
                ELSE \E z \in 1..Len(log[i]) : /\ log[i][z] = m.mentries
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ /\ m.mterm < currentTerm[i]
                   /\ UNCHANGED <<serverVars>>
                \/ /\ m.mterm = currentTerm[i]
                   /\ conflict 
                   /\ UNCHANGED <<serverVars>>
                \/ \* return to follower state
                   /\ m.mterm = currentTerm[i]
                   /\ state[i] = Candidate
                   /\ state' = [state EXCEPT ![i] = Follower]
                   /\ UNCHANGED <<currentTerm, votedFor>>
             /\ Reply([mtype           |-> FastWriteResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       mfindex         |-> m.mfindex,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ UNCHANGED <<logVars>>
          
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ \lnot conflict
             /\ Reply([mtype |-> FastWriteResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 mfindex         |-> m.mfindex,
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
             /\ \/ /\ have
                   /\ UNCHANGED <<serverVars, logVars>>
                \/ \* no conflict: append entry
                    /\ m.mentries /= << >>
                    /\ log' = [log EXCEPT ![i] =
                                      Append(log[i], m.mentries)]
                    /\ UNCHANGED <<serverVars, commitIndex, clientAppliedLog>>
       /\ UNCHANGED <<candidateVars, leaderVars, clientVars, clientLogVars, fastVars>>
       
\* Client i receives an FastWrite response from server j with
\* m.mterm = currentTerm[i].
HandleFastWriteResponse(i, j, m) ==
    /\ m.mterm = fastTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ clientLogResponded' = [clientLogResponded EXCEPT ![i][m.mfindex] = clientLogResponded[i][m.mfindex] \cup {j}]
          /\ Discard(m)
          /\ UNCHANGED <<serverVars, clientLog, fIndex, clientVars>>
       \/ /\ \lnot m.msuccess \* not successful
          \* back to raft
          /\ Reply([mtype           |-> RequestMergeRequest,
                   mterm           |-> fastTerm[i],
                   msource         |-> i,
                   mdest           |-> raftLeader[i]],m)
          \*/\ Print("back to raft", TRUE)
          /\ clientState' = [clientState EXCEPT ![i] = Normal]
          /\ UNCHANGED <<serverVars, fastTerm, clientLogVars>>
    /\ UNCHANGED <<candidateVars, logVars, currentTerm, votedFor
                        , fastTerm, leaderVars, fIndex, fastVars>>


\* Client i commit log.
ClientCommitIndex(i) ==
    /\ clientState[i] = FastLeader
    /\ fIndex[i] \geq 2
    /\ \A x \in 1..(fIndex[i] - 1) :
            /\ IF Len(clientAppliedLog) = 0
               THEN TRUE
               ELSE \A applied \in 1..Len(clientAppliedLog) : clientLog[i][x] /= clientAppliedLog[applied]
            /\ Cardinality(clientLogResponded[i][x]) = Cardinality(Server)
            /\ clientAppliedLog' = Append(clientAppliedLog, clientLog[i][x])
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, commitIndex, 
                                                clientVars,clientLogVars, fastVars>>
                                                
\* Server i received msg from client j
HandleRequestMergeRequest(i, j, m) ==
    /\ state[i] = FastPrepare
    /\ currentTerm[i] = m.mterm
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ state' = [state EXCEPT ![i] = Merge]
    /\ mergeCollectResponded' = [mergeCollectResponded EXCEPT ![i] = {}]
    /\ mergeSyncResponded' = [mergeCollectResponded EXCEPT ![i] = {}]
    /\ Discard(m)
    /\ UNCHANGED << votedFor, clientVars, logVars, clientLogVars, raftLeader, votesClientGranted, candidateVars, leaderVars>>
    
\* Leader i merges the fast log and send merge collect msg to server
MergeFastLog(i, j) ==
    /\ state[i] = Merge
    /\ Send([mtype          |-> MergeCollectRequest,
             mterm          |-> currentTerm[i],
             msource        |-> i,
             mdest          |-> j])
    \*/\ Print("merge fast log", TRUE)
    /\ UNCHANGED <<serverVars, clientVars, logVars, clientLogVars, fastVars, candidateVars, leaderVars>>                    

\* Server i received a merge collect msg from Leader j
HandleMergeCollectRequest(i, j, m) ==
    /\ state[j] = Merge
    /\ currentTerm[i] <= currentTerm[j]
    /\ LET entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))  
       IN Reply([mtype          |-> MergeCollectResponse,
                mterm          |-> currentTerm[i],
                mentries       |-> entries,
                mnums          |-> Len(log[i]),
                msource        |-> i,
                mdest          |-> j],
                m)
    /\ UNCHANGED <<serverVars, clientVars, logVars, clientLogVars, fastVars, candidateVars, leaderVars>> 

\* Leader i handle merge collect msg from server j.
HandleMergeCollectResponse(i, j, m) == 
    /\ state[i] = Merge
    \* responsed
    /\ IF Len(log[i]) < m.mnums
       THEN LET s == Append(SubSeq(log[i],nextIndex[i][j],Len(log[i])) , m.mentries)
            IN log' = [log EXCEPT ![i] = s]
       ELSE UNCHANGED <<log>>
    /\ mergeCollectResponded' = [mergeCollectResponded EXCEPT ![i] = mergeCollectResponded[i] \cup {j}]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, clientVars, commitIndex, clientAppliedLog, raftLeader,
                            clientLogVars, votesClientGranted, mergeSyncResponded,candidateVars, leaderVars>> 
    
\* Leader i send merge sync msg to server j.
MergeSync(i, j) ==     
    /\ state[i] = Merge
    /\ Cardinality(mergeCollectResponded[i]) \geq Cardinality(Server) - 1
    /\ Print("Merge sync",TRUE)
    /\ LET entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))  
       IN Send([mtype          |-> MergeRequest,
                mterm          |-> currentTerm[i],
                mentries       |-> entries,
                msource        |-> i,
                mdest          |-> j])
    /\ UNCHANGED <<votesClientGranted, serverVars, clientVars, logVars, clientLogVars, fastVars, candidateVars, leaderVars>> 

\* Server i received merge sync from leader j.
HandleMergeSyncRequest(i, j, m)==
    /\ m.mterm <= currentTerm[i]
       /\ \/ /\ \* reject request
                \/ m.mterm < currentTerm[i]
                \/ \* return to follower state
                   /\ m.mterm = currentTerm[i]
                   /\ state[i] = Candidate
                   /\ state' = [state EXCEPT ![i] = Follower]
             /\ Reply([mtype           |-> MergeResponse,
                       mterm           |-> currentTerm[i],
                       msuccess        |-> FALSE,
                       msource         |-> i,
                       mdest           |-> j],
                       m)
             /\ Print("reject merge sync", TRUE)
             /\ Print(m.mterm - currentTerm[i],TRUE)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* accept request
             /\ m.mterm = currentTerm[i]
             /\ Reply([mtype |-> MergeResponse,
                                 mterm           |-> currentTerm[i],
                                 msuccess        |-> TRUE,
                                 msource         |-> i,
                                 mdest           |-> j],
                                 m)
              /\ log' = [log EXCEPT ![i] = Append(SubSeq(log[i],nextIndex[j][i],Len(log[i])) , m.mentries)] 
              /\ Print("accept merge request", TRUE)
              /\ UNCHANGED <<serverVars, commitIndex, clientAppliedLog>>
       /\ UNCHANGED <<candidateVars, leaderVars, clientVars, clientLogVars, fastVars>>

\* Leader i handle merge sync msg from server j.
HandleMergeSyncResponse(i, j, m) ==
    /\ state[i] = Merge
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ mergeSyncResponded' = [mergeSyncResponded EXCEPT ![i] = mergeSyncResponded[i] \cup {j}]
          /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = Len(log[i]) + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = Len(log[i])]
          /\ Print("handle merge sync success",TRUE)
          /\ UNCHANGED <<votesClientGranted, raftLeader, mergeCollectResponded>>
       \/ /\ \lnot m.msuccess \* not successful
          /\ Print("merge sync fail", TRUE)
          /\ MergeSync(i, j)
          /\ UNCHANGED <<leaderVars, fastVars>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, clientVars, clientLogVars>>
    
\* Leader i Merge stage done.
MergeDone(i) ==
    /\ state[i] = Merge
    /\ Cardinality(mergeSyncResponded[i]) \geq Cardinality(Server) - 1
    /\ Print("merge done", TRUE)
    /\ state' = [state EXCEPT ![i] = Leader]
    /\ votesClientGranted' = [k \in Client |-> {}]
    /\ mergeCollectResponded' = [c \in Server |-> {}]
    /\ mergeSyncResponded' = [c \in Server |-> {}]
    /\ matchIndex' = [matchIndex EXCEPT ![i][i] = Len(log[i])]
    /\ nextIndex' = [nextIndex EXCEPT ![i][i] = Len(log[i]) + 1]
    /\ UNCHANGED <<messages, raftLeader, currentTerm, votedFor, clientVars, logVars, clientLogVars, candidateVars>> 



\* Any RPC with a newer term causes the recipient to advance its term first.
UpdateTerm(i, j, m) ==
    /\ i \notin Client
    /\ m.mterm > currentTerm[i]
    /\ currentTerm'    = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'          = [state       EXCEPT ![i] = Follower]
    /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* Responses with stale terms are ignored.
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

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
       \/ /\ m.mtype = PrepareToFastRequest
          /\ HandlePrepareToFastRequest(i, j, m)
       \/ /\ m.mtype = PrepareToFastResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandlePrepareToFastResponse(i, j, m)
       \/ /\ m.mtype = FastWriteRequest
          /\ HandleFastWriteRequest(i, j, m)
       \/ /\ m.mtype = FastWriteResponse
          /\ HandleFastWriteResponse(i, j, m)   
       \/ /\ m.mtype = MergeCollectRequest
          /\ HandleMergeCollectRequest(i, j, m)
       \/ /\ m.mtype = MergeCollectResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleMergeCollectResponse(i, j, m) 
       \/ /\ m.mtype = MergeRequest
          /\ HandleMergeSyncRequest(i, j, m)
       \/ /\ m.mtype = MergeResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleMergeSyncResponse(i, j, m)    
       \/ /\ m.mtype = RequestMergeRequest
          /\ \/ DropStaleResponse(i, j, m)
             \/ /\ HandleRequestMergeRequest(i, j, m)
          
\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars, clientVars, clientLogVars, fastVars>>

----
\* Defines how the variables may transition.
Next == \/ \E i \in Server : Restart(i)
        \/ \E m \in DOMAIN messages :  Receive(m)
        \/ \E i \in Server : IF \A j \in Server : state[j] \in {Follower, Candidate} 
                             THEN Timeout(i)
                             ELSE FALSE
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server, v \in Value : ClientRequest(i, v)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i \in Client, j \in Server : FastWrite(i, j)
        \/ \E i \in Client : ClientCommitIndex(i)
        \/ \E i,j \in Server : MergeFastLog(i,j)
        \/ \E i,j \in Server : MergeSync(i, j)
        \/ \E i \in Server : MergeDone(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ \E i \in Server : ClientVotesRequest(i)
        \/ \E i,j \in Server, k \in Client : prepareToFast(i, j, k)
        \/ \E i \in Client, k \in Server : ClientBecomeLeader(i, k)
        \/ \E i \in Client, v \in Value : ClientLeaderRequest(i, v)
        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
        \/ \E m \in DOMAIN messages : DropMessage(m)

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars


\* check log 
\* if log i is committed, then quorum server have this log
checkLogConsistent == /\ LET maxindex == Max({commitIndex[s] : s \in Server})
                          cs == CHOOSE x \in Server : Len(log[x]) \geq maxindex
                       IN   IF maxindex = 0  
                         THEN TRUE
                         ELSE \A l \in 1..maxindex: 
                             IF log[cs][l].entryType = 0 \*raft msg
                             THEN LET  Agree == {} \cup {k \in Server :
                                        Len(log[k]) \geq maxindex /\ log[cs][l].value = log[k][l].value}
                                  IN Agree \in Quorum
                             
                             ELSE TRUE
                     /\ IF Len(clientAppliedLog) = 0
                        THEN TRUE  
                        ELSE \A flogindex \in 1..Len(clientAppliedLog) :
                            \A fserver \in Server : \E fserverindex \in 1..Len(log[fserver]) :
                                        clientAppliedLog[flogindex] = log[fserver][fserverindex]
\* if log i is committed before log j and i is conflict with j,
\* then log i is applied before log j in every server.
checkLogDependency == IF Len(clientAppliedLog) < 2
                      THEN TRUE
                      ELSE \A i,j \in 1..Len(clientAppliedLog) : 
                            IF   /\ i > j 
                                 /\ clientAppliedLog[i].value = clientAppliedLog[j].value 
                            THEN \E q \in Quorum : (\A k \in q : 
                            (CHOOSE x \in 1..Len(log[k]) : log[k][x] =  clientAppliedLog[i])
                             > (CHOOSE y \in 1..Len(log[k]) : log[k][y] =  clientAppliedLog[j]))
                            ELSE TRUE
                                                            




=============================================================================

