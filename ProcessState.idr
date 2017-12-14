module ProcessState

import System.Concurrency.Channels

data MessagePID = MkMessage PID
data Message = Add Nat Nat

data ProcState = NoRequest | Sent | Complete

data Process : Type ->
               (in_state : ProcState) ->
               (out_state : ProcState) ->
               Type where
  Request : MessagePID -> Message -> Process Nat st st
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) -> Process (Maybe Nat) st Sent
  Spawn : Process () NoRequest Complete -> Process (Maybe MessagePID) st st
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete
  Action : IO a -> Process a st st
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) -> Process b st1 st3

procAdder : Process () NoRequest Complete
procAdder = do
  Respond (\msg => case msg of
                     Add x y => Pure (x + y))
  Loop procAdder
