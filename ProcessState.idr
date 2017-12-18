module ProcessState

import System.Concurrency.Channels

%default total

data MessagePID = MkMessage PID
data Message = Add Nat Nat

data ProcState = NoRequest | Sent | Complete

data Process : Type ->
               (in_state : ProcState) ->
               (out_state : ProcState) ->
               Type where
  Request : MessagePID -> Message -> Process Nat st st
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) -> Process (Maybe Message) st Sent
  Spawn : Process () NoRequest Complete -> Process (Maybe MessagePID) st st
  Pure : a -> Process a st st
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete
  Action : IO a -> Process a st st
  (>>=) : Process a st1 st2 -> (a -> Process b st2 st3) -> Process b st1 st3

procAdder : Process () NoRequest Complete
procAdder = do
  Respond (\msg => case msg of
                     Add x y => Pure (x + y))
  Loop procAdder

procAdderBad1 : Process () NoRequest Complete
-- procAdderBad1 = do
--   Action (printLn "I'm out of the office today.")
--   Loop procAdder

procAdderBad2 : Process () NoRequest Complete
-- procAdderBad2 = Loop procAdderBad2

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process t in_state out_state -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Request (MkMessage pid) msg) = do
  Just channel <- connect pid
    | _ => pure Nothing
  ok <- unsafeSend channel msg
  if ok then do Just x <- unsafeRecv Nat channel
                   | _ => pure Nothing
                pure (Just x)
        else pure Nothing
run fuel (Respond f) = do
  Just sender <- listen 1
    | _ => pure Nothing
  Just msg <- unsafeRecv Message sender
    | _ => pure Nothing
  res <- run fuel (f msg)
  unsafeSend sender (Just res)
  pure (Just (Just msg))
run fuel (Spawn p) = do
  Just pid <- spawn (do run fuel p
                        pure ())
    | Nothing => pure Nothing
  pure (Just (Just (MkMessage pid)))
run (More fuel) (Loop p) = do
  res <- run fuel p
  pure res
run fuel (Action act) = do
  res <- act
  pure (Just res)
run fuel (Pure x) = pure (pure x)
run fuel (x >>= f) = do
  Just res <- run fuel x
    | Nothing => pure Nothing
  run fuel (f res)

partial
mr_fusion : Fuel
mr_fusion = More mr_fusion

runProc : Process () in_state out_state -> IO ()
runProc proc = do
  run mr_fusion proc
  pure ()
