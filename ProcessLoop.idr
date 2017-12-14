module ProcessLoop

import System.Concurrency.Channels

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data Process : Type -> Type where
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
  Spawn : Process () -> Process (Maybe MessagePID)
  Loop : Inf (Process a) -> Process a
  Action : IO a -> Process a
  Pure : a -> Process a
  (>>=) : Process a -> (a -> Process b) -> Process b

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> Process t -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Request (MkMessage pid) msg) = do
  Just channel <- connect pid
    | _ => pure (Just Nothing)
  ok <- unsafeSend channel msg
  if ok then do Just x <- unsafeRecv Nat channel
                   | _ => pure (Just Nothing)
                pure (Just (Just x))
        else pure (Just Nothing)
run fuel (Respond f) = do
  Just sender <- listen 1
    | _ => pure (Just Nothing)
  Just msg <- unsafeRecv Message sender
    | _ => pure (Just Nothing)
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

partial
runProc : Process () -> IO ()
runProc p = do
  run mr_fusion p
  pure ()
