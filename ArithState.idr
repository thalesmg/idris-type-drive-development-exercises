module ArithState

import Data.Primitives.Views
import System

%default total

record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

Show GameState where
  show st = show (correct . score $ st) ++ "/" ++
            show (attempted . score $ st) ++ "\n" ++
            "Difficulty: " ++ (show . difficulty $ st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

Functor Command where
  -- map func (PutStr x) = Pure (func ())
  map func (PutStr x) = Bind (PutStr x) (\() => Pure (func ()))
  map func GetLine = Bind GetLine (\x => Pure (func x))
  map func GetRandom = Bind GetRandom (\x => Pure (func x))
  map func GetGameState = Bind GetGameState (\x => Pure (func x))
  -- map func (PutGameState x) = Pure (func ())
  map func (PutGameState x) = Bind (PutGameState x) (\() => Pure (func ()))
  map func (Pure x) = Pure (func x)
  map func (Bind x f) = Bind x (\x => Bind (f x) (\y => Pure (func y)))

Applicative Command where
  pure x = Pure x
  (<*>) (Pure f) y = map f y
  (<*>) (Bind x f) y = Bind x (\res => let new_f = f res
                                       in new_f <*> y)

Monad Command where
  (>>=) x f = Bind x f
  join x = x >>= id
  -- C-c C-c this `x` creates a "Universe inconsistency"!!!!!
  -- join x = ?hole -- becomes...
  -- join (Pure x) = ?bum -- Universe inconsistency!
  -- join (Bind x f) = ?kabum

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

-- namespace CommandDo
--   (>>=) : Command a -> (a -> Command b) -> Command b
--   (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
mr_fusion : Fuel
mr_fusion = More mr_fusion

-- namespace Old
--   runCommand : Command a -> IO a
--   runCommand (PutStr x) = putStr x
--   runCommand GetLine = getLine
--   runCommand GetRandom = ?runCommand_rhs_1
--   runCommand GetGameState = ?runCommand_rhs_2
--   runCommand (PutGameState x) = ?runCommand_rhs_3
--   runCommand (Pure x) = pure x
--   runCommand (Bind c f)
--     = do
--         res <- runCommand c
--         runCommand (f res)
  -- run : Fuel -> ConsoleIO a -> IO (Maybe a)
  -- run Dry _ = pure Nothing
  -- run (More fuel) (Quit x) = pure . Just $ x
  -- run (More fuel) (Do c f) = do
  --   res <- runCommand c
  --   run fuel (f res)

addWrong : GameState -> GameState
addWrong = record { score->attempted $= (+1)}

addCorrect : GameState -> GameState
addCorrect = record { score->attempted $= (+1)
                    , score->correct   $= (+1)}

data Input = Answer Int
           | QuitCmd

mutual
  --||| Ex 1, pg. 350
  updateGameState : (GameState -> GameState) -> Command ()
  updateGameState f = do
    state <- GetGameState
    PutGameState (f state)

  correct : ConsoleIO GameState
  correct = do
    PutStr "Correct!\n"
    -- st <- GetGameState
    -- PutGameState (addCorrect st)
    updateGameState addCorrect
    quiz

  wrong : Int -> ConsoleIO GameState
  wrong x = do
    PutStr $ "Wrongo!!! The answer was " ++ show x ++ "\n"
    -- st <- GetGameState
    -- PutGameState (addWrong st)
    updateGameState addWrong
    quiz

  readInput : String -> Command Input
  readInput prompt = do
    PutStr prompt
    answer <- GetLine
    if toLower answer == "quit"
      then Pure QuitCmd
      else Pure (Answer (cast answer))

  quiz : ConsoleIO GameState
  quiz = do
    num1 <- GetRandom
    num2 <- GetRandom
    st   <- GetGameState
    PutStr (show st ++ "\n")
    input <- readInput (show num1 ++ " * " ++ show num2 ++ " = ? ")
    case input of
      (Answer x) => if x == num1 * num2
                       then correct
                       else wrong (num1 * num2)
      QuitCmd => Quit st

runCommand : Stream Int ->
             GameState ->
             Command a ->
             IO (a, Stream Int, GameState)
runCommand rnds state (PutStr x) = do putStr x
                                      pure ((), rnds, state)
runCommand rnds state GetLine = do str <- getLine
                                   pure (str, rnds, state)
runCommand (val :: rnds) state GetRandom = pure (getRandom val (difficulty state), rnds, state)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand rnds state GetGameState = pure (state, rnds, state)
runCommand rnds state (PutGameState new_state) = pure ((), rnds, new_state)
runCommand rnds state (Pure x) = pure (x, rnds, state)
runCommand rnds state (Bind c f) =
  do
    (res, newRnds, newState) <- runCommand rnds state c
    runCommand newRnds newState (f res)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
(seed' `shiftR` 2) :: randoms seed'

run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run fuel rnds state (Quit val) = pure (Just val, rnds, state)
run Dry rnds state p = pure (Nothing, rnds, state)
run (More fuel) rnds state (Do c f) =
  do
    (res, newRnds, newState) <- runCommand rnds state c
    run fuel newRnds newState (f res)

-- ||| Ex. 2, pg. 350

partial
main : IO ()
main = do
  seed <- time
  (Just score, _, state) <-
    run mr_fusion (randoms (fromInteger seed)) initState quiz
      | _ => putStrLn "Ran out of fuel!"
  putStrLn ("Final score: " ++ show score)
