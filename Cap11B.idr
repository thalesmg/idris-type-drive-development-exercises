module Cap11B

import System
import Data.Primitives.Views

%default total

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : (filepath : String) -> Command (Either FileError String)
  WriteFile : (filepath : String) -> (contents : String) -> Command (Either FileError ())
  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (Pure x) = pure x
runCommand (ReadFile filepath) = readFile filepath
runCommand (WriteFile filepath contents) = writeFile filepath contents
runCommand (Bind x f) = do res <- runCommand x
                           runCommand $ f res

data ConsoleIO : Type -> Type where
  Quit : a -> ConsoleIO a
  Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

namespace CommandDo
  (>>=) : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleDo
  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Input = Answer Int
           | QuitCmd

readInput : String -> Command Input
readInput prompt = do
  PutStr prompt
  answer <- GetLine
  if toLower answer == "quit"
    then Pure QuitCmd
    else Pure (Answer (cast answer))

mutual
  correct : Stream Int -> (score : Nat) -> (totalQs : Nat) -> ConsoleIO (Nat, Nat)
  correct nums score totalQs
    = do PutStr "Correct!\n"
         quiz nums (S score) totalQs

  wrong : Stream Int -> Int -> (score : Nat) -> (totalQs : Nat) -> ConsoleIO (Nat, Nat)
  wrong nums ans score totalQs
    = do PutStr $ "Wrongo! The answer is " ++ show ans ++ ", dumbass!\n"
         quiz nums score totalQs

  quiz : Stream Int -> (score : Nat) -> (totalQs : Nat) -> ConsoleIO (Nat, Nat)
  quiz (num1 :: num2 :: nums) score totalQs
    = do PutStr ("Score so far: " ++ show score ++ " / " ++ show totalQs ++ "\n")
         input <- readInput (show num1 ++ " * " ++ show num2 ++ "? ")
         case input of
           Answer answer => if answer == num1 * num2
                               then correct nums score (S totalQs)
                               else wrong nums (num1 * num2) score (S totalQs)
           QuitCmd => Quit (score, totalQs)

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> ConsoleIO a -> IO (Maybe a)
run Dry p = pure Nothing
run (More fuel) (Quit x) = pure (Just x)
run (More fuel) (Do y f) = do res <- runCommand y
                              run fuel (f res)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
                           (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

namespace Shell
  data Input = Cat String
             | Copy String String
             | NoOp
             | Exit

  readInput : String -> Command Shell.Input
  readInput prompt = do
    PutStr prompt
    input <- GetLine
    case words input of
      ["cat", filepath] => Pure $ Cat filepath
      ["copy", src, dst] => Pure $ Copy src dst
      ["exit"] => Pure Exit
      _ => Pure NoOp

  cat : String -> Command ()
  cat contents = go (words contents)
    where
      go : List String -> Command ()
      go [] = Pure ()
      go (line :: lines) = do PutStr (line ++ "\n")
                              go lines

  shell : String -> ConsoleIO ()
  shell prompt = do
    command <- Shell.readInput prompt
    case command of
      (Cat filename) => do
        Right contents <- ReadFile filename
          | Left fileerror => do
            PutStr ("Error opening file: " ++ show fileerror ++ "\n")
            shell prompt
        cat contents
        shell prompt
      (Copy src dst) => do
        Right contents <- ReadFile src
          | Left fileerror => do
            PutStr ("Error opening source file: " ++ show fileerror ++ "\n")
            shell prompt
        Right () <- WriteFile dst contents
          | Left fileerror => do
            PutStr ("Error writing destination file: " ++ show fileerror ++ "\n")
            shell prompt
        shell prompt
      NoOp => do
        PutStr "DOES NOT COMPUTE.\n"
        shell prompt
      Exit => Quit ()

namespace Main
  partial
  main : IO ()
  main = do seed <- time
            Just (score, totalQs) <- run forever (quiz (arithInputs (fromInteger seed)) 0 0)
              | Nothing => putStrLn "Ran out of fuel"
            putStrLn $ "Final score: " ++ show score ++ " / " ++ show totalQs

namespace Main2
  partial
  main : IO ()
  main = do
    run forever (shell "$hell maroto> ")
    pure ()
