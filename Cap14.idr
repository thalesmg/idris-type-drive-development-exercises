module Cap14

import Data.Vect

%default total

namespace ATM
  PIN : Type
  PIN = Vect 4 Char

  data ATMState = Ready | CardInserted | Session

  data PINCheck = CorrectPIN | IncorrectPIN

  data HasCard : ATMState -> Type where
    HasCI : HasCard CardInserted
    HasSession : HasCard Session

  data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
    InsertCard : ATMCmd () Ready (const CardInserted)
    EjectCard : {auto prf : HasCard state} -> ATMCmd () state (const Ready)
    GetPIN : ATMCmd PIN CardInserted (const CardInserted)

    CheckPIN : PIN -> ATMCmd PINCheck CardInserted
                             (\check => (case check of
                                              CorrectPIN => Session
                                              IncorrectPIN => CardInserted))
    GetAmount : ATMCmd Nat state (const state)
    Dispense : (amount : Nat) -> ATMCmd () Session (const Session)
    Message : String -> ATMCmd () state (const state)
    Pure : ty -> ATMCmd ty state (const state)
    (>>=) : ATMCmd a state1 state2_fn ->
            ((res : a) -> ATMCmd b (state2_fn res) state3_fn) ->
            ATMCmd b state1 state3_fn

  atm : ATMCmd () Ready (const Ready)
  atm = do
    InsertCard
    pin <- GetPIN
    pinOK <- CheckPIN pin
    case pinOK of
         CorrectPIN => do
           amount <- GetAmount
           Dispense amount
           EjectCard
         IncorrectPIN => do
           Message "Incorrect PIN!\n"
           EjectCard

  testPIN : PIN
  testPIN = ['1', '2', '3', '4']

  readVect : (n : Nat) -> IO (Vect n Char)
  readVect Z = do
    getLine
    pure []
  readVect (S k) = do
    ch <- getChar
    chs <- readVect k
    pure (ch :: chs)

  runATM : ATMCmd res inState outState_fn -> IO res
  runATM InsertCard = do
    putStrLn "Please insert your card (press Enter)"
    getLine
    pure ()
  runATM EjectCard = putStrLn "Card ejected. Bye!"
  runATM GetPIN = do
    putStr "Enter PIN: "
    readVect 4
  runATM (CheckPIN pin) =
    if pin == testPIN
      then pure CorrectPIN
      else pure IncorrectPIN
  runATM GetAmount = do
    putStr "Enter the amount you wish to withdraw: "
    amount <- getLine
    pure (cast amount)
  runATM (Dispense amount) = putStrLn ("Here is " ++ show amount)
  runATM (Message msg) = putStrLn msg
  runATM (Pure x) = pure x
  runATM (x >>= f) = do
    x' <- runATM x
    runATM (f x')

  insertEject : ATMCmd () Ready (const Ready)
  insertEject = do
    InsertCard
    EjectCard

  badATM : ATMCmd () Ready (const Ready)
  -- badATM = EjectCard

-- Ex. 1, pg. 389
namespace Ex1
  data Access = LoggedOut | LoggedIn
  data PwdCheck = Correct | Incorrect

  data ShellCmd : (ty : Type) -> Access -> (ty -> Access) -> Type where
    Password : String -> ShellCmd PwdCheck LoggedOut
                                           (\res => case res of
                                                         Correct => LoggedIn
                                                         Incorrect => LoggedOut)
    Logout : ShellCmd () LoggedIn (const LoggedOut)
    GetSecret : ShellCmd String LoggedIn (const LoggedIn)

    PutStr : String -> ShellCmd () state (const state)
    Pure : (res : ty) -> ShellCmd ty (state_fn res) state_fn
    (>>=) : ShellCmd a state1 state2_fn ->
            ((res : a) -> ShellCmd b (state2_fn res) state3_fn) ->
            ShellCmd b state1 state3_fn

  session : ShellCmd () LoggedOut (const LoggedOut)
  session = do
    Correct <- Password "wurzel"
      | Incorrect => PutStr "Wrong password\n"
    msg <- GetSecret
    PutStr ("Secret code: " ++ msg ++ "\n")
    Logout

  sessionBad : ShellCmd () LoggedOut (const LoggedOut)
  -- sessionBad = do
  --   Password "wurzel"
  --   msg <- GetSecret
  --   PutStr ("Secret code: " ++ msg ++ "\n")
  --   Logout

  noLogout : ShellCmd () LoggedOut (const LoggedOut)
  -- noLogout = do
  --   Correct <- Password "wurzel"
  --     | Incorrect => PutStr "Wrong password\n"
  --   msg <- GetSecret
  --   PutStr ("Secret code: " ++ msg ++ "\n")

-- Ex. 2, pg. 390
namespace Ex2
  VendState : Type
  VendState = (Nat, Nat)

  data CoinResult = Inserted | Rejected

  data Input = COIN
             | VEND
             | CHANGE
             | REFILL Nat

  data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
    InsertCoin : MachineCmd CoinResult (pounds, chocs)
                               (\res => case res of
                                             Inserted => (S pounds, chocs)
                                             Rejected => (pounds, chocs))
    Vend : MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
    GetCoins : MachineCmd () (pounds, chocs) (const (Z, chocs))
    Refill : (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, chocs + bars))

    Display : String -> MachineCmd () state (const state)
    GetInput : MachineCmd (Maybe Input) state (const state)

    Pure : ty -> MachineCmd ty state (const state)
    (>>=) : MachineCmd a state1 state2_fn ->
            ((res : a) -> MachineCmd b (state2_fn res) state3_fn) ->
            MachineCmd b state1 state3_fn

  data MachineIO : VendState -> Type where
    Do : MachineCmd a state1 state2_fn ->
         ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1

  namespace MachineDo
    (>>=) : MachineCmd a state1 state2_fn ->
            ((res : a) -> Inf (MachineIO (state2_fn res))) -> MachineIO state1
    (>>=) = Do

  mutual
    vend : MachineIO (pounds, chocs)
    vend {pounds = S p} {chocs = S c} = do
      Vend
      Display "Enjoy!"
      machineLoop
    vend {pounds = Z} = do
      Display "Insert a coin"
      machineLoop
    vend {chocs = Z} = do
      Display "Out of stock"
      machineLoop

    refill : (num : Nat) -> MachineIO (pounds, chocs)
    refill {pounds = Z} num = do
      Refill num
      machineLoop
    refill _ = do
      Display "Can't refill: Coind in machine"
      machineLoop

    machineLoop : MachineIO (pounds, chocs)
    machineLoop = do
      Just x <- GetInput
        | Nothing => do
                  Display "Invalid input"
                  machineLoop
      case x of
        COIN => do
          Inserted <- InsertCoin
            | Rejected => do
                       Display "Fake coin, mofo!!!"
                       machineLoop
          machineLoop
        VEND => vend
        CHANGE => do
          GetCoins
          Display "Change returned"
          machineLoop
        (REFILL k) => refill k


namespace Guess
  data GameState : Type where
    NotRunning : GameState
    Running : (guesses : Nat) -> (letters : Nat) -> GameState

  letters : String -> List Char
  letters str = nub (map toUpper (unpack str))

  data GuessResult = Correct | Incorrect

  data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    NewGame : (word : String) -> GameCmd () NotRunning
                                            (const (Running 6 (length (letters word))))
    Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
    Lost : GameCmd () (Running Z (S guesses)) (const NotRunning)

    Guess : (c : Char) -> GameCmd GuessResult (Running (S guesses) (S letters))
                                              (\res => case res of
                                                            Correct => Running (S guesses) letters
                                                            Incorrect => Running guesses (S letters))

    Pure : (res : ty) -> GameCmd ty (state_fn res) state_fn
    (>>=) : GameCmd a state1 state2_fn ->
            ((res : a) -> GameCmd b (state2_fn res) state3_fn) ->
            GameCmd b state1 state3_fn

    ShowState : GameCmd () state (const state)
    Message : String -> GameCmd () state (const state)
    ReadGuess : GameCmd Char state (const state)

  namespace Loop
    data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
      (>>=) : GameCmd a state1 state2_fn ->
              ((res : a) -> Inf (GameLoop b (state2_fn res) state3_fn)) ->
              GameLoop b state1 state3_fn
      Exit : GameLoop () NotRunning (const NotRunning)

  gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
  gameLoop {guesses} {letters} = do
    ShowState
    g <- ReadGuess
    ok <- Guess g
    case ok of
      Correct => case letters of
                   Z => do
                     Won
                     ShowState
                     Exit
                   (S k) => do
                     Message "Correct!"
                     gameLoop
      Incorrect => case guesses of
                     Z => do
                       Lost
                       ShowState
                       Exit
                     (S k) => do
                       Message "Wrong!"
                       gameLoop

  hangman : GameLoop () NotRunning (const NotRunning)
  hangman = do
    NewGame "testing"
    gameLoop

  data Game : GameState -> Type where
    GameStart : Game NotRunning
    GameWon : (word : String) -> Game NotRunning
    GameLost : (word : String) -> Game NotRunning
    InProgress : (word : String) -> (guesses : Nat) ->
                 (missing : Vect letters Char) ->
                 Game (Running guesses letters)

  Show (Game g) where
    show GameStart = "Starting"
    show (GameWon word) = "Game won: word was " ++ word
    show (GameLost word) = "Game lost: word was " ++ word
    show (InProgress word guesses missing) =
      "\n" ++ pack (map hideMissing (unpack word))
        ++ "\n" ++ show guesses ++ " guesses left."
      where
        hideMissing : Char -> Char
        hideMissing c = if c `elem` missing then '_' else c

  data Fuel = Dry | More (Lazy Fuel)

  data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
    OK : (res : ty) -> Game (outstate_fn res) -> GameResult ty outstate_fn
    OutOfFuel : GameResult ty outstate_fn

  run : Fuel -> Game instate -> GameLoop ty instate outstate -> IO (GameResult ty outstate_fn)
  -- Parei entre as páginas 398 e 399
