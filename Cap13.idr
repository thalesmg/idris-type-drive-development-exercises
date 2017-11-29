module Cap13

import Data.Vect

%default total

data DoorState = DoorClosed | DoorOpen

data DoorCmd : Type ->
               DoorState ->
               DoorState ->
               Type where
  Open : DoorCmd () DoorClosed DoorOpen
  Close : DoorCmd () DoorOpen DoorClosed
  RingBell : DoorCmd () state state

  Pure : ty -> DoorCmd ty state state
  (>>=) : DoorCmd a state1 state2 ->
          (a -> DoorCmd b state2 state3) ->
          DoorCmd b state1 state3

doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do
  RingBell
  Open
  RingBell
  Close

VendState : Type
VendState = (Nat, Nat)

data MachineCmd : Type ->
                  VendState ->
                  VendState ->
                  Type where
  InsertCoin : MachineCmd () (pounds, chocs) (S pounds, chocs)
  Vend : MachineCmd () (S pounds, S chocs) (pounds, chocs)
  GetCoins : MachineCmd () (pounds, chocs) (Z, chocs)


-- Ex2, pg 362
namespace Ex2
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S k) k

    Pure : ty -> GuessCmd ty state state
    (>>=) : GuessCmd a state1 state2 ->
            (a -> GuessCmd b state2 state3) ->
            GuessCmd b state1 state3

  threeGuesses : GuessCmd () 3 0
  threeGuesses = do
    Try 10
    Try 20
    Try 15
    Pure ()

  noGuesses : GuessCmd () 0 0
  -- noGuesses = do
  --   Try 10
  --   Pure ()

-- Ex. 3, pg 362
namespace Ex3
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Melt : MatterCmd () Solid Liquid
    Condense : MatterCmd () Gas Liquid
    Boil : MatterCmd () Liquid Gas
    Freeze : MatterCmd () Liquid Solid

    Pure : ty -> MatterCmd ty state state
    (>>=) : MatterCmd a state1 state2 ->
            (a -> MatterCmd b state2 state3) ->
            MatterCmd b state1 state3

  iceSteam : MatterCmd () Solid Gas
  iceSteam = do
    Melt
    Boil

  steamIce : MatterCmd () Gas Solid
  steamIce = do
    Condense
    Freeze

  overMelt : MatterCmd () Solid Gas
  -- overMelt = do
  --   Melt
  --   Melt


-- Ex. 1, pg. 371
namespace Ex1
  data StackCmd : Type -> Nat -> Nat -> Type where
    Push : Integer -> StackCmd () height (S height)
    Pop : StackCmd Integer (S height) height
    Top : StackCmd Integer (S height) (S height)

    GetStr : StackCmd String height height
    PutStr : String -> StackCmd () height height

    Pure : ty -> StackCmd ty height height
    (>>=) : StackCmd a height1 height2 ->
            (a -> StackCmd b height2 height3) ->
            StackCmd b height1 height3

  runStack : (stk : Vect inHeight Integer) ->
             StackCmd ty inHeight outHeight ->
             IO (ty, Vect outHeight Integer)
  runStack stk (Push val) = pure ((), val :: stk)
  runStack (val :: stk) Pop = pure (val, stk)
  runStack (val :: stk) Top = pure (val, val :: stk)
  runStack stk (Pure val) = pure (val, stk)
  runStack stk GetStr = do
    input <- getLine
    pure (input, stk)
  runStack stk (PutStr y) = do
    putStr y
    pure ((), stk)
  runStack stk (cmd >>= next) = do
    (cmdRes, newStk) <- runStack stk cmd
    runStack newStk (next cmdRes)


  doAdd : StackCmd () (S (S height)) (S height)
  doAdd = do
    val1 <- Pop
    val2 <- Pop
    Push (val1 + val2)

  doSubtract : StackCmd () (S (S height)) (S height)
  doSubtract = do
    val1 <- Pop
    val2 <- Pop
    Push (val1 - val2)

  doMultiply : StackCmd () (S (S height)) (S height)
  doMultiply = do
    val1 <- Pop
    val2 <- Pop
    Push (val1 * val2)

  doNegate : StackCmd () (S height) (S height)
  doNegate = do
    val <- Pop
    Push (- val)

  doDuplicate : StackCmd () (S height) (S (S height))
  doDuplicate = do
    val <- Top
    Push val

  data StackIO : Nat -> Type where
    Do : StackCmd a height1 height2 ->
         (a -> Inf (StackIO height2)) -> StackIO height1

  namespace StackDo
    (>>=) : StackCmd a height1 height2 ->
            (a -> Inf (StackIO height2)) -> StackIO height1
    (>>=) = Do

  data Fuel = Dry | More (Lazy Fuel)

  partial
  forever : Fuel
  forever = More forever

  run : Fuel -> Vect height Integer -> StackIO height -> IO ()
  run Dry stk p = pure ()
  run (More fuel) stk (Do c f) = do
    (res, newStk) <- runStack stk c
    run fuel newStk (f res)

  data StkInput = Number Integer
                | Add
                | Sub
                | Mul
                | Neg
                | Discard
                | Dup

  strToInput : String -> Maybe StkInput
  strToInput "" = Nothing
  strToInput "add" = Just Add
  strToInput "subtract" = Just Sub
  strToInput "multiply" = Just Mul
  strToInput "negate" = Just Neg
  strToInput "discard" = Just Discard
  strToInput "duplicate" = Just Dup
  strToInput x = if all isDigit (unpack x)
                    then Just (Number (cast x))
                    else Nothing

  mutual
    tryAdd : StackIO height
    tryAdd {height = S (S k)} = do
      doAdd
      result <- Top
      PutStr (show result ++ "\n")
      stackCalc
    tryAdd = do
      PutStr "Fewer than two elements on the stack...\n"
      stackCalc

    trySub : StackIO height
    trySub {height = S (S k)} = do
      doSubtract
      result <- Top
      PutStr (show result ++ "\n")
      stackCalc
    trySub = do
      PutStr "Fewer than two elements on the stack...\n"
      stackCalc

    tryMul : StackIO height
    tryMul {height = S (S k)} = do
      doMultiply
      result <- Top
      PutStr (show result ++ "\n")
      stackCalc
    tryMul = do
      PutStr "Fewer than two elements on the stack...\n"
      stackCalc

    tryNeg : StackIO height
    tryNeg {height = S k} = do
      doNegate
      result <- Top
      PutStr (show result ++ "\n")
      stackCalc
    tryNeg = do
      PutStr "No elements on the stack...\n"
      stackCalc

    tryDiscard : StackIO height
    tryDiscard {height = S k} = do
      val <- Pop
      PutStr ("Discarded " ++ show val ++ "\n")
      stackCalc
    tryDiscard = do
      PutStr "No elements on the stack...\n"
      stackCalc

    tryDuplicate : StackIO height
    tryDuplicate {height = S k} = do
      doDuplicate
      val <- Top
      PutStr ("Duplicated " ++ show val ++ "\n")
      stackCalc
    tryDuplicate = do
      PutStr "No elements on the stack...\n"
      stackCalc

    stackCalc : StackIO height
    stackCalc = do
      PutStr "> "
      input <- GetStr
      case strToInput input of
        Nothing => do
          PutStr "Invalid input\n"
          stackCalc

        Just (Number x) => do Push x
                              stackCalc
        Just Add => tryAdd
        Just Sub => trySub
        Just Mul => tryMul
        Just Neg => tryNeg
        Just Discard => tryDiscard
        Just Dup => tryDuplicate

  partial
  main : IO ()
  main = run forever [] stackCalc
