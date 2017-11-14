module Cap12

import Control.Monad.State

%default total

update : (stateType -> stateType) -> State stateType ()
update f = do
  actual <- get
  put . f $ actual

increase : Nat -> State Nat ()
increase k = update (+k)

data Tree a = Empty
            | Node (Tree a) a (Tree a)

testTree : Tree String
testTree = Node (Node (Node Empty "Jim" Empty) "Fred"
                (Node Empty "Sheila" Empty)) "Alice"
                (Node Empty "Bob" (Node Empty "Eve" Empty))

countEmpty : Tree a -> State Nat ()
countEmpty Empty = increase 1
countEmpty (Node l _ r) = do
  countEmpty l
  countEmpty r

increase' : Either Nat Nat -> State (Nat, Nat) ()
increase' (Left val) = update (\(x, y) => (x + val, y))
increase' (Right val) = update (\(x, y) => (x, y + val))

countEmptyNode : Tree a -> State (Nat, Nat) ()
countEmptyNode Empty = increase' (Left 1)
countEmptyNode (Node l _ r) = do
  countEmptyNode l
  increase' (Right 1)
  countEmptyNode r
