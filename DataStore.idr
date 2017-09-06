module Main

import Data.Vect

data DataStore : Type where
  MkData : (size : Nat) ->
           (items : Vect size String) ->
           DataStore
%name DataStore store, store1, store2

size : DataStore -> Nat
size (MkData size' _) = size'

items : (store : DataStore) -> Vect (size store) String
items (MkData _ items') = items'

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) newitem = MkData _ (addToData items)
  where
    addToData : Vect old String -> Vect (S old) String
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs

data Command = Add String
             | Get Integer
             | Size
             | Search String
             | Quit

parseCommand : (cmd : String) -> (args : String) -> Maybe Command
parseCommand "add" args = Just (Add args)
parseCommand "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just (Get (cast val))
parseCommand "quit" "" = Just Quit
parseCommand "size" "" = Just Size
parseCommand "search" string = Just (Search string)
parseCommand _ _ = Nothing

parse : (input : String) -> Maybe Command
parse input = case span (/= ' ') input of
                   (cmd, args) => parseCommand cmd (ltrim args)

getEntry : (id : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry id store@(MkData size' items') =
  case integerToFin id size' of
    Nothing => Just ("Out of bounds.\n", store)
    (Just i) => Just (index i items' ++ "\n", store)

enumerate : Vect n elem -> Vect n (Nat, elem)
enumerate xs = go 0 xs
  where
    go : Nat -> Vect n elem -> Vect n (Nat, elem)
    go ind [] = []
    go ind (y :: ys) = (ind, y) :: go (S ind) ys

formatElems : Vect n (Nat, String) -> Vect n String
formatElems [] = []
formatElems ((a, b) :: xs) = (show a ++ "\t" ++ b) :: formatElems xs



searchStore : String -> DataStore -> Maybe (String, DataStore)
searchStore str store@(MkData size' items') =
  case filter (\(i,s) => Strings.isInfixOf str s) (enumerate items') of
    (x ** pf) => (case pf of
                       [] => Just ("Nothing found!!!", store)
                       elems@(x :: xs) => Just (concat (intersperse "\n" (formatElems elems)) ++ "\n", store))
    -- (x ** pf) => (case pf of
    --                    [] => Just ("Nothing found!!!\n", store)
    --                    elems => Just (concat (intersperse "\n" elems) ++ "\n", store))

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse input of
                            Nothing => Just ("Invalid command.\n", store)
                            Just cmd => case cmd of
                              Add x =>
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store x)
                              Get id => getEntry id store
                              Size => Just ("Size: " ++ show (size store) ++ "\n", store)
                              Search str => searchStore str store
                              Quit => Nothing

main : IO ()
main = replWith (MkData _ []) "Command: " processInput
