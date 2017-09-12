module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

%name Schema schm, schm1, schm2

SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (schm .+. schm1) = (SchemaType schm, SchemaType schm1)

record DataStore where
  constructor MkData
  schema : Schema
  size : Nat
  items : Vect size (SchemaType schema)

%name DataStore store, store1, store2


addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem = MkData schema _ (addToData items)
  where
    addToData : Vect old (SchemaType schema) -> Vect (S old) (SchemaType schema)
    addToData [] = [newitem]
    addToData (x :: xs) = x :: addToData xs


data Command : Schema -> Type where
  Add : SchemaType schema -> Command schema
  Get : Integer -> Command schema
  Size : Command schema
  Quit : Command schema
  SetSchema : (newschema : Schema) -> Command schema
  -- Search : SchemaType schema -> Command schema

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString x = getQuoted (unpack x)
  where
    getQuoted : List Char -> Maybe (String, String)
    getQuoted ('"'::rest0) =
      (case span (/= '"') rest0 of
            (text, '"'::rest1) => Just (pack text, ltrim (pack rest1))
            _ => Nothing)
    getQuoted _ = Nothing
parsePrefix SInt x = case span isDigit x of
                          ("", rest) => Nothing
                          (num, rest) => Just (cast num, ltrim rest)
parsePrefix (schm1 .+. schm2) x = do
  (res1, rest1) <- parsePrefix schm1 x
  (res2, rest2) <- parsePrefix schm2 rest1
  if rest2 == ""
    then pure ((res1, res2), "")
    else Nothing


parseBySchema : (schema : Schema) -> (args : String) -> Maybe (SchemaType schema)
parseBySchema schema args = case parsePrefix schema args of
                                 Nothing => Nothing
                                 Just (res, "") => Just res
                                 Just _ => Nothing

parseCommand : (schema : Schema) -> (cmd : String) -> (args : String) -> Maybe (Command schema)
parseCommand schema "add" args = case parseBySchema schema args of
                                      Nothing => Nothing
                                      (Just x) => Just (Add x)
parseCommand schema "get" val = case all isDigit (unpack val) of
                                     False => Nothing
                                     True => Just (Get (cast val))
parseCommand schema "quit" "" = Just Quit
parseCommand schema "size" "" = Just Size
-- parseCommand "search" string = Just (Search string)
parseCommand _ _ _ = Nothing

parse : (schema : Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (cmd, args) => parseCommand schema cmd (ltrim args)

display : SchemaType schema -> String
display {schema = SString} item          = show item
display {schema = SInt} item             = show item
display {schema = (schm .+. schm1)} (a, b) = display a ++ ", " ++ display b

getEntry : (id : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry id store@(MkData schema size items) =
  case integerToFin id size of
    Nothing => Just ("Out of bounds.\n", store)
    (Just i) => Just (display (index i items) ++ "\n", store)


enumerate : Vect n elem -> Vect n (Nat, elem)
enumerate xs = go 0 xs
  where
    go : Nat -> Vect n elem -> Vect n (Nat, elem)
    go ind [] = []
    go ind (y :: ys) = (ind, y) :: go (S ind) ys

formatElems : Vect n (Nat, String) -> Vect n String
formatElems [] = []
formatElems ((a, b) :: xs) = (show a ++ "\t" ++ b) :: formatElems xs


{-
searchStore : String -> DataStore -> Maybe (String, DataStore)
searchStore str store@(MkData schema size items) =
  case filter (\(i,s) => Strings.isInfixOf str s) (enumerate items') of
    (x ** pf) => (case pf of
                       [] => Just ("Nothing found!!!", store)
                       elems@(x :: xs) => Just (concat (intersperse "\n" (formatElems elems)) ++ "\n", store))
    -- (x ** pf) => (case pf of
    --                    [] => Just ("Nothing found!!!\n", store)
    --                    elems => Just (concat (intersperse "\n" elems) ++ "\n", store))
-}

processInput : DataStore -> String -> Maybe (String, DataStore)
processInput store input = case parse (schema store) input of
                            Nothing => Just ("Invalid command.\n", store)
                            Just cmd => case cmd of
                              Add item =>
                                Just ("ID " ++ show (size store) ++ "\n", addToStore store item)
                              Get id => getEntry id store
                              Size => Just ("Size: " ++ show (size store) ++ "\n", store)
                              -- Search str => searchStore str store
                              Quit => Nothing
{-
main : IO ()
main = replWith (MkData _ []) "Command: " processInput
-}
