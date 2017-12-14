module WordCount

import ProcessLib

record WCData where
  constructor MkWCData
  wordCount : Nat
  lineCount : Nat

doCount : (content : String) -> WCData
doCount content =
  let lcount = length (lines content)
      wcount = length (words content)
  in MkWCData wcount lcount

data WC = CountFile String
        | GetData String

WCType : WC -> Type
WCType (CountFile x) = ()
WCType (GetData x) = Maybe WCData

countFile : (loaded : List (String, WCData)) -> (file : String) -> Process WCType (List (String, WCData)) Sent Sent
countFile loaded file = do
  Right content <- Action (readFile file)
    | Left err => do Action (putStrLn $ "Error opening " ++ file)
                     Pure loaded
  let count = doCount content
  Action (putStrLn ("Counting complete for " ++ file))
  Pure ((file, count) :: loaded)

wcService : (loaded : List (String, WCData)) ->
            Service WCType ()
wcService loaded = do
  msg <- Respond (\msg => case msg of
                            CountFile file => Pure ()
                            GetData file => Pure (lookup file loaded))
  newLoaded <- case msg of
                 Just (CountFile file) => countFile loaded file
                 _ => Pure loaded
  Loop (wcService newLoaded)

procMain : Client ()
procMain = do
  Just wc <- Spawn (wcService [])
    | Nothing => Action (putStrLn "Spawn failed")
  Action (putStrLn "Counting test.txt")
  Request wc (CountFile "test.txt")
  Action (putStrLn "Processing")
  Just wcdata <- Request wc (GetData "test.txt")
    | Nothing => Action (putStrLn "File error")
  Action (putStrLn $ "Word count: " ++ show (wordCount wcdata))
  Action (putStrLn $ "Line count: " ++ show (lineCount wcdata))
