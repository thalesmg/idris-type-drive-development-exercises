import Data.Vect
import System

data VectUnknown : Type -> Type where
  MkVect : (len : Nat) -> Vect len a -> VectUnknown a

readVect0 : IO (VectUnknown String)
readVect0 = do
  x <- getLine
  if x == ""
    then pure (MkVect _ [])
    else do
      MkVect _ xs <- readVect0
      pure (MkVect _ (x :: xs))

printVect : Show a => VectUnknown a -> IO ()
printVect (MkVect len xs)
      = putStrLn (show xs ++ " (length " ++ show len ++ ")")

readVect : IO (len ** Vect len String)
readVect = do
  x <- getLine
  if x == ""
    then pure (_ ** [])
    else do
      (_ ** xs) <- readVect
      pure (_ ** x :: xs)

zipInputs : IO ()
zipInputs = do
  putStrLn "Enter first vector (blank line to end):"
  (len1 ** vec1) <- readVect
  putStrLn "Enter second vector (blank line to end):"
  (len2 ** vec2) <- readVect
  case exactLength len1 vec2 of
    Nothing => putStrLn "Vectors are of differente lengthe, entende?"
    Just vec2' => printLn (zip vec1 vec2')


printLonger : IO ()
printLonger = do
  putStrLn "Enter the first string:"
  str1 <- getLine
  putStrLn "Enter the second string:"
  str2 <- getLine
  let len1 = length str1
  let len2 = length str2
  (case compare len1 len2 of
        LT => putStrLn (show len2)
        _ => putStrLn (show len1))

printLonger2 : IO ()
printLonger2 =
  putStrLn "Enter the first string: " >>=
  \_ => getLine >>=
  \str1 => putStrLn "Enter the second string: " >>=
  \_ => getLine >>=
  \str2 => let len1 = length str1
               len2 = length str2
           in
             case compare len1 len2 of
               LT => putStrLn (show len2)
               _  => putStrLn (show len1)

parseInt : String -> Maybe Nat
parseInt input = case span isDigit input of
                  (num, "") => Just (cast num)
                  _         => Nothing

guess : (target : Nat) -> (guesses : Nat) -> IO ()
guess target guesses = do
  if guesses == Z
    then pure ()
    else putStrLn ("You have made " ++ show guesses ++ " wrong guesses...")
  putStrLn "Enter a number"
  input <- getLine
  case parseInt input of
    Nothing => do
      putStrLn "That was not a number, fool!!!"
      guess target guesses
    (Just num) => (case compare num target of
                          LT => do
                            putStrLn "Too low!"
                            guess target (S guesses)
                          EQ => do
                            putStrLn "You win!"
                          GT => do
                            putStrLn "Too high!"
                            guess target (S guesses))


main : IO ()
main = do
  int <- System.time
  let target = the Nat (cast (mod int 100) + 1)
  guess target Z


meuRepl : (prompito : String) -> (onInput : String -> String) -> IO ()
meuRepl prompito onInput = do
  putStrLn prompito
  input <- getLine
  putStrLn (onInput input)
  meuRepl prompito onInput

meuReplWith : (state : a) -> (prompito : String) -> (onInput : a -> String -> Maybe (String, a)) -> IO ()
meuReplWith state prompito onInput = do
  putStrLn prompito
  input <- getLine
  case onInput state input of
    Nothing => pure ()
    (Just (outputo, state')) => do
      putStrLn outputo
      meuReplWith state' prompito onInput


readToBlank : IO (List String)
readToBlank = do
  line <- getLine
  if line == ""
    then pure []
    else do
      rest <- readToBlank
      pure (line :: rest)

readAndSave : IO ()
readAndSave = do
  lines <- readToBlank
  filename <- getLine
  Right h <- openFile filename WriteTruncate
    | Left err => putStrLn ("Fodeu! " ++ show err)
  Right () <- writeFile filename (unlines lines)
    | Left err => putStrLn ("Fodeu foda! " ++ show err)
  pure ()

fReadVect : (file : File) -> IO (Either FileError (n ** Vect n String))
fReadVect file = do
  eof <- fEOF file
  if eof
    then pure (Right (_ ** []))
    else do
      Right x <- fGetLine file
        | Left err => pure (Left err)
      if x == ""
        then pure (Right (_ ** []))
        else do
          Right (k ** rest) <- fReadVect file
            | Left err => pure (Left err)
          pure (Right ((S k) ** ((trim x) :: rest)))

readVectFile : (filename : String) -> IO (n ** Vect n String)
readVectFile filename = do
  Right h <- openFile filename Read
    | Left err => pure (_ ** [])
  Right (n ** vect) <- fReadVect h
    | Left err => pure (_ ** [])
  pure (n ** vect)
