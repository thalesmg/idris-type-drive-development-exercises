
import Data.Vect

valToString : (isInt : Bool) -> (case isInt of
                                         False => String
                                         True => Int) -> String
valToString False x = trim x
valToString True x = cast x

AdderType : (numargs : Nat) -> Type
AdderType Z = Int
AdderType (S k) = Int -> AdderType k

adder : (numargs : Nat) -> (acc : Int) -> AdderType numargs
adder Z acc = acc
adder (S k) acc = \next => adder k (acc + next)

data Format = Number Format
            | Str Format
            | Lit String Format
            | End
            | Dbl Format
            | Chr Format

%name Format fmt, fmt1

PrintfType : Format -> Type
PrintfType (Number fmt) = (i : Int) -> PrintfType fmt
PrintfType (Str fmt) = (s : String) -> PrintfType fmt
PrintfType (Lit x fmt) = PrintfType fmt
PrintfType End = String
PrintfType (Dbl fmt) = (d : Double) -> PrintfType fmt
PrintfType (Chr fmt) = (x : Char) -> PrintfType fmt

printfFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printfFmt (Number fmt) acc = \i => printfFmt fmt (acc ++ show i)
printfFmt (Str fmt) acc = \s => printfFmt fmt (acc ++ s)
printfFmt (Lit x fmt) acc = printfFmt fmt (acc ++ x)
printfFmt End acc = acc
printfFmt (Dbl fmt) acc = \d => printfFmt fmt (acc ++ show d)
printfFmt (Chr fmt) acc = \c => printfFmt fmt (acc ++ (strCons c ""))

toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: chars) = Number (toFormat chars)
toFormat ('%' :: 's' :: chars) = Str (toFormat chars)
toFormat ('%' :: 'f' :: chars) = Dbl (toFormat chars)
toFormat ('%' :: 'c' :: chars) = Chr (toFormat chars)
toFormat ('%' :: chars) = Lit "%" (toFormat chars)
toFormat (c :: chars) = case toFormat chars of
                             (Lit cs fmt) => Lit (strCons c cs) fmt
                             fmt => Lit (strCons c "") fmt

printf : (fmt : String) -> PrintfType (toFormat (unpack fmt))
printf fmt = printfFmt _ ""



Matrix : Nat -> Nat -> Type
Matrix n m = Vect n (Vect m Double)

testMatrix : Matrix 2 3
testMatrix = [[0,0,0], [0,0,0]]

TupleVect : Nat -> Type -> Type
TupleVect Z ty = ()
TupleVect (S k) ty = (ty, TupleVect k ty)

testeTuple : TupleVect 4 Nat
testeTuple = (1, 2, 3, 4, ())
