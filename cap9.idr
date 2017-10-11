module Cap09

import Data.Vect

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem x (x :: xs) {prf = Here} = xs
removeElem {n = Z}   value (x :: []) {prf = (There later)} = absurd later
removeElem {n = S k} value (x :: xs) {prf = (There later)} = x :: removeElem value xs

data Last : List a -> a -> Type where
  LastOne  : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

Uninhabited (Last [] value) where
  uninhabited x impossible

notInNil : Last [] value -> Void
notInNil x impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast contra (LastCons prf) = notInNil prf

notInLast : (contra2 : Last xs value -> Void) -> (contra1 : (xs = []) -> Void) -> Last (x :: xs) value -> Void
notInLast contra2 contra1 LastOne = contra1 Refl
notInLast contra2 contra1 (LastCons prf) = contra2 prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInNil
isLast (x :: xs) value = case decEq xs [] of
                              (Yes prf1) => (case decEq x value of
                                                 (Yes prf2) => rewrite prf2
                                                               in rewrite prf1
                                                               in Yes LastOne
                                                 (No contra) => rewrite prf1 in No (notLast contra))
                              (No contra1) => (case isLast xs value of
                                                   (Yes prf) => Yes (LastCons prf)
                                                   (No contra2) => No (notInLast contra2 contra1))
