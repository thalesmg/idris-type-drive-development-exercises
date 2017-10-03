module CH08

import Data.Vect

same_cons : {xs : List a} -> {ys : List a} ->
            xs = ys -> x :: xs = x :: ys
same_cons {xs = ys} {ys = ys} {x = x} Refl = Refl


same_lists : {xs : List a} -> {ys : List a} ->
             x = y -> xs = ys -> x :: xs = y :: ys
same_lists {xs = ys} {ys = ys} {x = x} {y = x} Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  SameThree : (x : ty) -> ThreeEq x x x

-- ThreeEq : a -> b -> c -> Type
-- ThreeEq x y z = ?ThreeEq_rhs

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (SameThree z) = SameThree (S z)

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes   Z   m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = rewrite myPlusCommutes k m
                         in rewrite plusSuccRightSucc m k
                         in Refl

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
  where reverse' : Vect n a -> Vect m a -> Vect (n + m) a
        reverse' {n} acc [] = rewrite plusZeroRightNeutral n in acc
        reverse' {n = n} {m = S k} acc (x :: xs)
                        = rewrite sym (plusSuccRightSucc n k) in (reverse' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
              (contra : (x = y) -> Void) -> ((x::xs) = (y::ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} ->
              (contra : (xs = ys) -> Void) -> ((x::xs) = (y::ys)) -> Void
tailUnequal contra Refl = contra Refl


data MeuVect : Nat -> Type -> Type where
  Nil  : MeuVect Z a
  (::) : a -> MeuVect k a -> MeuVect (S k) a

meuHeadUnequal : DecEq a => {xs : MeuVect n a} -> {ys : MeuVect n a} ->
              (contra : (x = y) -> Void) -> ((x::xs) = (y::ys)) -> Void
meuHeadUnequal contra Refl = contra Refl

meuTailUnequal : DecEq a => {xs : MeuVect n a} -> {ys : MeuVect n a} ->
              (contra : (xs = ys) -> Void) -> ((x::xs) = (y::ys)) -> Void
meuTailUnequal contra Refl = contra Refl

same_meu_vect : {xs : MeuVect n a} -> {ys : MeuVect n a} ->
                x = y -> xs = ys -> x :: xs = y :: ys
same_meu_vect {xs = ys} {ys = ys} {x = x} {y = x} Refl Refl = Refl

DecEq a => DecEq (MeuVect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: y) (z :: w) = case decEq x z of
                                 (Yes prf) =>   case decEq y w of
                                                     (Yes prf2) =>  Yes (same_meu_vect prf prf2)
                                                     (No contra) => No (meuTailUnequal contra)
                                 (No contra) => No (meuHeadUnequal contra)
