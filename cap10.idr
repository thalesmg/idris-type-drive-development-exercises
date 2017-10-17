module Cap10

import Data.Vect
import Data.List.Views
import Data.Vect.Views
import Data.Nat.Views

data TakeN : List a -> Type where
  Fewer : TakeN xs
  Exact : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN n xs = takeNHelper n xs
  where
    takeNHelper : Nat -> (input : List a) -> TakeN input
    -- takeNHelper Z [] = Fewer --Exact ([] ++ [])
    -- takeNHelper Z (x :: zs) = Fewer -- ?!??!?!
    takeNHelper Z xs = Exact ([] ++ [])
    takeNHelper (S k) [] = Fewer
    takeNHelper (S k) (x :: zs) = case takeNHelper k zs of
                                          Fewer {xs = boom} => Fewer
                                          Exact n_xs => Exact (x::n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | Fewer = [xs]
  groupByN n (n_xs ++ rest) | (Exact n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs with (takeN (div (length xs) 2) xs)
  halves xs | Fewer = ([], xs)
  halves (n_xs ++ rest) | (Exact n_xs) = (n_xs, rest)

equalSuffix : Eq a => List a -> List a -> List a
equalSuffix xs ys = reverse $ helper xs ys
  where
    helper : Eq a => List a -> List a -> List a
    helper xs ys with (snocList ys)
      helper xs [] | Empty = []
      helper xs (zs ++ [x]) | (Snoc rec) with (snocList xs)
        helper [] (zs ++ [x]) | (Snoc rec) | Empty = []
        helper (ys ++ [y]) (zs ++ [x]) | (Snoc rec1) | (Snoc rec2) =
          if x == y
            then x :: (helper ys zs | rec1 | rec2)
            else []

mergeSort : Ord a => Vect n a -> Vect n a
mergeSort xs with (splitRec xs)
  mergeSort [] | SplitRecNil = []
  mergeSort [x] | SplitRecOne = [x]
  mergeSort (ys ++ zs) | (SplitRecPair lrec rrec) =
    merge (mergeSort ys) (mergeSort zs)
    where
      merge : Ord a => Vect n a -> Vect m a -> Vect (n + m) a
      merge [] ys = ys
      merge {n} xs [] = rewrite plusZeroRightNeutral n in xs
      merge {n = S o} (x :: xs) {m = S p} (y :: ys) = case compare x y of
                                       LT => x :: merge xs (y::ys)
                                       _ => rewrite sym (plusSuccRightSucc o p) in
                                            y :: merge (x::xs) ys

toBinary : Nat -> String
toBinary k = reverse (go k)
  where
     go k with (halfRec k)
       go Z | HalfRecZ = ""
       go (n + n) | (HalfRecEven rec) = strCons '0' (go n | rec)
       go (S (n + n)) | (HalfRecOdd rec) = strCons '1' (go n | rec)

palindrome : DecEq a => List a -> Bool
palindrome lst with (vList lst)
  palindrome [] | VNil = True
  palindrome [x] | VOne = True
  palindrome (x :: (xs ++ [y])) | (VCons rec) =
    case decEq x y of
      (Yes prf) => palindrome xs | rec
      (No contra) => False
