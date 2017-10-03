

occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item [] = 0
occurrences item (x :: xs) = case x == item of
                                  False => occurrences item xs
                                  True => 1 + occurrences item xs

data Matter = Solid
            | Liquid
            | Gas

Eq Matter where
  (==) Solid Solid = True
  (==) Liquid Liquid = True
  (==) Gas Gas = True
  (==) _ _ = False

  (/=) x y = not (x == y)


data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)

Eq elem => Eq (Tree elem) where
  (==) Empty Empty = True
  (==) (Node t11 e1 t12) (Node t21 e2 t22) =
       (t11 == t21) && e1 == e2 && (t12 == t22)
  (==) _ _ = False


data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle x y) = (x * y) / 2
area (Rectangle x y) = x * y
area (Circle x) = pi *  x * x

Eq Shape where
  (==) (Triangle x z) (Triangle y w) = (x == y) && (z == w)
  (==) (Rectangle x z) (Rectangle y w) = (x == y) && (z == w)
  (==) (Circle x) (Circle y) = x == y
  (==) _ _ = False

Ord Shape where
  compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]


data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)

eval : (Neg num, Integral num) => Expr num -> num
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Abs x) = abs (eval x)


Num ty => Num (Expr ty) where
  (+) = Add
  (*) = Mul
  fromInteger x = Val (fromInteger x)

Neg ty => Neg (Expr ty) where
  negate x = 0 - x
  (-) = Sub
  abs = Abs

Show ty => Show (Expr ty) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Abs x) = "|" ++ show x ++ "|"

(Integral ty, Neg ty, Eq ty) => Eq (Expr ty) where
  (==) x y = (eval x) == (eval y)

(Integral ty, Neg ty) => Cast (Expr ty) ty where
  cast orig = eval orig

Functor Expr where
  map func (Val x) = Val (func x)
  map func (Add x y) = Add (map func x) (map func y)
  map func (Sub x y) = Sub (map func x) (map func y)
  map func (Mul x y) = Mul (map func x) (map func y)
  map func (Div x y) = Div (map func x) (map func y)
  map func (Abs x) = Abs (map func x)

data Vect : Nat -> Type -> Type where
  Nil  : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

Eq a => Eq (Vect n a) where
  (==) [] [] = True
  (==) (x :: z) (y :: w) = (x == y) && (z == w)

Foldable (Vect n) where
  foldr func init [] = init
  foldr func init (x :: y) = func x (foldr func init y)
  foldl func init [] = init
  foldl func init (x :: y) = foldl func (func init x) y

Functor Tree where
  map func Empty = Empty
  map func (Node x y z) =
    Node (map func x)
         (func y)
         (map func z)


totalLen : List String -> Nat
totalLen xs = foldr (\s, l => length s + l) 0 xs

Foldable Tree where
  foldr func init Empty = init
  foldr func init (Node x y z)
    = let rightFold = foldr func init z
          middleFold = func y rightFold in
          foldr func middleFold x
