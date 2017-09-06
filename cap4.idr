import Data.Vect

data Tree elem = Empty
               | Node (Tree elem) elem (Tree elem)
%name Tree tree, tree1

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x orig@(Node left y right) = case compare x y of
                                    LT => Node (insert x left) y right
                                    EQ => orig
                                    GT => Node left y (insert x right)

listToTree : Ord a => List a -> Tree a
listToTree [] = Empty
listToTree (x :: xs) = insert x (listToTree xs)

treeToList : Tree a -> List a
treeToList Empty = []
treeToList (Node left x right) = treeToList left ++ [x] ++ treeToList right

data Expr : Type where
  Prim : Int -> Expr
  Add  : Expr -> Expr -> Expr
  Sub  : Expr -> Expr -> Expr
  Mul  : Expr -> Expr -> Expr

%name Expr expr, expr1, expr2

evaluate : Expr -> Int
evaluate expr = case expr of
                     (Prim x) => x
                     (Add expr1 expr2) => evaluate expr1 + evaluate expr2
                     (Sub expr1 expr2) => evaluate expr1 - evaluate expr2
                     (Mul expr1 expr2) => (evaluate expr1) * (evaluate expr2)

maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = case compare x y of
                                  LT => Just y
                                  EQ => Just x
                                  GT => Just x

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture

area : Shape -> Double
area (Triangle x y) = x * y / 2
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive x) = case x of
                                     t@(Triangle y z) => Just (area t)
                                     _ => Nothing
biggestTriangle (Combine x y) = maxMaybe (biggestTriangle x) (biggestTriangle y)
biggestTriangle (Rotate x y) = biggestTriangle y
biggestTriangle (Translate x y z) = biggestTriangle z


data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
     Bicycle : Vehicle Pedal
     Car : (fuel : Nat) -> Vehicle Petrol
     Bus : (fuel : Nat) -> Vehicle Petrol
     Unicycle : Vehicle Pedal
     Motorcycle : (fuel : Nat) -> Vehicle Petrol
     Tram : (charge : Nat) -> Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels Unicycle = 1
wheels (Motorcycle fuel) = 2
wheels (Tram charge) = 6

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50
refuel Bicycle impossible
refuel Unicycle impossible
refuel (Tram fuel) impossible

recharge : Vehicle Electric -> Vehicle Electric
recharge (Tram charge) = Tram 400

-- take : Nat -> List a -> List a
-- take k [] = []
-- take Z (x :: xs) = xs
-- take (S k) (x :: xs) = x :: take k xs

vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vectTake Z xs = []
vectTake (S k) (x :: xs) = x :: vectTake k xs


sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                (Just nat) => Just (index nat xs + index nat ys)
