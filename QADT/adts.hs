-- given an ordered list, and a new element, output a sorted list with
-- the new element added
insert :: (Ord a) => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = if x > y then y : insert x ys else x : (y : ys)

fold :: t -> (a -> t -> t) -> [a] -> t
fold t0 f [] = t0
fold t0 f (x:xs) = f x (fold t0 f xs)

mapFromFold :: (a -> b) -> [a] -> [b]
mapFromFold f = fold [] (\x y -> f x : y)

insertAtEnd :: a -> [a] -> [a]
insertAtEnd x0 = fold [x0] (:)

addList :: [Integer] -> Integer
addList = fold (0) (+)

concatLists :: [a] -> [a] -> [a]
concatLists xs ys = fold (ys) (:) xs

insertFromFold :: (Ord a) => a -> [a] -> [a]
insertFromFold x ys = fold [x] (\y zs -> if x > y then y : zs else x : y : zs) ys

data Nat = Z | S Nat deriving Show

iter :: a -> (a -> a) -> Nat -> a
iter z f Z = z
iter z f (S n) = f (iter z f n)

addFromIter :: Nat -> Nat -> Nat
addFromIter m = iter m S

mulFromIter :: Nat -> Nat -> Nat
mulFromIter m = iter (Z) (addFromIter m)

fac :: Nat -> Nat
fac Z = S Z
fac (S n) = mulFromIter (S n) (fac n)


fact :: Nat -> Nat
fact Z = S Z
fact (S n) = iter (S Z) (\k -> mulFromIter (S n) k) n

nat2int :: Nat -> Integer
nat2int Z = 0
nat2int (S n) = 1 + nat2int n
