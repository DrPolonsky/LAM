data FX = BNode FX FX | UNode1 FX | UNode2 FX | Leaf
  deriving (Eq, Show)

type FX2 = (FX, FX)

f :: Maybe (Either (FX2, FX2) (FX2, Bool)) -> FX2
f Nothing = (Leaf, Leaf)
f (Just (Right ((Leaf, fx), False))) = (Leaf, UNode1 fx)
f (Just (Right ((UNode1 fx1, fx2), False))) = (Leaf, BNode fx1 fx2)
f (Just (Right ((UNode2 fx1, fx2), False))) = (BNode fx1 fx2, Leaf)
f (Just (Right ((BNode fx1 fx2, fx3), False))) = (BNode fx1 fx2, UNode1 fx3)
f (Just (Right ((fx, Leaf), True))) = (Leaf, UNode2 fx)
f (Just (Right ((fx1, UNode1 fx2), True))) = (UNode1 fx1, fx2)
f (Just (Right ((fx1, UNode2 fx2), True))) = (UNode2 fx1, fx2)
f (Just (Right ((fx1, BNode fx2 fx3), True))) = (BNode fx1 fx3, UNode2 fx2)
f (Just (Left ((fx1, fx2), (fx3, fx4)))) = (BNode fx1 fx3, BNode fx2 fx4)

foldF :: FX -> FX2
foldF (Leaf) = f Nothing
foldF (UNode1 fx) = f (Just (Right (foldF fx, False)))
foldF (UNode2 fx) = f (Just (Right (foldF fx, True)))
foldF (BNode fx1 fx2) = f (Just (Left (foldF fx1, foldF fx2)))

g :: FX2 -> Maybe (Either (FX2, FX2) (FX2, Bool))
g (Leaf, Leaf) = Nothing
g (Leaf, UNode1 fx) = Just (Right ((Leaf, fx), False))
g (Leaf, BNode fx1 fx2) = (Just (Right ((UNode1 fx1, fx2), False)))
g (BNode fx1 fx2, Leaf) = (Just (Right ((UNode2 fx1, fx2), False)))
g (BNode fx1 fx2, UNode1 fx3) = (Just (Right ((BNode fx1 fx2, fx3), False)))
g (Leaf, UNode2 fx) = Just (Right((fx, Leaf), True))
g (UNode1 fx1, fx2) = (Just (Right ((fx1, UNode1 fx2), True)))
g (UNode2 fx1, fx2) = (Just (Right ((fx1, UNode2 fx2), True)))
g (BNode fx1 fx3, UNode2 fx2) = (Just (Right ((fx1, BNode fx2 fx3), True)))
g (BNode fx1 fx3, BNode fx2 fx4) = (Just (Left ((fx1, fx2), (fx3, fx4))))

unfold :: Maybe (Either (FX2, FX2) (FX2, Bool)) -> FX
unfold Nothing = Leaf
unfold (Just (Right (fx2, False))) = UNode1 (unfold (g fx2))
unfold (Just (Right (fx2, True))) = UNode2 (unfold (g fx2))
unfold (Just (Left (fx20,fx21))) = BNode (unfold (g fx20)) (unfold (g fx21))

test1 :: FX -> FX
test1 = (unfold . g) . foldF

test2 :: FX2 -> FX2
test2 = foldF . (unfold . g)

merge :: [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = x:y:merge xs ys

lazyProd :: [a] -> [a] -> [(a,a)]
lazyProd xs [] = []
lazyProd [] ys = []
lazyProd (x:xs) (y:ys) = (x,y) : merge (lazyProd xs (y:ys)) ((\z -> (x,z)) <$> ys)

allFX :: [FX]
allFX = Leaf : merge (merge (UNode1 <$> allFX) (UNode2 <$> allFX)) (uncurry BNode <$> lazyProd allFX allFX)

allFX2 :: [FX2]
allFX2 = lazyProd allFX allFX

list1 = [x == test1 x | x <- take 10000 allFX]
list2 = [x == test2 x | x <- take 10000 allFX2]

swap :: (a,b) -> (b,a)
swap (x,y) = (y,x)

mapj :: (a -> b) -> Maybe (Either (a, a) (a, Bool)) -> Maybe (Either (b, b) (b, Bool))
mapj f Nothing = Nothing
mapj f (Just (Left (x , y))) = Just (Left (f x, f y))
mapj f (Just (Right (x,c))) = Just (Right (f x, c))

jswap :: Maybe (Either (FX2, FX2) (FX2, Bool)) -> Maybe (Either (FX2, FX2) (FX2, Bool))
jswap = mapj swap

list3 = [((g . swap) x , (jswap . g) x) | x <- (take 10000 allFX2) ]

check :: [Bool] -> Bool
check = all id
