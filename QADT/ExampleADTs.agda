module QADT.ExampleADTs where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment

-- B = 1 + B²

b : ADT (↑ ⊥)
b = 1+ (𝕧₀ ²)

B : ADT ⊥
B = μ b

BB : Set
BB = ⟦ B ⟧ Γ₀

Bleaf : BB
Bleaf = lfp (in1 tt)
Bnode : BB → BB → BB
Bnode x y = lfp (in2 (x , y))
BnodeCurried : BB ∧ BB → BB
BnodeCurried (x , y) = lfp (in2 (x , y))

allB : ℕ → List BB
allB 0 = []
allB (succ n) =
  let b² = lazyProd (allB n) (allB n)
      bn = List→ BnodeCurried b²
      in Bleaf ∷ bn

==B : BB → BB → 𝔹
==B = ==ADT {B}

-- B pretty printer
data ppB : Set where
  bl : ppB
  bb : ppB → ppB → ppB

BB→ppB : BB → ppB
BB→ppB (lfp (in1 tt)) = bl
BB→ppB (lfp (in2 (x , y))) = bb (BB→ppB x ) (BB→ppB y)

ppB→BB : ppB → BB
ppB→BB bl = lfp (in1 tt)
ppB→BB (bb x y) = lfp (in2 ((ppB→BB x) , ppB→BB y ) )

-- 2B

2b : ADT (↑ ⊥)
2b = 𝟏 ⊔ ((𝟏 ⊔ 𝕧₀ ²) ⊔ (𝕧₀ ²))

2B : ADT ⊥
2B = μ 2b

2BB : Set
2BB = ⟦ 2B ⟧ Γ₀

2Bleaf1 : 2BB
2Bleaf1 = lfp (in1 tt )
2Bleaf2 : 2BB
2Bleaf2 = lfp (in2 (in1 (in1 tt ) )  )
2Bnode1 : 2BB → 2BB → 2BB
2Bnode1 x y = lfp (in2 (in1 (in2 (x , y) ) ) )
2Bnode2 : 2BB → 2BB → 2BB
2Bnode2 x y = lfp (in2 (in2  (x , y) ) )
2Bnode1Curried : 2BB ∧ 2BB → 2BB
2Bnode1Curried (x , y) = lfp (in2 (in1 (in2 (x , y)) ) )
2Bnode2Curried : 2BB ∧ 2BB → 2BB
2Bnode2Curried (x , y) = lfp (in2 (in2 (x , y)))

all2B : ℕ → List 2BB
all2B 0 = []
all2B (succ n) =
  let b² = lazyProd (all2B n) (all2B n)
      bn1 = List→ 2Bnode1Curried b²
      bn2 = List→ 2Bnode2Curried b²
      in 2Bleaf1 ∷ 2Bleaf2 ∷ (merge bn1 bn2)

==2B : 2BB → 2BB → 𝔹
==2B = ==ADT {2B}

-- B²

B² : ADT ⊥
B² = B ²

BB² : Set
BB² = BB ∧ BB

allB² : ℕ → List (BB²)
allB² n = lazyProd (allB n) (allB n)


BB²→ppB : BB² → ppB ∧ ppB
BB²→ppB (b1 , b2) = (BB→ppB b1 ) , BB→ppB b2

ppB→BB² : ppB ∧ ppB → BB²
ppB→BB² (b1 , b2) = (ppB→BB b1)  , (ppB→BB b2)

-- T = 1 + T + T³

t : ADT (↑ ⊥)
t = 1+ (𝕧₀ ⊔ (𝕧₀ ³))

T : ADT ⊥
T = μ t

TT : Set
TT = ⟦ T ⟧ Γ₀

Tleaf : TT
Tleaf = lfp (in1 tt)
Tunode : TT → TT
Tunode x = lfp (in2 (in1 x ) )
Ttnode : TT → TT → TT → TT
Ttnode x y z = lfp (in2 (in2 (x , (y , z ) ) ) )
TtnodeCurried : TT ∧ (TT ∧ TT) → TT
TtnodeCurried (x , (y , z)) = lfp (in2 (in2 (x , (y , z ) ) ) )

allT : ℕ → List TT
allT zero = []
allT (succ n) =
    let un = List→ Tunode (allT n)
        t³ = lazyProd (allT n) (lazyProd (allT n) (allT n))
        tn = List→ TtnodeCurried t³
        in Tleaf ∷ (merge un tn)

==T : TT → TT → 𝔹
==T = ==ADT {T}

-- T pretty printer
data 𝕋 : Set where
  tl : 𝕋
  tu : 𝕋 → 𝕋
  tt : 𝕋 → 𝕋 → 𝕋 → 𝕋

TT→𝕋 : TT → 𝕋
TT→𝕋 (lfp (in1 tt)) = tl
TT→𝕋 (lfp (in2 (in1 x))) = tu (TT→𝕋 x)
TT→𝕋 (lfp (in2 (in2 (x , (y , z))))) = tt (TT→𝕋 x) (TT→𝕋 y) (TT→𝕋 z)

𝕋→TT : 𝕋 → TT
𝕋→TT tl = lfp (in1 tt)
𝕋→TT (tu x) = lfp (in2 (in1 (𝕋→TT x) ) )
𝕋→TT (tt x y z) = lfp (in2 (in2 (𝕋→TT x , (𝕋→TT y , 𝕋→TT z ) ) ) )

-- J = 1 + 2J + J²

j : ADT (↑ ⊥)
j = 𝟏 ⊔ (𝕍 o) ⊔ (𝕍 o) ⊔ (𝕍 o) ²

J : ADT ⊥
J = μ j

JJ : Set
JJ = ⟦ J ⟧ Γ₀

Jleaf : JJ
Jleaf = lfp (in1 tt)
Junode1 : JJ → JJ
Junode1 x = lfp (in2 (in1 x ) )
Junode2 : JJ → JJ
Junode2 x = lfp (in2 (in2 (in1 x)))
Jbnode : JJ → JJ → JJ
Jbnode x1 x2 = lfp (in2 (in2 (in2 (x1 , x2))))
JbnodeCurried : JJ ∧ JJ → JJ
JbnodeCurried (x1 , x2) = lfp (in2 (in2 (in2 (x1 , x2))))

allJ : ℕ → List JJ
allJ zero = []
allJ (succ n) = let
  un1 = List→ Junode1 (allJ n)
  un2 = List→ Junode2 (allJ n)
  allJ² : List (JJ ∧ JJ)
  allJ² = lazyProd (allJ n) (allJ n)
  bn = List→ JbnodeCurried allJ²
  in Jleaf ∷ merge (merge un1 un2) bn

==J : JJ → JJ → 𝔹
==J = ==ADT {J}

-- J pretty printer
data 𝕁 : Set where
  jl : 𝕁
  ju1 : 𝕁 → 𝕁
  ju2 : 𝕁 → 𝕁
  jb : 𝕁 → 𝕁 → 𝕁

J→𝕁 : JJ → 𝕁
J→𝕁 (lfp (in1 tt)) = jl
J→𝕁 (lfp (in2 (in1 x))) = ju1 (J→𝕁 x)
J→𝕁 (lfp (in2 (in2 (in1 x)))) = ju2 (J→𝕁 x)
J→𝕁 (lfp (in2 (in2 (in2 (pr3 , pr4))))) = jb (J→𝕁 pr3) (J→𝕁 pr4)

𝕁→J : 𝕁 → JJ
𝕁→J jl = Jleaf
𝕁→J (ju1 x) = Junode1 (𝕁→J x)
𝕁→J (ju2 x) = Junode2 (𝕁→J x)
𝕁→J (jb x x₁) = Jbnode (𝕁→J x) (𝕁→J x₁)

-- M = 1 + M + M²

m : ADT (↑ ⊥)
m = 𝟏 ⊔ (𝕍 (o)) ⊔ (𝕍 (o)) ²

M : ADT ⊥
M = μ m

M³ : ADT ⊥
M³ = M × M × M

MM : Set
MM = ⟦ M ⟧ Γ₀

MM³ : Set
MM³ = ⟦ M³ ⟧ Γ₀

Mleaf : MM
Mleaf = lfp (in1 tt)
Munode : MM → MM
Munode m = lfp (in2 (in1 m) )
Mbnode : MM → MM → MM
Mbnode m1 m2 = lfp (in2 (in2 ((m1 , m2 )) ) )
MbnodeCurried : MM ∧ MM → MM
MbnodeCurried (m1 , m2) = lfp (in2 (in2 ((m1 , m2 )) ) )

allM : ℕ → List MM
allM² : ℕ → List (MM ∧ MM)
allM zero = []
allM (succ n) = let
  un = List→ Munode (allM n)
  bn = List→ MbnodeCurried (allM² n)
  in Mleaf ∷ merge un bn
allM² n = lazyProd (allM n) (allM n)

allM³ : ℕ → List MM³
allM³ n = lazyProd (allM n) (lazyProd (allM n) (allM n))

==M : MM → MM → 𝔹
==M = ==ADT {M}

==M³ : MM³ → MM³ → 𝔹
==M³ = ==ADT {M³}

-- M pretty printer
data 𝕄 : Set where
  ml : 𝕄
  mu : 𝕄 → 𝕄
  mb : 𝕄 → 𝕄 → 𝕄

𝕄² : Set
𝕄² = 𝕄 ∧ 𝕄

S-alg : ↑ (𝕄² ∨ 𝕄²) → 𝕄²
S-alg  o                        = ml , ml
S-alg (i (in1 (m1 , m2)))       = ml , mb m1 m2
S-alg (i (in2 (m1 , ml)))       = ml , mu m1
S-alg (i (in2 (m1 , mu m2)))    = mu m2 , m1
S-alg (i (in2 (m1 , mb m2 m3))) = mb m2 m3 , m1

_==𝕄_ : 𝕄 → 𝕄 → 𝔹
_==𝕄_ ml ml = true
_==𝕄_ (mu m1) (mu m2) = m1 ==𝕄 m2
_==𝕄_ (mb m11 m12) (mb m21 m22) = and (m11 ==𝕄 m21) (m12 ==𝕄 m22)
_==𝕄_ _ _ = false

_==𝕄²_ : 𝕄² → 𝕄² → 𝔹
(m11 , m12) ==𝕄² (m21 , m22) = (mb m11 m12) ==𝕄 (mb m21 m22)

data 𝕊 : Set where
  so : 𝕊
  sp : 𝕊 → 𝕊
  sq : 𝕊 → 𝕊

S→M² : 𝕊 → 𝕄²
S→M² so = S-alg o
S→M² (sp s) = S-alg (i (in1 (S→M² s)))
S→M² (sq s) = S-alg (i (in2 (S→M² s)))

all𝕊 : ℕ → List 𝕊
all𝕊 0 = []
all𝕊 (succ n) = so ∷ merge (List→ sp (all𝕊 n)) (List→ sq (all𝕊 n))

M→𝕄 : MM → 𝕄
M→𝕄 (lfp (in1 tt)) = ml
M→𝕄 (lfp (in2 (in1 x))) = mu (M→𝕄 x)
M→𝕄 (lfp (in2 (in2 (pr3 , pr4)))) = mb (M→𝕄 pr3 ) (M→𝕄 pr4)

𝕄→M : 𝕄 → MM
𝕄→M ml = lfp (in1 tt)
𝕄→M (mu mm) = lfp (in2 (in1 (𝕄→M mm) ))
𝕄→M (mb mm1 mm2) = lfp (in2 (in2 ((𝕄→M mm1) , 𝕄→M mm2 ) ))

M²→𝕄² : MM ∧ MM → 𝕄²
M²→𝕄² (m1 , m2) = M→𝕄 m1 , M→𝕄 m2
𝕄²→M² : 𝕄² → MM ∧ MM
𝕄²→M² (m1 , m2) = 𝕄→M m1 , 𝕄→M m2

M³→𝕄 : MM³ → (𝕄 ∧ (𝕄 ∧ 𝕄))
M³→𝕄 (m1 , (m2 , m3)) = M→𝕄 m1 , (M→𝕄 m2 , M→𝕄 m3 )

𝕄→M³ : (𝕄 ∧ (𝕄 ∧ 𝕄)) → MM³
𝕄→M³ (m1 , (m2 , m3)) = (𝕄→M m1 ) , (𝕄→M m2 , 𝕄→M m3 )

findCycleHelper : 𝕄² → 𝕄² → ℕ → ↑ 𝕊
findCycleHelper init cur zero     = if init ==𝕄² cur then i so else o
findCycleHelper init cur (succ k)
  with init ==𝕄² cur
... | true  = i so
... | false
  with findCycleHelper init (S-alg (i (in1 cur))) k
     | findCycleHelper init (S-alg (i (in2 cur))) k
... | o | o     = o
... | o | (i s) = i (sq s)
... | (i s) | _ = i (sp s)

findCycle : 𝕄² → ↑ 𝕊
findCycle mm = io (i ∘ sq) ((↑→ sp (findCycleHelper mm mm2 d))) (↑→ sp (findCycleHelper mm mm1 d)) where
  mm1 = S-alg (i (in1 mm))
  mm2 = S-alg (i (in2 mm))
  d = 10 -- depth



testS : Set
testS = ⊤ where
    -- {! e11    !} where
    -- e0 = (lfp (in2 (in1 (lfp (in1 tt)))) , lfp (in1 tt))
    SHOW = List→ M²→𝕄²
    e1 : List 𝕊
    e1 = all𝕊 20
    e2 : List (MM ∧ MM)
    e2 = allM² 4
    e3 : List 𝕄²
    e3 = List→ S→M² e1
    e4 : List (MM ∧ MM)
    e4 = filter (λ mm → elem (_==𝕄²_) (M²→𝕄² mm) e3 ) e2
    e5 : List 𝕄²
    e5 = SHOW (take 1 e4)
    e6 = SHOW (take 10 e2)
    e7 = SHOW (take 20 e4)
    e71 = SHOW (take 50 e4)
    e8 = List→ (λ mm → or (mm ==𝕄² S-alg (i (in1 mm))) (mm ==𝕄²  S-alg (i (in2 mm)))) e7
    e9 = List→ (λ mm → mm ==𝕄²  S-alg (i (in2 mm))) e7
    e10 = List→ (λ mm → or (mm ==𝕄² S-alg (i (in2 mm))) (mm ==𝕄²  S-alg (i (in2 (S-alg (i (in2 mm))))))) e7
    e11 = List→ findCycle e71
{-
e11 output:
i (sp so) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp so) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
o ∷
i (sp so) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
i (sp (sq so)) ∷
o ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷
o ∷
i (sp (sq so)) ∷ o ∷ i (sp (sq so)) ∷ o ∷ i (sp (sq so)) ∷ o ∷ []
-}

-- 2M = 1 + (1 + 2M + 2M²) + 2M²
2m : ADT (↑ ⊥)
2m = 𝟏 ⊔ m ⊔ (𝕍 o) ²

2M : ADT ⊥
2M = μ 2m
--
-- allJ zero = []
-- allJ (succ n) = let
--   un1 = List→ Junode1 (allJ n)
--   un2 = List→ Junode2 (allJ n)
--   allJ² : List (JJ ∧ JJ)
--   allJ² = lazyProd (allJ n) (allJ n)
--   bn = List→ JbnodeCurried allJ²
--   in Jleaf ∷ merge (merge un1 un2) bn

2MM : Set
2MM = ⟦ 2M ⟧ Γ₀

2mleaf1 : 2MM
2mleaf1 = lfp (in1 tt )
2mleaf2 : 2MM
2mleaf2 = lfp (in2 (in1 (in1 tt ) ) )
2munode : 2MM → 2MM
2munode 2mm = lfp (in2 (in1 (in2 (in1 2mm ) ) ) )
2mbnode1 : 2MM → 2MM → 2MM
2mbnode1 2mm1 2mm2 = lfp (in2 (in1 (in2 (in2 (2mm1 , 2mm2 ) ) ) ) )
2mbnode2 : 2MM → 2MM → 2MM
2mbnode2 2mm1 2mm2 = lfp (in2 (in2 (2mm1 , 2mm2 ) ) )
2mbnode1Curried : 2MM ∧ 2MM → 2MM
2mbnode1Curried (x , y) = lfp (in2 (in1 (in2 (in2 (x , y) ) ) ) )
2mbnode2Curried : 2MM ∧ 2MM → 2MM
2mbnode2Curried (x , y) = lfp (in2 (in2 (x , y) ) )

all2M : ℕ → List 2MM
all2M zero = []
all2M (succ n) = let
  un = List→ 2munode (all2M n)
  bn1 = List→ 2mbnode1Curried (lazyProd (all2M n) (all2M n))
  bn2 = List→ 2mbnode2Curried (lazyProd (all2M n) (all2M n))
  in 2mleaf1 ∷ 2mleaf2 ∷ merge un (merge bn1 bn2)
