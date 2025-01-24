module QADT.Examples2 where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment

b : ADT 1
b = 1+ (𝕧₀ ²)

t : ADT 1
t = 1+ (𝕧₀ ⊔ (𝕧₀ ³))

B : ADT 0
B = μ b

T : ADT 0
T = μ t

BB : Set
BB = ⟦ B ⟧ Γ₀

TT : Set
TT = ⟦ T ⟧ Γ₀

Bleaf : BB
Bleaf = lfp (in1 tt)
Bnode : BB → BB → BB
Bnode x y = lfp (in2 (x , y))
BnodeCurried : BB ∧ BB → BB
BnodeCurried (x , y) = lfp (in2 (x , y))

Tleaf : TT
Tleaf = lfp (in1 tt)
Tunode : TT → TT
Tunode x = lfp (in2 (in1 x ) )
Ttnode : TT → TT → TT → TT
Ttnode x y z = lfp (in2 (in2 (x , (y , z ) ) ) )
TtnodeCurried : TT ∧ (TT ∧ TT) → TT
TtnodeCurried (x , (y , z)) = lfp (in2 (in2 (x , (y , z ) ) ) )

allB : ℕ → List BB
allB 0 = []
allB (succ n) =
  let b² = lazyProd (allB n) (allB n)
      bn = List→ BnodeCurried b²
      in Bleaf ∷ bn

allT : ℕ → List TT
allT zero = []
allT (succ n) =
    let un = List→ Tunode (allT n)
        t³ = lazyProd (allT n) (lazyProd (allT n) (allT n))
        tn = List→ TtnodeCurried t³
        in Tleaf ∷ (merge un tn)

==B : BB → BB → 𝔹
==B = ==ADT {B}

==T : TT → TT → 𝔹
==T = ==ADT {T}




tB=B : Iso (t [ B ]) B
tB=B = ~~ (fix≃ b =!= += (×= (fix≃ b) =!= dl= (=+ i×r ) ) )

T→B : ⟦ T ⟧ Γ₀  → ⟦ B ⟧ Γ₀
T→B = foldADT t (λ ()) (⟦ B ⟧ Γ₀) ((_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ )))
-- foldT (⟦ B ⟧ Γ₀) (_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ ) )

tB=Bv2 : Iso (t [ B ]) B
tB=Bv2 = ~~ (fix≃ b =!= += (=× (fix≃ b) =!= dr= (cong+ i×l a× ) ) )

T→Bv2 : TT → BB
T→Bv2 = RigFold t B tB=Bv2

-- Sanity Check
tB=Bv3 : Iso (t [ B ]) B
tB=Bv3 = += (=+ i×r ~!~ dl ) =!= (+= (×= ( fix≃ b ) ) ~!= ~~ (fix≃ b) )

T→Bv3 : TT → BB
T→Bv3 = RigFold t B tB=Bv3

tB=Bv4 : Iso (t [ B ]) B
tB=Bv4 = ~~ (fix≃ b =!= += (=× (fix≃ b) =!= dr= (cong+ i×l c× ) ) )

T→Bv4 : TT → BB
T→Bv4 = RigFold t B tB=Bv4

tB=Bv5 : Iso (t [ B ]) B
tB=Bv5 = ~~ (fix≃ b =!= += (c×= (=× (fix≃ b) =!= dr= (cong+ i×l a× ) ) ) )

T→Bv5 : TT → BB
T→Bv5 = RigFold t B tB=Bv5

tB=Bv6 : Iso (t [ B ]) B
tB=Bv6 = ~~ (fix≃ b =!= += (c×= (=× (fix≃ b) =!= dr= (cong+ i×l c× ) ) ) )

T→Bv6 : TT → BB
T→Bv6 = RigFold t B tB=Bv6

findB : BB → ℕ → 𝔹
findB b n = elem ==B b (List→ T→Bv5 (allT n))

someB : List BB
someB = take 50 (allB 5)

passN : ℕ → List BB
passN zero = someB
passN (succ n) = filter (λ x → findB x (succ n)) (passN n)

passN1 : ℕ → List BB
passN1 x = filter (λ y → findB y x ) someB

-- B pretty printer
data ppB : Set where
  lf : ppB
  bn : ppB → ppB → ppB

-- T pretty printer
data 𝕋 : Set where
  tl : 𝕋
  un : 𝕋 → 𝕋
  tn : 𝕋 → 𝕋 → 𝕋 → 𝕋

BB→ppB : BB → ppB
BB→ppB (lfp (in1 tt)) = lf
BB→ppB (lfp (in2 (x , y))) = bn (BB→ppB x ) (BB→ppB y)

TT→𝕋 : TT → 𝕋
TT→𝕋 (lfp (in1 tt)) = tl
TT→𝕋 (lfp (in2 (in1 x))) = un (TT→𝕋 x)
TT→𝕋 (lfp (in2 (in2 (x , (y , z))))) = tn (TT→𝕋 x) (TT→𝕋 y) (TT→𝕋 z)

testonto : Set
testonto = {! passN1 5  !}

test54 : Set
test54 = {! List→ BB→ppB (List→ T→Bv6 (take 100 (allT 5)))  !}

bB⁵=B⁵ : Iso (1+ (B ⁵) ²) (B ⁵)
bB⁵=B⁵ = ~~ (=× (fix≃ b) =!= dr= {!   !} )
