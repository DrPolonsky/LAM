module QADT.Examples.T=B where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

tB=B : Iso (subst t B) B
tB=B = ~~ (fix≃ b =!= += (×= (fix≃ b) =!= dl= (=+ i×r ) ) )

T→B : ⟦ T ⟧ Γ₀  → ⟦ B ⟧ Γ₀
T→B = foldADT t (λ ()) (⟦ B ⟧ Γ₀) ((_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ )))
-- foldT (⟦ B ⟧ Γ₀) (_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ ) )

tB=Bv2 : Iso (subst t B) B
tB=Bv2 = ~~ (fix≃ b =!= += (=× (fix≃ b) =!= dr= (cong+ i×l a× ) ) )

T→Bv2 : TT → BB
T→Bv2 = RigFold t B tB=Bv2

-- Sanity Check
tB=Bv3 : Iso (subst t B) B
tB=Bv3 = += (=+ i×r ~!~ dl ) =!= (+= (×= ( fix≃ b ) ) ~!= ~~ (fix≃ b) )

T→Bv3 : TT → BB
T→Bv3 = RigFold t B tB=Bv3

tB=Bv4 : Iso (subst t B) B
tB=Bv4 = ~~ (fix≃ b =!= += (=× (fix≃ b) =!= dr= (cong+ i×l c× ) ) )

T→Bv4 : TT → BB
T→Bv4 = RigFold t B tB=Bv4

tB=Bv5 : Iso (subst t B) B
tB=Bv5 = ~~ (fix≃ b =!= += (c×= (=× (fix≃ b) =!= dr= (cong+ i×l a× ) ) ) )

T→Bv5 : TT → BB
T→Bv5 = RigFold t B tB=Bv5

tB=Bv6 : Iso (subst t B) B
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





testonto : Set
testonto = {! passN1 5  !}

test54 : Set
test54 = {! List→ BB→ppB (List→ T→Bv6 (take 100 (allT 5)))  !}

bB⁵=B⁵ : Iso (1+ (B ⁵) ²) (B ⁵)
bB⁵=B⁵ = ~~ (=× (fix≃ b) =!= dr= {!   !} )
