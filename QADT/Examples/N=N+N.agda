open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
-- open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.N=N+N where


f : ADT (↑ ⊥)
f = 𝟏 ⊔ 𝕧₀

g : ADT (↑ ⊥)
g = 𝟏 ⊔ 𝟏 ⊔ 𝕧₀

F : ADT ⊥
F = μ f

G : ADT ⊥
G = μ g

gF=F : Iso (subst g (F)) F
gF=F = ~~ (fix≃ _ =!= += (fix≃ _) )

gF=Fv2 : Iso (subst g (F)) F
gF=Fv2 = a+ ~!= (=+ c+ =!= a+= gF=F )

gF=Fv3 : Iso (subst g (F)) F
gF=Fv3 = {!   !}

G→F : ⟦ G ⟧ Γ₀ → ⟦ F ⟧ Γ₀
G→F = RigFold g F gF=F

G→Fv2 : ⟦ G ⟧ Γ₀ → ⟦ F ⟧ Γ₀
G→Fv2 = RigFold g F gF=Fv2

data 𝔾 : Set where
  Z : 𝔾
  Z' : 𝔾
  S : 𝔾 → 𝔾

𝔾→G : 𝔾 → ⟦ G ⟧ Γ₀
𝔾→G Z = lfp (in2 (in1 tt))
𝔾→G Z' = lfp (in1 tt)
𝔾→G (S x) = lfp (in2 (in2 (𝔾→G x) ) )

F→ℕ : ⟦ F ⟧ Γ₀ → ℕ
F→ℕ (lfp (in1 tt)) = 0
F→ℕ (lfp (in2 x)) = succ (F→ℕ x)

ℕ→𝔾 : ℕ → 𝔾
ℕ→𝔾 zero = Z
ℕ→𝔾 (succ zero) = Z'
ℕ→𝔾 (succ (succ n)) = S (ℕ→𝔾 n )

ℕ→G : ℕ → ⟦ G ⟧ Γ₀
ℕ→G = 𝔾→G ∘ ℕ→𝔾

[1-n]G : ℕ → List (⟦ G ⟧ Γ₀)
[1-n]G zero = []
[1-n]G (succ n) = ℕ→G n ∷ [1-n]G n

check5 : Set
check5 = {! List→ (F→ℕ ∘ G→F) ([1-n]G 30)  !}
