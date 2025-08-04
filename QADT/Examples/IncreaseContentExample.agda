open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
-- open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.IncreaseContentExample where


p : ADT (↑ ⊥)
p = 𝕧₀ ² ⊔ 𝟏

z : ADT (↑ ⊥)
z = p ⊔ 𝕧₀

2z : ADT (↑ ⊥)
2z = Num 2 × p ⊔ 𝕧₀

Z : ADT ⊥
Z = μ z

2Z : ADT ⊥
2Z = μ 2z

2zZ=Z : Iso (subst 2z (Z)) Z
2zZ=Z = =+ (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) !!) ) =!= a+= (+= (~~ (fix≃ z) ) =!= ~~ (fix≃ z) )

2Z→Z : ⟦ 2Z ⟧ Γ₀ → ⟦ Z ⟧ Γ₀
2Z→Z = RigFold 2z Z 2zZ=Z

chec : Set
chec = {! List- (==ADT {Z}) (EnumADTk Z Γ₀ EnumΓ₀ 4) (List→ 2Z→Z (EnumADTk 2Z Γ₀ EnumΓ₀ 4))  !}

chec2 : Set
chec2 = {! length (EnumADTk Z Γ₀ EnumΓ₀ 4)  !}

-- Example 2

Ψ : ADT (↑ ⊥)
Ψ = p ⊔ 𝕧₀

ϕ : ADT (↑ ⊥)
ϕ = Num 3 × p ⊔ 𝕧₀

μϕ : ADT ⊥
μϕ = μ ϕ

μΨ : ADT ⊥
μΨ = μ Ψ

ϕμΨ=μΨ : Iso (subst ϕ (μΨ)) (μΨ)
ϕμΨ=μΨ = =+ (dr= (cong+= i×l (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) !!) ) !!) ) =!= a+= (+= (a+= (+= (a+= (~~ (fix≃ Ψ =!= a+ ) ) ) =!= ~~ (fix≃ Ψ) ) ) =!= ~~ (fix≃ Ψ) )

μϕ→μΨ : ⟦ μϕ ⟧ Γ₀ → ⟦ μΨ ⟧ Γ₀
μϕ→μΨ = RigFold ϕ μΨ ϕμΨ=μΨ

findΨ : ℕ → ⟦ μΨ ⟧ Γ₀ → 𝔹
findΨ n p = elem (==ADT {μΨ}) p (List→ μϕ→μΨ (EnumADTk μϕ Γ₀ EnumΓ₀ n) )

someΨ = take 50 (EnumADTk μΨ Γ₀ EnumΓ₀ 4)

checkCheck : 𝔹
checkCheck = {! isSubset' (eqℕ) ([1-n] 100)  ([1-n] 100000)  !}
