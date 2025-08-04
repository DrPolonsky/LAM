open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment

module QADT.Examples.IsoNeqExample where

𝔹≃𝔹₁ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₁ = !!
𝔹≃𝔹₂ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₂ = a+ ~!= i+r= (c+= (+= (~~ i+r) ) )

𝔹1≠𝔹2 : ¬ (≃⟦ 𝔹≃𝔹₁ ⟧ Γ₀ ≡ ≃⟦ 𝔹≃𝔹₂ ⟧ Γ₀)
𝔹1≠𝔹2 i1=i2 = iso≠lemma (≃⟦ 𝔹≃𝔹₁ ⟧ Γ₀) (≃⟦ 𝔹≃𝔹₂ ⟧ Γ₀) (in1 tt) (λ {()} ) i1=i2
