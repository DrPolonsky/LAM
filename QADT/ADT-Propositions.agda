module QADT.ADT-Propositions where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import Environment
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms

module X=nPX+X {V : Set} (a : ADT (↑ V)) (ρ₀ : SetEnv V) where

  f : ADT (↑ V)
  f = a ⊔ 𝕧₀

  g : ℕ → ADT (↑ V)
  g k = (Num k × a) ⊔ 𝕧₀

  F : ADT V
  F = μ f
  G : ℕ → ADT V
  G k = μ (g k)

  _≃!≃_ = _iso∘_

  FisG : ∀ (X : Set) (k : ℕ) → (⟦ f ⟧ (ρ₀ ⅋o:= X)) ≃ X → ((⟦ g k ⟧ (ρ₀ ⅋o:= X)) ≃ X)
  FisG X zero fX=X = iso∨ (comm∧ ≃!≃ annih∧ ) (id≃ X ) ≃!≃ iso~ id∨
  FisG X (succ k) fX=X =
    let reccall = FisG X k fX=X
     in ((iso∨ isodistrR (id≃ _) iso∘ iso∨ (iso∨ (iso~ id∧) (id≃ _) ) (id≃ _)  ) iso∘ (iso~ assoc∨  ≃!≃ (iso∨ (id≃ _ ) comm∨ ≃!≃ (assoc∨ ≃!≃ (iso∨ fX=X (id≃ _) ≃!≃ comm∨ ) )) ) ) ≃!≃ reccall
