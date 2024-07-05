open import Predicates
open import Logic-Levels
open import Wellfounded

-- Knaster-Tarski Lemma: Let S be a set. If the mapping Δ: 𝓟 (S) → 𝓟 (S) is monotone with respect to
-- ⊆ (property Δ⊆ below), then there exists a smallest Δ-closed set. Moreover, this smallest
-- Δ-closed set coincides with the smallest fixed point of Δ.
module Knaster-Tarski {S : Set} (Δ : 𝓟 S → 𝓟 S) (Δ⊆ : ∀ {X Y : 𝓟 S} → X ⊆ Y → Δ X ⊆ Δ Y) where

preFP : 𝓟 S → Set
preFP X = Δ X ⊆ X
postFP : 𝓟 S → Set
postFP X = X ⊆ Δ X
FP : 𝓟 S → Set
FP X = preFP X × postFP X

-- May need to define it as a datatype: data M : S → Set where ....
{-# NO_POSITIVITY_CHECK #-}
data μΔ : 𝓟 S where
  clos : ∀ (x : S) → x ∈ Δ μΔ → x ∈ μΔ

μΔ-preFP : preFP μΔ
μΔ-preFP = clos
μΔ-postFP : postFP μΔ
μΔ-postFP x (clos .x x∈ΔμΔ) = x∈ΔμΔ
μΔ-FP : FP μΔ
μΔ-FP = μΔ-preFP , μΔ-postFP

{-# TERMINATING #-}
μΔ-LFP : ∀ {Y} → preFP Y → μΔ ⊆ Y
μΔ-LFP {Y} preFPY x (clos .x x∈ΔμΔ) = preFPY x (Δ⊆ (μΔ-LFP preFPY) x x∈ΔμΔ)

-- The smallest Δ closed set is the intersection of all Δ closed sets.
∩Δ : S → Set₁
∩Δ x = ∀ (X : 𝓟 S) → preFP X → X x

∩Δ⊆μΔ : ∀ x → ∩Δ x → μΔ x
∩Δ⊆μΔ x x∈∩Δ = x∈∩Δ μΔ μΔ-preFP
μΔ⊆∩Δ : ∀ x → μΔ x → ∩Δ x
μΔ⊆∩Δ x x∈μΔx = λ X ΔX⊆X → μΔ-LFP ΔX⊆X x x∈μΔx
-- μΔ⊆∩Δ x (clos .x x∈ΔμΔ) = λ X ΔX⊆X → ΔX⊆X x (Δ⊆ (λ y y∈μΔ → μΔ⊆∩Δ y y∈μΔ X ΔX⊆X ) x x∈ΔμΔ)

monoPreCont : ∀ {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (s : D → 𝓟 S)
           (s-mono : ∀ {x y : D} → R x y → s x ⊆ s y)
           → ⋃ (λ x → Δ (s x)) ⊆ Δ (⋃ s)
monoPreCont {D} R wfR s s-mono = ⋃-lub (λ z → Δ (s z)) (Δ (⋃ s)) λ d x → Δ⊆ (⋃-ub s d ) x

isCont : Set₁
isCont = ∀ {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (s : D → 𝓟 S)
           (s-mono : ∀ {x y : D} → R x y → s x ⊆ s y)
           → Δ (⋃ s) ⊆ ⋃ (λ x → Δ (s x))

module Kleene {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (Δcont : isCont) where
      
  seq-helper : ∀ (d : D) → is R -accessible d → 𝓟 S
  seq-helper d (acc H) = ⋃ s where
    s : D → 𝓟 S
    s d' = λ x → ∀ (Rd'd : R d' d) → seq-helper d' (H d' Rd'd) x

  ⋃Δ : 𝓟 S
  ⋃Δ = ⋃ s where s = λ d → seq-helper d (wfR d)

  ⋃Δ-preFP : preFP ⋃Δ
  ⋃Δ-preFP x x∈Δ⋃Δ = {!   !} 
  -- with Δcont R wfR {!   !} {!   !} x x∈Δ⋃Δ
  -- ... | H = {!   !} 
  ⋃Δ-postFP : postFP ⋃Δ
  ⋃Δ-postFP x x∈⋃Δ = monoPreCont R wfR {!   !} {!   !} x {!   !}
  ⋃Δ-FP : FP ⋃Δ
  ⋃Δ-FP = ⋃Δ-preFP , ⋃Δ-postFP
  ⋃Δ-LFP : ∀ {Y} → preFP Y → ⋃Δ ⊆ Y
  ⋃Δ-LFP {Y} preFPY x x∈⋃Δ = preFPY x (Δ⊆ {!   !} x {!   !})
  