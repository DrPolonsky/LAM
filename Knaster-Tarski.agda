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

module KleeneFresh {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (Δcont : isCont) where

  s-acc : ∀ (d : D) → is R -accessible d → 𝓟 S
  s-acc d (acc dacc) = ⋃ sa where
    sa : (Σ[ i ∈ D ] R i d) → 𝓟 S
    sa (i ,, Rid) = Δ (s-acc i (dacc i Rid))

  s : D → 𝓟 S
  s d = s-acc d (wfR d)

  ⋃Δ : 𝓟 S
  ⋃Δ = ⋃ s

  s-acc-irrel : ∀ {d : D} → (da1 da2 : is R -accessible d) → s-acc d da1 ⊆ s-acc d da2
  s-acc-irrel (acc da1) (acc da2) = ⋃-mono _ _ f where
    f = λ {(i ,, Rid) x → Δ⊆ (s-acc-irrel (da1 i Rid) (da2 i Rid)) x}

  s-mono-acc :  ∀ {i j : D} → (ia : is R -accessible i) → R i j → s-acc i ia ⊆ s j
  s-mono-acc {i} {j} acci Rij x x∈⋃ with acci | x∈⋃
  ... | acc ia | Sup (d ,, Rdi) .x x∈sad with wfR j
  ... | acc ja = Sup (i ,, Rij) x (Δ⊆ f x x∈sad)
    where f = λ z z∈sd → s-acc-irrel (wfR i) (ja i Rij) z (s-mono-acc (ia d Rdi) Rdi z z∈sd)

  s-mono :  ∀ {i j : D} → R i j → s i ⊆ s j
  s-mono {i} = s-mono-acc (wfR i)

  ⋃Δ-preFP : preFP ⋃Δ
  ⋃Δ-preFP x x∈Δ⋃ with Δcont R wfR s s-mono x x∈Δ⋃
  ... | Sup d .x x∈Δsd = {!    !}

  ⋃Δ-postFP-acc : ∀ i (iacc : is R -accessible i) → s-acc i iacc ⊆ ⋃ (λ z → Δ (s z))
  ⋃Δ-postFP-acc i (acc Hi) x (Sup (d ,, Rdi) .x x∈sad) = Sup d x (Δ⊆ (s-acc-irrel (Hi d Rdi) (wfR d)) x x∈sad)

  ⋃Δ-postFP : ∀ x → x ∈ ⋃Δ → x ∈ Δ (⋃Δ)
  ⋃Δ-postFP x (Sup d .x x∈sd) = monoPreCont R wfR s s-mono x (⋃Δ-postFP-acc d (wfR d) x x∈sd )



module KleeneAcc {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (Δcont : isCont) where
  seq-helper : ∀ (d : D) → is R -accessible d → 𝓟 S
  seq-helper d (acc H) = ⋃ seq where
    seq : D → 𝓟 S
    seq d' = λ x → ∀ (Rd'd : R d' d) → Δ (seq-helper d' (H d' Rd'd)) x

  seq-helper-mono : ∀ (d : D) (da1 da2 : is R -accessible d) → seq-helper d da1 ⊆ seq-helper d da2
  seq-helper-mono d (acc H1) (acc H2) = ⋃-mono _ _ seq-mono where
    seq-mono = λ d' x x∈S1 Rd'd → Δ⊆ (seq-helper-mono d' (H1 d' Rd'd) (H2 d' Rd'd)) x (x∈S1 Rd'd ) --

  s : D → 𝓟 S
  s d = seq-helper d (wfR d)

  s-mono :  ∀ {i j : D} → R i j → s i ⊆ s j
  s-mono {i} {j} Rij x x∈si with wfR j
  ... | acc Hj = Sup j x (λ Rjj → ∅ (wf→irrefl R wfR j Rjj))

  s-mono-acc : ∀ (i : D) → Δ (s i) ⊆ ⋃ s
  s-mono-acc = {!   !}
  -- s-mono-acc i = s-mono-acc-helper i (wfR i) where
  --   s-mono-acc-helper : ∀ (j : D) (ai : is R -accessible j) → Δ (s j) ⊆ ⋃ s
  --   s-mono-acc-helper j (acc Hj) x x∈Δsj with Δcont R wfR {!   !} {!   !} x {!   !}
  --   ... | Sup k .x x∈Δseq = s-mono-acc-helper j (acc Hj) x (Δ⊆ (λ y Rkd → {!   !} ) x x∈Δseq)

  -- s-mono-acc i (acc Hi) x x∈Δsi with wfR i
  -- ... | acc Hi' = let
  --      Δc = Δcont R wfR s s-mono x (Δ⊆ (λ z z∈⋃ → Sup i z (seq-helper-mono i (acc Hi') (wfR i) z z∈⋃)) x x∈Δsi)
  --      rc : ∀ y → R y i → Δ (s y) ⊆ ⋃ s
  --      rc y Ryi = s-mono-acc y (Hi y Ryi)
  --   in Sup i x {!   !}

  ⋃Δ : 𝓟 S
  ⋃Δ = ⋃ s

  ⋃Δ-preFP : preFP ⋃Δ
  ⋃Δ-preFP x x∈Δ⋃Δ  with Δcont R wfR s s-mono x x∈Δ⋃Δ
  ... | H = ⋃-lub (λ x₁ → Δ (seq-helper x₁ (wfR x₁))) (⋃ (λ d → seq-helper d (wfR d))) inc x H
    where inc = λ d y y∈Δsd → {!   !} --  s-mono-acc d y y∈Δsd

  ⋃Δ-postFP : ∀ x → x ∈ ⋃Δ → x ∈ Δ (⋃Δ)
  ⋃Δ-postFP x (Sup d .x x∈sd) = monoPreCont R wfR s s-mono x {!   !}

  ⋃Δ-postFP-acc : ∀ i → (is R -accessible i) → s i ⊆ ⋃ (λ z → Δ (s z))
  ⋃Δ-postFP-acc i (acc Hi) x x∈si with wfR i
  ... | acc Hi' = ⋃-lub _ (⋃ (λ z → Δ (seq-helper z (wfR z))))
                          (λ j y → λ KT → ⋃Δ-postFP-acc j {!   !} y (myFun j y KT))
                          x x∈si
              where myFun = λ j y KT →  {!   !}

  ⋃Δ-FP : FP ⋃Δ
  ⋃Δ-FP = ⋃Δ-preFP , ⋃Δ-postFP
  -- ⋃Δ-LFP : ∀ {Y} → preFP Y → ⋃Δ ⊆ Y
  -- ⋃Δ-LFP {Y} preFPY x x∈⋃Δ = preFPY x (Δ⊆ {!   !} x {!   !})
