open import Predicates
open import Logic-Levels
open import Wellfounded
open import RelationsCore

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

isContBad : isCont → Δ K⊥ ⊆ K⊥
isContBad isC x = i3 x ∘ (i2 x ∘ i1 x) where
      i1 = Δ⊆ {K⊥} {⋃ (K K⊥)} (⊥⊆ (⋃ (K K⊥)))
      i2 = isC K⊥ (λ x → ∅ x) (K K⊥) ∅
      i3 = ⋃-empty (λ x → Δ (K K⊥ x))

module KleeneFresh {D : Set} (R : 𝓡 D) (wfR : isWFacc R) (Δcont : isCont) where

  s-acc : ∀ (d : D) → is R -accessible d → 𝓟 S
  s-acc d (acc dacc) = ⋃ sa where
    sa : (Σ[ i ∈ D ] R i d) → 𝓟 S
    sa (i ,, Rid) = Δ (s-acc i (dacc i Rid))

  s : D → 𝓟 S
  s d = s-acc d (wfR d)

  ⋃s : 𝓟 S
  ⋃s = ⋃ s

  ⋃s-ub : ∀ d → s d ⊆ ⋃s
  ⋃s-ub = Sup
  ⋃s-lub : ∀ {P : 𝓟 S} (P-ub : ∀ d → s d ⊆ P) → ⋃s ⊆ P
  ⋃s-lub P-ub x (Sup d .x x∈sd) = P-ub d x x∈sd

  s-acc-irrel : ∀ {d : D} → (da1 da2 : is R -accessible d) → s-acc d da1 ⊆ s-acc d da2
  s-acc-irrel (acc da1) (acc da2) = ⋃-mono _ _ f where
    f = λ {(i ,, Rid) x → Δ⊆ (s-acc-irrel (da1 i Rid) (da2 i Rid)) x}

  s-acc-bad : ∀ d (dacc : is R -accessible d) → s-acc d dacc ⊆ K⊥
  s-acc-bad d (acc da) x (Sup (j ,, Rjd) .x x∈sj) with da j Rjd
  ... | acc ja = isContBad Δcont x (Δ⊆ (⋃-lub _ K⊥ f) x x∈sj) -- s-acc-bad j (da j Rjd) x {!   !}
    where f : _
          f (i ,, Rij) z z∈si with wfR j
          ... | acc ja0 = s-acc-bad j (da j Rjd) z
                  (s-acc-irrel (acc ja0) (da j Rjd) z (Sup (i ,, Rij) z (Δ⊆ (s-acc-irrel (ja i Rij) (ja0 i Rij) ) z z∈si)) )

  ⋃s-bad : ⋃s ⊆ K⊥
  ⋃s-bad = ⋃-lub s K⊥ (λ d x → s-acc-bad d (wfR d) x)

  ⋃s-ub-acc : ∀ d (dacc : is R -accessible d) → s-acc d dacc ⊆ ⋃s
  ⋃s-ub-acc d dacc x x∈sd = ⋃s-ub d x (s-acc-irrel dacc (wfR d) x x∈sd )

  s-mono-acc :  ∀ {i j : D} → (ia : is R -accessible i) → R i j → s-acc i ia ⊆ s j
  s-mono-acc {i} {j} acci Rij x x∈⋃ with acci | x∈⋃
  ... | acc ia | Sup (d ,, Rdi) .x x∈sad with wfR j
  ... | acc ja = Sup (i ,, Rij) x (Δ⊆ f x x∈sad)
    where f = λ z z∈sd → s-acc-irrel (wfR i) (ja i Rij) z (s-mono-acc (ia d Rdi) Rdi z z∈sd)

  s-mono :  ∀ {i j : D} → R i j → s i ⊆ s j
  s-mono {i} = s-mono-acc (wfR i)

  module LiftedRel where
    open import Lifting

    𝓡↑ : ∀ {X} → 𝓡 X → 𝓡 (↑ X)
    𝓡↑ Q o _ = ⊥
    𝓡↑ Q (i x) o =  ⊤
    𝓡↑ Q (i x) (i y) = Q x y

    R↑ : 𝓡 (↑ D)
    R↑ = 𝓡↑ R

    isAcci : ∀ x → is R -accessible x → is R↑ -accessible (i x)
    isAcci x (acc xa) = acc yR↑acc where
      yR↑acc : ∀ (y : ↑ D) → R↑ y (i x) → is R↑ -accessible y
      yR↑acc (i y) R↑yx = isAcci y (xa y R↑yx)

    isAcco : is R↑ -accessible o
    isAcco = acc oacc where
      oacc : ∀ (y : ↑ D) → R↑ y o → is R↑ -accessible y
      oacc (i x) tt = isAcci x (wfR x)

    R↑wf : isWFacc R↑
    R↑wf (i x) = isAcci x (wfR x)
    R↑wf o = isAcco

    s↑ : ↑ D → 𝓟 S
    s↑ (i x) = s x
    s↑ o = ⋃ s

    s↑mono : ∀ {x y : ↑ D} → R↑ x y → s↑ x ⊆ s↑ y
    s↑mono {i x} {i y} R↑xy a a∈s↑x = s-mono R↑xy a a∈s↑x
    s↑mono {i x} {o} tt a a∈s↑x = Sup x a a∈s↑x

    ⋃s↑ : Δ (⋃ s↑) ⊆ ⋃ (λ z → Δ (s↑ z))
    ⋃s↑ x x∈Δ⋃s↑ = Δcont {↑ D} R↑ R↑wf s↑ (λ {a} → s↑mono {a} ) x x∈Δ⋃s↑

  ⋃s-preFP-acc : ∀ (i : D) (iacc : is R -accessible i) → Δ (s-acc i iacc) ⊆ ⋃s
  ⋃s-preFP-acc i (acc ia) x x∈Δsi = {!   !}
{-
  ⋃s-preFP-acc : ∀ (i : D) (iacc : is R -accessible i) → Δ (s-acc i iacc) ⊆ ⋃s
  ⋃s-preFP-acc i (acc ia) x x∈Δsi =
    let inc = λ {y (Sup (j ,, Rji) .y y∈sj) → ⋃s-preFP-acc j (ia j Rji) y y∈sj  }
        cont = Δcont R wfR s s-mono x (Δ⊆ inc x x∈Δsi)
    --     g = λ { y (Sup (k ,, Rki) .y y∈si) → Sup k y (λ Rji → {!   !} ) }
    --     contΣ = Δcont R wfR (λ j y → ∀ (Rji : R j i) → s-acc j (ia j Rji) y)
    --             (λ {z} {y} Rzy s sa Ryi → {! acc  !} ) x ((Δ⊆ g x x∈Δsi))
        -- contΣ = Δcont {Σ[ y ∈ D ] R y i} (λ { (y1 ,, _) (y2 ,, _) → R y1 y2 }) {!   !}
        --                 (λ {(y ,, _) → s y}) s-mono x (Δ⊆ (λ z z∈⋃ → {!   !} ) x x∈Δsi)
     in ⋃-lub (λ d → Δ (s d)) ⋃s {!   !} x cont -- inc x {!   !} -- (⋃-lub (λ z → Δ (s z)) (λ w → Σ[ ρ ] R w i) → w ∈ ⋃s) {!   !} x ?
     -- in ⋃-lub (λ d → Δ (s d)) ⋃s (λ d z z∈Δsd → ⋃s-ub-acc d (wfR d) z {!   !} ) x cont -- inc x {!   !} -- (⋃-lub (λ z → Δ (s z)) (λ w → Σ[ ρ ] R w i) → w ∈ ⋃s) {!   !} x ?
     -- in inc x (⋃-lub (λ z → Δ (s z)) {! λ w → ∀ (ρ : R w i) → w ∈ ⋃s  !}  {!   !} x cont)

  -- ⋃s-preFP-acc i (acc ia) x x∈Δsi with Δcont R wfR s s-mono x (Δ⊆ inc x x∈Δsi)
  --   where inc : _
  --         inc = {!   !} -- λ {y (Sup (j ,, Rji) .y y∈sj) → ⋃s-preFP-acc j (ia j Rji) y y∈sj  }
  -- ... | Sup d .x x∈Δsd = {!   !}
  -- -- ... | Sup d .x x∈Δsd = ⋃s-preFP-acc d (ia d {!   !} ) x
  -- --                                     (Δ⊆ (s-acc-irrel (wfR d) (ia d _)) x x∈Δsd)
-}
  ⋃s-preFP : preFP ⋃s
  ⋃s-preFP x x∈Δ⋃ with Δcont R wfR s s-mono x x∈Δ⋃
  ... | Sup d .x x∈Δsd = ⋃s-preFP-acc d (wfR d) x x∈Δsd

  ⋃s-postFP-acc : ∀ i (iacc : is R -accessible i) → s-acc i iacc ⊆ ⋃ (λ z → Δ (s z))
  ⋃s-postFP-acc i (acc Hi) x (Sup (d ,, Rdi) .x x∈sad) = Sup d x (Δ⊆ (s-acc-irrel (Hi d Rdi) (wfR d)) x x∈sad)

  -- ⋃s-postFP : ∀ x → x ∈ ⋃s → x ∈ Δ (⋃s)
  ⋃s-postFP : ⋃s ⊆ Δ (⋃s)
  ⋃s-postFP x (Sup d .x x∈sd) = monoPreCont R wfR s s-mono x (⋃s-postFP-acc d (wfR d) x x∈sd )
