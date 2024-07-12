{-# OPTIONS --allow-unsolved-metas #-}

open import Logic-Levels
open import Lifting
open import Predicates
open import RelationsCore

{- 2024.06.28.
  Questions to investigate.
  1. Does ¬¬ R-accessible x → R-accessible x ?
  2. Does ¬¬WFacc R → WFacc R ?
  3. Does WFacc- R → ¬¬WFacc R ?
  4. What's the role of ¬¬-closedness in the implication WFmin→WFind ?
  5. How should the "minimality" concept be changed to be useful?
  6. Does WFseq → WFmin- ?
  -}

module Wellfounded where

module WFDefinitions {A : Set} (R : 𝓡 A) where

  -- 1. DEFINITIONS

  -- An element is R-accessible if all elements R-below it are R-accessible
  data is_-accessible_ : 𝓟 A where
    acc : ∀ {x : A} → (∀ y → R y x → is_-accessible_ y) → is_-accessible_ x

  -- R is well-founded if every element is accessible
  isWFacc : Set
  isWFacc = ∀ (x : A) → is_-accessible_ x

  is_-inductive_ : 𝓟 A → Set
  is_-inductive_ φ = ∀ x → (∀ y → R y x → φ y) → φ x

  -- R is well-founded if every inductive predicate is universally true
  isWFind : Set₁
  isWFind = ∀ (φ : 𝓟 A) → is_-inductive_ φ → ∀ x → φ x

  is_-_-minimal_ : 𝓟 A → 𝓟 A
  -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
  is_-_-minimal_ φ x = x ∈ φ × (∀ y → y ∈ φ → R y x → ⊥)

  -- Well-foundedness defined as: every non-empty subset contains a minimal element
  isWFmin : Set₁
  isWFmin = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

  is_-decreasing_ : 𝓟 (ℕ → A)
  is_-decreasing_ s = ∀ n → ~R R (s n) (s (succ n)) -- xₙ > xₙ₊₁

  -- The classical concept of a well-founded relation [TeReSe]
  isWFseq : Set
  isWFseq = ∀ (s : ℕ → A) → ¬ (is_-decreasing_ s)

  -- 2. Relations between definitions of well-foundedness
  acc⊆ind : ∀ (φ : 𝓟 A) → is_-inductive_ φ → is_-accessible_ ⊆ φ
  acc⊆ind φ φisR-ind x (acc IH) = φisR-ind x (λ y Ryx → acc⊆ind φ φisR-ind y (IH y Ryx) )

  isWFacc→isWFind : isWFacc → isWFind
  isWFacc→isWFind wfAcc φ φ-ind = λ x → acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : isWFind → isWFacc
  isWFind→isWFacc wfInd = wfInd is_-accessible_ (λ x → acc {x})

  -- Weaker notions of well-foundedness (¬¬)

  isWFacc- : Set
  isWFacc- = ∀ x → ¬¬ (is_-accessible_ x)

  isWFmin- : Set₁
  isWFmin- = ∀ (P : 𝓟 A) → ∀ {d : A} → d ∈ P → ¬¬ (Σ[ y ∈ A ] is_-_-minimal_ P y)

  isWFind- : Set₁
  isWFind- = ∀ (φ : 𝓟 A) → (is_-inductive_ φ) → ∀ x → ¬¬ (φ x)

  ¬¬isWFacc→isWFacc- :  ¬¬ (isWFacc) → isWFacc-
  ¬¬isWFacc→isWFacc- ¬¬wfAccR = λ x ¬accx → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  isWFacc-→isWFind- : isWFacc- → isWFind-
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- → isWFacc-
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → is_-accessible_ y) (λ x → acc)

  isWFacc-→isWFmin- : isWFacc- → isWFmin-
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → is_-accessible_ x → ¬¬ Σ[ y ∈ A ] (is_-_-minimal_ P y)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  isWFind-→isWFmin- : isWFind- → isWFmin-
  isWFind-→isWFmin- RisWFind- P {d} d∈P = -- ¬Σmin =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (is_-_-minimal_ P y)
        φ-ind : is_-inductive_ φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin-→isWFseq : isWFmin- → isWFseq
  isWFmin-→isWFseq RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] is_-_-minimal_ B d
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  ¬acc : ∀ {x : A} → ¬ (is_-accessible_ x) → ¬ (∀ y → R y x → is_-accessible_ y)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  wf→irrefl : isWFacc → ∀ x → ¬ R x x
  wf→irrefl RisWF x = go x (RisWF x) where
    go : ∀ y → is_-accessible_ y → ¬ R y y
    go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

open WFDefinitions public

module ClassicalProperties {D : Set} (R : 𝓡 D) where

  isMinDec : D → Set
  isMinDec x = (Σ[ y ∈ D ] R y x) ⊔ (∀ y → ¬ R y x)

  -- Double negation shift for accessibility (element-wise)
  ¬¬ACC : Set
  ¬¬ACC = ∀ {x : D} → ¬¬ (is R -accessible x) → is R -accessible x

  ¬¬acc : ∀ {x : D} → ¬¬ (is R -accessible x) → is R -accessible x
  ¬¬acc {x} ¬¬accx = {!   !}
  -- Non-terminating proof:
  -- ¬¬acc {x} ¬¬accx = acc (λ y Ryx → ¬¬acc (λ ¬accy → ¬¬accx λ {  (acc xa) → ¬accy (xa y Ryx) } ))

  -- Double negation shift for accessibility (global)
  isWFacc-→¬¬isWFacc : ¬¬ACC → isWFacc- R → ¬¬ (isWFacc R)
  isWFacc-→¬¬isWFacc ¬¬ACC RisWFacc- ¬RisWFacc  = ¬RisWFacc λ x → ¬¬ACC (RisWFacc- x)
  -- This follows from the previous one:
  -- isWFacc-→¬¬isWFacc  RisWFacc- ¬RisWFacc = ¬RisWFacc (λ x → ¬¬acc (RisWFacc- x) )

  isWFmin-→¬¬isWFmin : ¬¬ACC → isWFmin- R → ¬¬ (isWFmin R)
  isWFmin-→¬¬isWFmin ¬¬Acc isWFmin- ¬isWFmin = ¬isWFmin (λ P {a} a∈P  → a ,, a∈P , λ b b∈P Rba → isWFmin- P a∈P λ {(c ,, c∈P , cIsMin) → {!   !}})

  isWFacc→isWFmin : (∀ x → isMinDec x) → isWFacc R → isWFmin R
  isWFacc→isWFmin minDec RisWFacc P {d} d∈P = f d d∈P (RisWFacc d) where
    f : ∀ x → x ∈ P → is R -accessible x → _
    f x x∈P (acc xac) = {! f y   !}

  {- TO DELETE:
  isWFind→isWFmin : isWFind R → isWFmin R
  isWFind→isWFmin RisWFind P d∈P =
    let S = Σ[ y ∈ D ] (is R - P -minimal y)
        φ : 𝓟 D
        φ x = x ∈ P → Σ[ y ∈ D ] (y ∈ P × ∀ z → z ∈ P → R z y → S)
        φ-ind : is R -inductive φ
        φ-ind x IH x∈P = {!   !}
      in {!   !} -- RisWFind φ φ-ind _ d∈P

  -- The next two implications are valid only for ¬¬-closed φ
  isWFmin→isWFind- : isWFmin R → isWFind- R
  isWFmin→isWFind- RisWFmin φ φ-ind x ¬φx with RisWFmin (λ y → ¬ φ y) ¬φx
  ... | d ,, (¬φd , d-min) = {!   !}
  -}

  isWFmin→isWFacc- : ¬¬ACC → isWFmin R → isWFacc- R
  isWFmin→isWFacc- ¬¬Acc RisWFmin d ¬disRacc with RisWFmin (λ x → ¬ is R -accessible x) (¬disRacc)
  ... | m ,, ¬misRacc , mismin =
    let f : ¬ ((y : D) → R y m → is R -accessible y) → ¬ ((y : D) → (is R -accessible y → ⊥) → R y m → ⊥)
        f ¬H G = {!   !}
      in f (¬acc R ¬misRacc ) mismin

  isWFmin-→isWFind- : ¬¬ACC → isWFmin- R → isWFind- R
  isWFmin-→isWFind- ¬¬Acc RisWFmin- φ φ-ind x ¬φx = RisWFmin- (λ v → ¬ (φ v)) ¬φx f
    where f : ¬ Σ[ d ∈ D ] is R - (∁ φ) -minimal d
          f (d ,, ¬φd , ¬φ⊆¬↓d) = {!   !}

  isWFseq→isWFmin- : isWFseq R → isWFmin- R
  isWFseq→isWFmin- RisWFseq = {!   !}
  -- isWFseq→isWFmin- RisWFseq P {d} d∈P ¬Σmin = RisWFseq f f-dec where
  --   -- ∀¬min : ∀ x → x ∈ P →
  --   f : ℕ → D
  --   f⊆P : ∀ n → f n ∈ P
  --   f-dec : is R -decreasing f
  --   f zero = d
  --   f (succ n) = {!   !}
  --   f-dec n = {!   !}
  --   f⊆P zero = d∈P
  --   f⊆P (succ n) = {!   !}
   