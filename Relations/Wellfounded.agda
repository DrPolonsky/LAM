{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical

{- 2024.06.28.
  Questions to investigate.
  1. Does ¬¬ R-accessible x → R-accessible x ?
     (This appears not to be the case.
      However, the implication should be valid for all ``definable'' P.)
  2. Does ¬¬WFacc R → WFacc R ?
  3. Does WFacc- R → ¬¬WFacc R ?
    (This is DNS for accessibility.)
  4. What's the role of ¬¬-closedness in the implication WFmin→WFind ?
  5. How should the "minimality" concept be changed to be useful?
  6. Does WFseq → WFmin- ?
  -}

{- 2024.07.25.
  ¬¬-closure of well-foundedness properties should be provable for an
  inductively defined collection of predicates -}

module Relations.Wellfounded where

module WFDefinitions {A : Set} (R : 𝓡 A) where

  -- An element is R-accessible if all elements R-below it are R-accessible
  data is_-accessible_ : 𝓟 A where
    acc : ∀ {x : A} → (∀ y → R y x → is_-accessible_ y) → is_-accessible_ x

  -- R is well-founded if every element is accessible
  isWFacc : Set
  isWFacc = ∀ (x : A) → is_-accessible_ x

  -- A predicate φ is R-inductive if:
  --   φ x is true whenever φ y is true for all elements y R-below x.
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

  -- Like isWFmin, but restricted to ¬¬-closed predicates
  isWFmin₀ : Set₁
  isWFmin₀ = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

  -- Like isWFmin, but restricted to decidable predicates
  isWFmin₁ : Set₁
  isWFmin₁ = ∀ (P : 𝓟 A) → dec P → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

  is_-increasing_ : 𝓟 (ℕ → A)
  is_-increasing_ s = ∀ n → R (s n) (s (succ n)) -- xₙ < xₙ₊₁

  is_-decreasing_ : 𝓟 (ℕ → A)
  is_-decreasing_ s = ∀ n → R (s (succ n)) (s n) -- xₙ > xₙ₊₁

  -- Well-foundedness defined as: every sequence contains a non-decreasing index
  isWFseq : Set
  isWFseq = ∀ (s : ℕ → A) → Σ[ n ∈ ℕ ] (¬ (R (s (succ n)) (s n)))

  -- Weaker notions of well-foundedness
  isWFacc- : Set
  isWFacc- = ∀ x → ¬¬ (is_-accessible_ x)

  isWFind- : Set₁
  isWFind- = ∀ (φ : 𝓟 A) → (is_-inductive_ φ) → ∀ x → ¬¬ (φ x)

  isWFmin- : Set₁
  isWFmin- = ∀ (P : 𝓟 A) → ∀ {d : A} → d ∈ P → ¬¬ (Σ[ y ∈ A ] is_-_-minimal_ P y)

  -- The classical concept of a well-founded relation [TeReSe]
  isWFseq- : Set
  isWFseq- = ∀ (s : ℕ → A) → ¬ (is_-decreasing_ s)

  -- A positive variation of isWFmin
  -- What about restricting P to ¬¬-closed predicates instead?
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )

open WFDefinitions public

module WFImplications {A : Set} (R : 𝓡 A) where
-- 2. Implications between well-foundedness notions

  -- Accessibility is the least inductive predicate
  acc⊆ind : ∀ (φ : 𝓟 A) → is R -inductive φ → (is_-accessible_ R) ⊆ φ
  acc⊆ind φ φisR-ind x (acc IH) = φisR-ind x (λ y Ryx → acc⊆ind φ φisR-ind y (IH y Ryx) )

  isWFacc→isWFind : isWFacc R → isWFind R
  isWFacc→isWFind wfAcc φ φ-ind = λ x → acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : isWFind R → isWFacc R
  isWFind→isWFacc wfInd = wfInd (is_-accessible_ R) λ x → acc

  isWFmin→isWFseq : isWFmin R → isWFseq R
  isWFmin→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) {s zero } (zero ,, refl)
  ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

  -- The status of isWFmin+ ??
  isWFmin+→isWFmin₀ : isWFmin+ R → isWFmin₀ R
  isWFmin+→isWFmin₀ RisWFmin+ P ∁∁P⊆P {a} a∈P with RisWFmin+ (∁ P) (λ a∉P → a∉P a∈P)
  ... | x ,, ¬¬x∈P , xmin = (x ,, ∁∁P⊆P x ¬¬x∈P , λ y y∈P Ryx → xmin y Ryx y∈P )

  -- Remark.  The converse of this is exactly the DNS for accessibility
  ¬¬isWFacc→isWFacc- :  ¬¬ (isWFacc R) → isWFacc- R
  ¬¬isWFacc→isWFacc- ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- Remark.  The converse of this is exactly the DNS for φ
  ¬¬isWFind→isWFind- : ¬¬ isWFind R → isWFind- R
  ¬¬isWFind→isWFind- ¬¬WFiR   = λ φ φind x ¬φx → ¬¬WFiR (λ isWFiR → ¬φx (isWFiR φ φind x) )

  ¬¬isWFmin→isWFmin- : ¬¬ isWFmin R → isWFmin- R
  ¬¬isWFmin→isWFmin- ¬¬WFmR   = λ P p ¬Σ       → ¬¬WFmR (λ WFmR →   ¬Σ (WFmR P p ) )

  ¬¬isWFseq→isWFseq- : ¬¬ isWFseq R → isWFseq- R
  ¬¬isWFseq→isWFseq- ¬¬WFs = λ s sdec  → ¬¬WFs (λ WFs → snd (WFs s) (sdec (fst (WFs s)) ) )


  isWFacc-→isWFind- : isWFacc- R → isWFind- R
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- R → isWFacc- R
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → is R -accessible y) (λ x → acc)

  isWFacc-→isWFmin- : isWFacc- R → isWFmin- R
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → is R -accessible x → ¬¬ Σ[ y ∈ A ] (is R - P -minimal y)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  isWFind-→isWFmin- : isWFind- R → isWFmin- R
  isWFind-→isWFmin- RisWFind- P {d} d∈P = -- ¬Σmin =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (is R - P -minimal y)
        φ-ind : is R -inductive φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin-→isWFseq- : isWFmin- R → isWFseq- R
  isWFmin-→isWFseq- RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] is R - B -minimal d
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  ¬acc : ∀ {x : A} → ¬ (is R -accessible x) → ¬ (∀ y → R y x → is R -accessible y)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  ¬ind : ∀ (P : 𝓟 A) → is R -inductive P → ∀ x → ¬ (P x) → ¬ (∀ y → R y x → P y)
  ¬ind P Pind x ¬Px ∀y = ¬Px (Pind x ∀y )

  wf→irrefl : isWFacc R → ∀ x → ¬ R x x
  wf→irrefl RisWF x = go x (RisWF x) where
    go : ∀ y → is R -accessible y → ¬ R y y
    go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

open WFImplications public

module ClassicalImplications {A : Set} (R : 𝓡 A) where
  -- 1. Implications relying on decidability of minimality

  isDec : Set
  isDec = ∀ x y → R x y ⊔ ¬ R x y

  isMin : 𝓟 A
  isMin x = (∀ y → ¬ R y x)

  -- Decidability of being R-minimal, for a given element
  isMinDec : A → Set
  isMinDec x = (Σ[ y ∈ A ] R y x) ⊔ isMin x

  isMinDec- : A → Set
  isMinDec- x = ¬ isMin x → (Σ[ y ∈ A ] R y x)

  isMinDec⊆isMinDec- : isMinDec ⊆ isMinDec-
  isMinDec⊆isMinDec- x x∈md x∉M with x∈md
  ... | in1 x→y = x→y
  ... | in2 x∈M = ∅ (x∉M x∈M)

  -- Decidability of being R-minimal, globally
  decMin : Set
  decMin = ∀ x → isMinDec x

  isWFacc→isWFseq : isDec → isWFacc R → isWFseq R
  isWFacc→isWFseq dR wfAcc s = f s (s zero) (wfAcc (s zero)) refl where
    f : ∀ (s : ℕ → A) (x : A) (x-acc : is R -accessible x) (x=s0 : x ≡ s zero)
              → Σ[ k ∈ ℕ ] (¬ R (s (succ k)) (s k))
    f s x (acc xa) x=s0 with dR (s 1) x
    ... | in2 ¬Ryx = 0 ,, λ Rs1s0 → ¬Ryx (transp (R (s 1)) (~ x=s0) Rs1s0)
    ... | in1  Ryx with f (s ∘ succ) (s 1) (xa (s 1) Ryx) refl
    ... | i ,, p = succ i ,, p

  isWFind→isWFseq : isDec →  isWFind R → isWFseq R
  isWFind→isWFseq dR wfInd = isWFacc→isWFseq dR (isWFind→isWFacc R wfInd)

  -- Even with the global decidability assumption, this is not yet provable
  isWFacc→isWFmin : decMin → isWFacc R → isWFmin R
  isWFacc→isWFmin dM RisWFacc P {d} d∈P = f d (RisWFacc d) d∈P where
    f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
    f x (acc xac) with dM x
    ... | in1 (y ,, Ryx) = {! f y (xac y Ryx)   !}
    ... | in2 xIsMin = λ x∈P → (x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx ))

  decMin→isWFacc→isWFmin₀ : decMin → isWFacc R → isWFmin₀ R
  decMin→isWFacc→isWFmin₀ dM RisWFacc P ¬¬P→P {d} d∈P = f d (RisWFacc d) d∈P where
    f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
    f x (acc xac) x∈P with dM x
    ... | in2 xIsMin = x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx)
    -- ... | in1 (y ,, Ryx) = λ px → f y (xac y Ryx) (¬¬P→P {!   !} {!   !} )
    ... | in1 (y ,, Ryx) = f y (xac y Ryx) (¬¬P→P y λ ¬Py → {!   !} )
    -- Missing piece: deciding whether ∃y.(Rxy × Py)
    -- If yes, that would give the rec. call.  Otherwise, the min. elt. is x.
    -- Don't see how decidability of P can be avoided if we want an explicit witness.

  -- -- An additional condition for proving the converse implication
  CoInd : 𝓟 A → Set
  CoInd P = ∀ x → ¬ (P x) → Σ[ y ∈ A ] (R y x × ¬ P y)

  CoInd→Ind : ∀ (P : 𝓟 A) → ¬¬Closed P → CoInd P → is R -inductive P
  CoInd→Ind P ¬¬cP ciP x IHx = ¬¬cP x (λ ¬px → f (ciP x ¬px) ) where
    f : Σ[ y ∈ A ] (R y x × ¬ P y) → ⊥
    f (y ,, Ryx , ¬Py) = ¬Py (IHx y Ryx)

  isWFmin₀→isWFind- : isWFmin₀ R → isWFind- R
  isWFmin₀→isWFind- RisWFmin φ φ-ind a₀ ¬φa₀
    with RisWFmin (∁ φ) (λ x ¬¬¬φx φx → ¬¬¬φx (λ n → n φx)) ¬φa₀
  ... | (a ,, ¬φa , Rxa→¬¬φx) = {!   !}
    -- Missing piece: double-negation shift to go from
    --  ¬(∀y.Ryx→φy) to ¬(∀y.Ryx→¬¬φy)

  isWFmin₀→Coind→∀¬¬φ : isWFmin₀ R → ∀ (φ : 𝓟 A) → CoInd φ → ∀ a → ¬¬ φ a
  isWFmin₀→Coind→∀¬¬φ RisWFmin φ φ-coind a₀ ¬φa₀
    with RisWFmin (∁ φ) (λ x ¬¬¬φx φx → ¬¬¬φx (λ n → n φx)) ¬φa₀
  ... | (a ,, ¬φa , Rxa→¬¬φx) with φ-coind a ¬φa
  ... | (b ,, Rba , ¬φb) = Rxa→¬¬φx b ¬φb Rba

  -- isWFind→isWFmin₀ : isWFind R → ∀ (P : 𝓟 A) → CoInd P → ¬¬
  -- isWFind→isWFmin₀ RisWFi P ¬¬P→P {a₀} =
  --   let φ = ∁ P
  --       ¬¬φ→φ : ¬¬Closed φ
  --       ¬¬φ→φ = λ x z z₁ → z (λ z₂ → z₂ z₁)
  --       φ-ind : is R -inductive φ
  --       φ-ind a H pa =  ¬¬φ→φ a (λ ¬¬pa → {!   !} ) pa
  --       WFφ = {! RisWFi φ φ-ind   !}
  --    in {!   !}

  isWFind→isWFmin : decMin → isWFind R → isWFmin R
  isWFind→isWFmin dM RisWFind P d∈P = RisWFind φ φ-ind _ d∈P where
        S = Σ[ y ∈ A ] (is R - P -minimal y)
        φ : 𝓟 A
        φ x = x ∈ P → S
        -- φ : 𝓟 A
        -- φ x = x ∈ P → Σ[ y ∈ A ] (y ∈ P × ∀ z → z ∈ P → R z y → S)
        φ-ind : is R -inductive φ
        φ-ind x H x∈P with dM x
        ... | in1 (y ,, Ryx) = {!   !}
        ... | in2 xRmin = x ,, x∈P , (λ x _ → xRmin x)

  isWFmin₀→isWFseq : isWFmin₀ R → isWFseq R
  isWFmin₀→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) ¬¬CP {s zero } (zero ,, refl)
    where ¬¬CP = {!   !}
  ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

  dMseq : decMin → A → ℕ → A
  dMseq dM a0 zero = a0
  dMseq dM a0 (succ n) with dM (dMseq dM a0 n)
  ... | in1 (b ,, bRsn) = b
  ... | in2 x = dMseq dM a0 n

  {- It seems we need the following lemma. -}
  -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero) → ∀ (n : ℕ) → ¬ (P (s n))
  --              → Σ[ m  ∈ ℕ ] → ¬ P (s m) × ∀ (k : ℕ) → k < m → P (s k)

  -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero)

  isWFseq→isWFmin : decMin → isWFseq R → isWFmin R
  isWFseq→isWFmin dM RisWFseq P {a} a∈P with RisWFseq (dMseq dM a)
  ... | n ,, snRn with dM (dMseq dM a n)
  ... | in1 (y ,, yRsn) = ∅ (snRn yRsn)
  ... | in2 snRmin = {!   !}

  isWFseq→isWFmin₁ : decMin → isWFseq R → isWFmin₁ R
  isWFseq→isWFmin₁ dM RisWFseq P Pdec {a} a∈P with RisWFseq (dMseq dM a)
  ... | n ,, snRn with dM (dMseq dM a n)
  ... | in1 (y ,, yRsn) = ∅ (snRn yRsn)
  ... | in2 snRmin = {!   !}

  -- This seems to lead to the same issue as above
  isWFseq-→isWFmin- : decMin → isWFseq- R → isWFmin- R
  isWFseq-→isWFmin- dM RisWFseq P {a} a∈P ¬Σmin = RisWFseq (dMseq dM a) s-dec where
    s-dec : is R -decreasing (dMseq dM a)
    s-dec 0 = {!   !}
    s-dec (succ n) with dM (dMseq dM a (succ n))
    ... | in1 (y ,, yRsn) = yRsn
    ... | in2 snRmin = ∅ (snRmin (dMseq dM a n) {!   !} )

  -- 2. Implications relying on ¬¬-closure of accessibility
  ¬¬ACC : Set
  ¬¬ACC = ∀ {x : A} → ¬¬ (is R -accessible x) → is R -accessible x

  -- Non-terminating proof of ¬¬ACC:
  -- ¬¬acc : ¬¬ACC
  -- ¬¬acc {x} ¬¬accx = acc (λ y Ryx → ¬¬acc (λ ¬accy → ¬¬accx λ {  (acc xa) → ¬accy (xa y Ryx) } ))

  -- Double negation shift for accessibility (global)
  isWFacc-→¬¬isWFacc : ¬¬ACC → isWFacc- R → ¬¬ (isWFacc R)
  isWFacc-→¬¬isWFacc ¬¬acc RisWFacc- ¬RisWFacc  = ¬RisWFacc λ x → ¬¬acc (RisWFacc- x)

  -- isWFacc-→¬¬isWFacc : isWFacc- R → ¬¬ (isWFacc R)
  -- isWFacc-→¬¬isWFacc RisWFacc- ¬RisWFacc = f (λ {(a ,, ¬acca) → RisWFacc- a ¬acca })
  --   where f : ¬¬ Σ[ x ∈ A ] (¬ is R -accessible x)
  --         f ¬Σ = ¬RisWFacc (λ x → acc (λ y Ryx → {!   !} ) )

  ¬¬isWFacc→isWFacc : ¬¬ACC → ¬¬ (isWFacc R) → isWFacc R
  ¬¬isWFacc→isWFacc ¬¬acc ¬¬isWFaccR = λ x → ¬¬acc (λ ¬accx → ¬¬isWFaccR (λ ∀acc → ¬accx (∀acc x ) ))

  ¬¬isWFind→isWFind : ¬¬ACC → ¬¬ (isWFind R) → isWFind R
  ¬¬isWFind→isWFind ¬¬acc ¬¬isWFindR = isWFacc→isWFind R (¬¬isWFacc→isWFacc ¬¬acc g )
    where g = λ ¬Racc → ¬¬isWFindR (λ Rind → ¬Racc (isWFind→isWFacc R Rind ) )

  {- Investigating whether inductive predicates are ¬¬-closed.  Apparently they aren't.
  ¬¬ind : ∀ (P : 𝓟 A) (Pind : is R -inductive P) (x : A) → ¬¬ (P x) → P x
  ¬¬ind P Pind x ¬¬Px =
    let huh = ¬¬Px λ Px → {!   !}
        npx = {!   !}
     in Pind x {!   !}

  Pind→¬¬Pind : ∀ (P : 𝓟 A) → is R -inductive P → is R -inductive (∁ (∁ P))
  Pind→¬¬Pind P Pind = λ x IHx ¬Px → {!   !}
  -}

  -- No idea about this one.
  isWFmin-→¬¬isWFmin : ¬¬ACC → isWFmin- R → ¬¬ (isWFmin R)
  isWFmin-→¬¬isWFmin ¬¬Acc isWFmin- ¬isWFmin = {!  !}
  -- isWFmin-→¬¬isWFmin ¬¬Acc isWFmin- ¬isWFmin = ¬isWFmin (λ P {a} a∈P  → a ,, a∈P , λ b b∈P Rba → isWFmin- P a∈P λ {(c ,, c∈P , cIsMin) → {!   !}})

  -- Requires ¬(∀n)R(sn,n) → (∃n)¬R(sn,n), IE, Markov Principle + Decidability of R
  isWFseq-→¬¬isWFseq : isWFseq R → ¬¬ isWFseq R
  isWFseq-→¬¬isWFseq WFs ¬isWFseq = ¬isWFseq λ s → {! WFs s   !}

  {- TO DELETE:
  -- Not provable, almost certainly
  isWFmin→isWFacc- : ¬¬ACC → isWFmin R → isWFacc- R
  isWFmin→isWFacc- ¬¬Acc RisWFmin d ¬disRacc with RisWFmin (λ x → ¬ is R -accessible x) (¬disRacc)
  ... | m ,, ¬misRacc , mismin =
    let f : ¬ ((y : A) → R y m → is R -accessible y) → ¬ ((y : A) → (is R -accessible y → ⊥) → R y m → ⊥)
        f ¬H G = {!   !}
      in f (¬acc R ¬misRacc ) mismin

  isWFmin-→isWFind- : ¬¬ACC → isWFmin- R → isWFind- R
  isWFmin-→isWFind- ¬¬Acc RisWFmin- φ φ-ind x ¬φx = RisWFmin- (λ v → ¬ (φ v)) ¬φx f
    where f : ¬ Σ[ d ∈ A ] is R - (∁ φ) -minimal d
          f (d ,, ¬φd , ¬φ⊆¬↓d) = {!   !}

  -- The next two implications are valid only for ¬¬-closed φ
  isWFmin→isWFind- : isWFmin R → isWFind- R
  isWFmin→isWFind- RisWFmin φ φ-ind x ¬φx with RisWFmin (λ y → ¬ φ y) ¬φx
  ... | d ,, (¬φd , d-min) = {!   !}
-}
