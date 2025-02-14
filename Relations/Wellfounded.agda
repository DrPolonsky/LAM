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
  isWFminDNE : Set₁
  isWFminDNE = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

  -- Like isWFmin, but restricted to decidable predicates
  isWFminEM : Set₁
  isWFminEM = ∀ (P : 𝓟 A) → dec P → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

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
  isWFmin- = ∀ (P : 𝓟 A)               → ∀ {d : A} → d ∈ P → ¬¬ Σ[ y ∈ A ] is_-_-minimal_ P y

  isWFminDNE- : Set₁
  isWFminDNE- = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ {a : A} → a ∈ P → ¬¬ Σ[ m ∈ A ] is_-_-minimal_ P m

  isWFminEM- : Set₁
  isWFminEM- = ∀ (P : 𝓟 A) → dec P      → ∀ {a : A} → a ∈ P → ¬¬ Σ[ m ∈ A ] is_-_-minimal_ P m

  -- The classical concept of a well-founded relation [TeReSe]
  isWFseq- : Set
  isWFseq- = ∀ (s : ℕ → A) → ¬ (is_-decreasing_ s)

  -- A positive variation of isWFmin
  -- What about restricting P to ¬¬-closed predicates instead?
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )

  -- [AP] Need to rename this.  Strongly inductive?  Tightly inductive? Reductive?
  _-coinductive_ : 𝓟 A → Set
  _-coinductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P)

  isWFminCoind+ : Set₁
  isWFminCoind+ = ∀ (P : 𝓟 A) → _-coinductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] is_-_-minimal_ (∁ P) m

  ¬isWFminCoind+ : isWFminCoind+ → ∀ P → _-coinductive_ P → ∀ x → ¬¬ P x
  ¬isWFminCoind+ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  -- isWFminCoind : Set₁
  -- isWFminCoind = ∀ (P : 𝓟 A) → _-coinductive_ P → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m
open WFDefinitions public

open import Relations.ClosureOperators

module WFImplications {A : Set} (R : 𝓡 A) where
-- 2. Implications between well-foundedness notions

  -- Facts about accessible relations
  -- Wellfounded relations are irreflexive
  wf→irrefl : isWFacc R → ∀ x → ¬ R x x
  wf→irrefl RisWF x = go x (RisWF x) where
    go : ∀ y → is R -accessible y → ¬ R y y
    go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

  -- Accessibility is the least inductive predicate
  acc⊆ind : ∀ (φ : 𝓟 A) → is R -inductive φ → (is_-accessible_ R) ⊆ φ
  acc⊆ind φ φisR-ind x (acc IH) = φisR-ind x (λ y Ryx → acc⊆ind φ φisR-ind y (IH y Ryx) )

  ¬acc : ∀ {x : A} → ¬ (is R -accessible x) → ¬ (∀ y → R y x → is R -accessible y)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  ¬ind : ∀ (P : 𝓟 A) → is R -inductive P → ∀ x → ¬ (P x) → ¬ (∀ y → R y x → P y)
  ¬ind P Pind x ¬Px ∀y = ¬Px (Pind x ∀y )

  isWFacc→isWFind : isWFacc R → isWFind R
  isWFacc→isWFind wfAcc φ φ-ind = λ x → acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : isWFind R → isWFacc R
  isWFind→isWFacc wfInd = wfInd (is_-accessible_ R) λ x → acc

  isWFmin→isWFseq : isWFmin R → isWFseq R
  isWFmin→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) {s zero } (zero ,, refl)
  ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

    -- Remark.  The converse of this is exactly the DNS for accessibility
  ¬¬isWFacc→isWFacc- :  ¬¬ (isWFacc R) → isWFacc- R
  ¬¬isWFacc→isWFacc- ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- Remark.  The converse of this is exactly the DNS for all inductive φ
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

  isWFacc-→isWFseq- : isWFacc- R → isWFseq- R
  isWFacc-→isWFseq- RisWFacc- s0 s0-inc =
    RisWFacc- (s0 0) (λ s00∈acc → f (s0 0) s00∈acc s0 s0-inc refl ) where
      f : ∀ x → is R -accessible x → ∀ s → is R -decreasing s → ¬ (s 0 ≡ x)
      f x (acc xacc) s s-inc s0=x =
        f (s 1) (xacc (s 1) (transp (R (s 1)) s0=x (s-inc 0) ) )
          (s ∘ succ) (λ n → s-inc (succ n)) refl

  isWFacc-→isWFmin- : isWFacc- R → isWFmin- R
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → is R -accessible x → ¬¬ Σ[ y ∈ A ] (is R - P -minimal y)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  isWFind-→isWFmin- : isWFind- R → isWFmin- R
  isWFind-→isWFmin- RisWFind- P {d} d∈P =
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

  -- The status of isWFmin+
  -- isWFmin→isWFmin+  : isWFmin R → isWFmin+ R
  -- Problem: can only conclude the minimum element is ¬¬P
  -- isWFmin→isWFmin+ RisWF P ¬pa with RisWF (∁ P) ¬pa
  -- ... | (m ,, ¬pm , H) = (m ,, ¬pm , {!   !} )

  -- same issue, can only conclude ¬¬pm
  -- isWFminDNE→isWFmin+ : isWFminDNE R → isWFmin+ R
  -- isWFminDNE→isWFmin+ RisWF P ¬pa
  --   with RisWF (∁ P) (λ x z z₁ → z (λ z₂ → z₂ z₁)) ¬pa
  -- ... | (m ,, ¬pm , h) = (m ,, ¬pm , λ x Rxm → {!   !} )

  -- accCoind→isWFind→isWFmin+ : R -coinductive (is_-accessible_ R) → isWFacc R → isWFmin+ R
  -- accCoind→isWFind→isWFmin+ accCi RisWF P {a} = f a (RisWF a)
  --   where f : ∀ (x : A) (xa : ¬ is R -accessible x) → ¬ (P x) →
  --                       Σ[ z ∈ A ] (z ∉ P × (∀ y → R y z → P y))
  --         f x (acc xa) x∉P with accCi x {!   !}
  --         ... | (y ,, Rxy , y∉acc) = f y {!   !} {!   !}

  isWFmin+→isWFind- : isWFmin+ R → isWFind- R
  isWFmin+→isWFind- RisWF P Pind x ¬px with RisWF P ¬px
  ... | (y ,, ¬py , yind) = ¬py ((Pind y yind))

  isWFmin+→isWFmin- : isWFmin+ R → isWFmin- R
  isWFmin+→isWFmin- Rmin+ P {d} p ¬∃minP with Rmin+ (∁ P ) (λ x → x p)
  ... | (a ,, ¬¬Pa , aMin) = ¬¬Pa (λ pa → ¬∃minP ((a ,, pa , λ y Py Rya → aMin y Rya Py )) )

  isWFmin+→isWFminDNE : isWFmin+ R → isWFminDNE R
  isWFmin+→isWFminDNE RisWFmin+ P ∁∁P⊆P {a} a∈P with RisWFmin+ (∁ P) (λ a∉P → a∉P a∈P)
  ... | x ,, ¬¬x∈P , xmin = (x ,, ∁∁P⊆P x ¬¬x∈P , λ y y∈P Ryx → xmin y Ryx y∈P )

  isWFminDNE→isWFminEM : isWFminDNE R → isWFminEM R
  isWFminDNE→isWFminEM RisWFminDNE P PEM = RisWFminDNE P (λ x → pr2 (EM→WEM×DNE (P x) (PEM x) ) )

open WFImplications public

module FBImplications {A : Set} (R : 𝓡 A) where

  open import Lists

-- Thigns to do:
-- 1. FB implies ¬¬-shift for φ over R
-- 2. WFseq implies minWF₀, induction

  FB : A → Set
  FB a = Σ[ xs ∈ List A ] (∀ b → R b a → b ∈List xs)

  _isFB : Set
  _isFB = ∀ (a : A) → a ∈ FB

  -- [AP: redo]
  FB→DNS : ∀ (P : 𝓟 A) → ∀ x → x ∈ FB → (∀ y → R y x → ¬¬ P y) → ¬¬ (∀ y → R y x → P y)
  FB→DNS P a aisFB H1 H2 with aisFB
  ... | (xs ,, w) = ¬¬Allxs (λ allxs → H2 (g allxs))
      where h : ∀ ys → List∀ (λ x → ¬ (¬ (R x a → P x))) ys
            h [] = tt
            h (x ∷ ys) = (λ ¬Rax⊆Px → ¬Rax⊆Px (λ Rax → ∅ (H1 x Rax (λ px → ¬Rax⊆Px (λ _ → px) )) ) ) , (h ys)
            ¬¬Allxs : ¬¬ (List∀ (λ y → R y a → P y) xs)
            ¬¬Allxs ¬allPxs = ListDNS (λ y → R y a → P y) xs (h xs) ¬allPxs
            g : List∀ (λ y → R y a → P y) xs → (∀ y → R y a → P y)
            g allxs y Ray = All∈List (λ z → R z a → P z) (w y Ray) allxs Ray

  -- Corollary: When FB holds, ¬¬-accessibility is inductive
  FB→ind∁∁acc : _isFB → is R -inductive (λ x → ¬¬ is R -accessible x)
  FB→ind∁∁acc fb x H x∉acc = FB→DNS (is_-accessible_ R) x (fb x) H (λ f → x∉acc (acc f) )

open FBImplications public

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

  -- Proposition.  For finitely branching relations, isDec implies decMin
  open import Lists
  FB→isDec→decMin : R isFB → isDec → decMin
  FB→isDec→decMin RisFB RisDec x₀ with decList∃ P Pdec (fst (RisFB x₀))
    where P    = λ y → R y x₀
          Pdec = λ x → RisDec x x₀
  ... | in2 ∄y = in2 (λ y Ryx₀ →
    ∄y (List∃intro (~R R x₀) (fst (RisFB x₀)) y (snd (RisFB x₀) y Ryx₀ , Ryx₀)))
  ... | in1 ∃y with List∃elim (~R R x₀) (fst (RisFB x₀)) ∃y
  ... | (y ,, _ , Ryx₀) = in1 (y ,, Ryx₀ )

  -- For decidable relations, sequential well-foundedness is implied by the standard one
  isDec→isWFacc→isWFseq : isDec → isWFacc R → isWFseq R
  isDec→isWFacc→isWFseq dR wfAcc s = f s (s zero) (wfAcc (s zero)) refl where
    f : ∀ (s : ℕ → A) (x : A) (x-acc : is R -accessible x) (x=s0 : x ≡ s zero)
              → Σ[ k ∈ ℕ ] (¬ R (s (succ k)) (s k))
    f s x (acc xa) x=s0 with dR (s 1) x
    ... | in2 ¬Ryx = 0 ,, λ Rs1s0 → ¬Ryx (transp (R (s 1)) (~ x=s0) Rs1s0)
    ... | in1  Ryx with f (s ∘ succ) (s 1) (xa (s 1) Ryx) refl
    ... | i ,, p = succ i ,, p

  isDec→isWFind→isWFseq : isDec →  isWFind R → isWFseq R
  isDec→isWFind→isWFseq dR wfInd = isDec→isWFacc→isWFseq dR (isWFind→isWFacc R wfInd)

  -- Implications relating to minimality

  --   -- Even with the global decidability assumption,
  --   -- and restriction to ¬¬-closed predicates, this is not yet provable
  --   -- Missing piece: deciding whether ∃y.(Rxy × Py)
  --   -- If yes, that would give the rec. call.  Otherwise, the min. elt. is x.
  --   -- Don't see how decidability of P can be avoided if we want an explicit witness.
  -- decMin→isWFacc→isWFminDNE : decMin → isWFacc R → isWFminDNE R
  -- decMin→isWFacc→isWFminDNE dM RisWFacc P ¬¬P→P {d} d∈P = f d (RisWFacc d) d∈P where
  --   f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
  --   f x (acc xac) x∈P with dM x
  --   ... | in2 xIsMin = x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx)
  --   -- ... | in1 (y ,, Ryx) = λ px → f y (xac y Ryx) (¬¬P→P {!   !} {!   !} )
  --   ... | in1 (y ,, Ryx) = f y (xac y Ryx) (¬¬P→P y λ ¬Py → {!   !} )

  -- decMin→FB→isWFacc→isWFminDNE : decMin → FB R → isWFacc R → isWFminDNE R
  -- decMin→FB→isWFacc→isWFminDNE dM fb RisWFacc P ¬¬P→P {d} d∈P = f d (RisWFacc d) d∈P where
  --   f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
  --   f x (acc xac) x∈P with dM x
  --   ... | in2 xIsMin = x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx)
  --   -- ... | in1 (y ,, Ryx) = λ px → f y (xac y Ryx) (¬¬P→P {!   !} {!   !} )
  --   ... | in1 (y ,, Ryx) = f y (xac y Ryx) (¬¬P→P y λ ¬Py → {!   !} )

  FB→isWFminDNE-→isWFacc- : R isFB → isWFminDNE- R → isWFacc- R
  FB→isWFminDNE-→isWFacc- fb RisWF x₀ x₀∉acc =
            RisWF (λ z → ¬ is R -accessible z) (λ a nnnac ac → nnnac λ z → z ac ) x₀∉acc f
      where f : ¬ Σ-syntax A (is_-_-minimal_ R (λ z → ¬ (is R -accessible z)))
            f (z ,, z∉acc , z∈min) = FB→DNS R (is_-accessible_ R) z (fb z)
                                            (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                                            λ za → z∉acc (acc za)

  -- isWFminCoind→isWFminDNE : isWFminCoind+ R → isWFminDNE R
  -- isWFminCoind→isWFminDNE RisWF P dneP {m} m∈P
  --   with RisWF (∁ P) CP-coind (λ z → z m∈P)
  --     where CP-coind = λ x ¬¬px → {!   !}
  -- ... | (x ,, ¬¬px , xmin) = x ,, (dneP x ¬¬px) , λ y y∈P Ryx → xmin y (λ z → z y∈P) Ryx

  isWFminDNE→isWFminCoind+ : isWFminDNE R → isWFminCoind+ R
  isWFminDNE→isWFminCoind+ RisWFminDNE P Pco {a} a∉P = RisWFminDNE (∁ P) DNS¬ a∉P
    where DNS¬ = λ x y x∈P → y λ z → z x∈P

  -- isWFminDNE→isWFind- : isWFminDNE R → isWFind- R
  -- -- (!) Missing piece : double-negation shift to go from ¬(∀y.Ryx→φy) to ¬(∀y.Ryx→¬¬φy)  (!)
  -- isWFminDNE→isWFind- RisWFmin φ φ-ind a₀ ¬φa₀
  --   with RisWFmin (∁ φ) (λ x ¬¬¬φx φx → ¬¬¬φx (λ n → n φx)) ¬φa₀
  -- ... | (a ,, ¬φa , Rxa→¬¬φx) = ¬¬Ey {!   !}
  --     where ¬¬Ey : ¬¬ Σ[ y ∈ A ] (R y a × ¬ (φ y))
  --           ¬¬Ey f = {!   !}
  --   --
  -- [AP: Delete]

  -- isWFind→isWFminDNE : isWFind R → ∀ (P : 𝓟 A) → CoInd P → ¬¬
  -- isWFind→isWFminDNE RisWFi P ¬¬P→P {a₀} =
  --   let φ = ∁ P
  --       ¬¬φ→φ : ¬¬Closed φ
  --       ¬¬φ→φ = λ x z z₁ → z (λ z₂ → z₂ z₁)
  --       φ-ind : is R -inductive φ
  --       φ-ind a H pa =  ¬¬φ→φ a (λ ¬¬pa → {!   !} ) pa
  --       WFφ = {! RisWFi φ φ-ind   !}
  --    in {!   !}

  -- isWFind→isWFmin : decMin → isWFind R → isWFmin R
  -- isWFind→isWFmin dM RisWFind P d∈P = RisWFind φ φ-ind _ d∈P where
  --       S = Σ[ y ∈ A ] (is R - P -minimal y)
  --       φ : 𝓟 A
  --       φ x = x ∈ P → S
  --       -- φ : 𝓟 A
  --       -- φ x = x ∈ P → Σ[ y ∈ A ] (y ∈ P × ∀ z → z ∈ P → R z y → S)
  --       φ-ind : is R -inductive φ
  --       φ-ind x H x∈P with dM x
  --       ... | in1 (y ,, Ryx) = {!   !}
  --       ... | in2 xRmin = x ,, x∈P , (λ x _ → xRmin x)

  -- -- An alternative condition for using the WFmin₀ hypothesis
  CoInd : 𝓟 A → Set
  CoInd P = ∀ x → ¬ (P x) → Σ[ y ∈ A ] (R y x × ¬ P y)

  CoInd→Ind : ∀ (P : 𝓟 A) → ¬¬Closed P → CoInd P → is R -inductive P
  CoInd→Ind P ¬¬cP ciP x IHx = ¬¬cP x (λ ¬px → f (ciP x ¬px) ) where
    f : Σ[ y ∈ A ] (R y x × ¬ P y) → ⊥
    f (y ,, Ryx , ¬Py) = ¬Py (IHx y Ryx)

  isWFminDNE→Coind→∀¬¬φ : isWFminDNE R → ∀ (φ : 𝓟 A) → CoInd φ → ∀ a → ¬¬ φ a
  isWFminDNE→Coind→∀¬¬φ RisWFmin φ φ-coind a₀ ¬φa₀
    with RisWFmin (∁ φ) (λ x ¬¬¬φx φx → ¬¬¬φx (λ n → n φx)) ¬φa₀
  ... | (a ,, ¬φa , Rxa→¬¬φx) with φ-coind a ¬φa
  ... | (b ,, Rba , ¬φb) = Rxa→¬¬φx b ¬φb Rba

  CoIndSequence : ∀ P → R -coinductive P → Σ[ a ∈ A ] (a ∉ P) → ℕ → Σ[ e ∈ A ] (e ∉ P)
  CoIndSequence P CI aH zero = aH
  CoIndSequence P CI (a ,, Ha) (succ n) with CoIndSequence P CI (a ,, Ha) n
  ... | (a' ,, Ha') with CI a' Ha'
  ... | (x ,, Rxa , x∉P) = (x ,, x∉P)

  CoIndSequence-inc : ∀ P → (PCoind : R -coinductive P) (init : Σ[ a ∈ A ] (a ∉ P)) →
                          is R -decreasing (fst ∘ CoIndSequence P PCoind init)
  CoIndSequence-inc P PCoind init k with CoIndSequence P PCoind init k
  ... | (a ,, Ha) with PCoind a Ha
  ... | (x ,, Rxa , x∉P) = Rxa

  -- A Noteworthy Consequence
  isWFseq-→isWFacc- : R -coinductive (λ x → is R -accessible x) → isWFseq- R → isWFacc- R
  isWFseq-→isWFacc- AccisCoind RisWFseq- a a∉acc = RisWFseq- s s-inc where
    s     = fst ∘ CoIndSequence     (λ x → is R -accessible x) AccisCoind (a ,, a∉acc)
    s-inc = CoIndSequence-inc (λ x → is R -accessible x) AccisCoind (a ,, a∉acc)

  isWFseq-→isWFminCoind : isWFseq- R → isWFminCoind+ R
  isWFseq-→isWFminCoind RisWFseq P CI {a} ¬pa
    with (CoIndSequence P CI (a ,, ¬pa)) | RisWFseq (fst ∘ CoIndSequence P CI (a ,, ¬pa)) (CoIndSequence-inc P CI (a ,, ¬pa))
  ... | c | H = ∅ H

  -- isWFseq→isWFminCoind : isWFseq R → isWFminCoind+ R
  -- isWFseq→isWFminCoind RisWFseq P CI {a} ¬pa
  --   with (CoIndSequence P CI (a ,, ¬pa)) | RisWFseq (fst ∘ CoIndSequence P CI (a ,, ¬pa))
  -- ... | s | (n ,, Rs) with snd (CI (fst (s n)) (snd (s n)))
  -- ... | (c1 , c2) = ∅ (Rs c1)

  -- isWFseq→isWFminEM : isWFseq R → isWFminEM R
  -- isWFseq→isWFminEM RisWFseq P Pdec = {! isWFminDNe→isWFminDNE  !}

  module WFseqImplications (dM : decMin) where

    -- isWFminDNE→isWFseq requires: ¬¬Closed (Σa:ℕ. s n ≡ a)
    -- isWFmin+→isWFseq requires: same as above
    -- isWFminEM→isWFseq requires: decidability of the above predicate
    -- isWFminCoind→isWFseq cannot find the index in the sequence
    -- isWFmin→isWFseq is provable with no assumptions

    -- isWFminDNE→isWFseq : isWFminDNE R → isWFseq R
    -- isWFminDNE→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) ¬¬CP {s zero } (zero ,, refl)
    --   where ¬¬CP = {!   !}
    -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

    -- isWFmin+→isWFseq : isWFmin+ R → isWFseq R
    -- isWFmin+→isWFseq RisWF s with RisWF (∁ (λ z → Σ[ k ∈ ℕ ] (s k ≡ z))) ¬¬s0∈P
    --       where ¬¬s0∈P = λ z → z (0 ,, refl)
    -- ... | (m ,, ¬¬m∈P , mmin) = {!   !} -- ∅ (¬¬m∈P λ { (k ,, sk=m) → {!   !} } )

    -- isWFminCoind→isWFseq : isWFminCoind R → isWFseq R
    -- isWFminCoind→isWFseq RisWF s
    --   with RisWF (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) Coind {s zero } (zero ,, refl)
    --   where Coind : R -coinductive (λ a → Σ[ n ∈ ℕ ] (s n ≡ a))
    --         Coind x x∉s = {!   !}
    -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

    dMseq : A → ℕ → A
    dMseq a0 zero = a0
    dMseq a0 (succ n) with dM (dMseq a0 n)
    ... | in1 (b ,, bRsn) = b
    ... | in2 x = dMseq a0 n

    {- It seems we need the following lemma. -}
    -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero) → ∀ (n : ℕ) → ¬ (P (s n))
    --              → Σ[ m  ∈ ℕ ] → ¬ P (s m) × ∀ (k : ℕ) → k < m → P (s k)

    -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero)

    -- isWFseq→isWFmin : isWFseq R → isWFmin R
    -- isWFseq→isWFmin RisWFseq P {a} a∈P with RisWFseq (dMseq a)
    -- ... | n ,, snRn with dM (dMseq a n)
    -- ... | in1 (y ,, yRsn) = ∅ (snRn yRsn)
    -- ... | in2 snRmin = {!   !}

    isWFseq→isWFminDNE : isWFseq R → isWFminDNE R
    isWFseq→isWFminDNE RisWFseq P Pdne {a} a∈P with RisWFseq (dMseq a)
    ... | (k ,, p) with dM (dMseq a k) | p
    ... | in1 (x ,, Ryx) | x∈NF = ∅ (x∈NF Ryx) 
    ... | in2 x | c = {!   !}

    -- This seems to lead to the same issue as above
    isWFseq-→isWFmin- : isWFseq- R → isWFmin- R
    isWFseq-→isWFmin- RisWFseq P {a} a∈P ¬Σmin = RisWFseq (dMseq a) s-dec where
      s-dec : is R -decreasing (dMseq a)
      s-dec 0 with dM a
      ... | in1 (y ,, Rya) = Rya
      ... | in2 no = ∅ (¬Σmin (( a ,, a∈P , (λ y _ Rya → no y Rya) )) )
      s-dec (succ n) with dM (dMseq a (succ n))
      ... | in1 (y ,, yRsn) = yRsn
      ... | in2 snRmin = ∅ (snRmin (dMseq a n) {!   !} )

  -- 2. Implications relying on ¬¬-closure of accessibility
  ¬¬ACC : Set
  ¬¬ACC = ∀ {x : A} → ¬¬ (is R -accessible x) → is R -accessible x

  -- Non-terminating proof of ¬¬ACC:
  -- ¬¬acc : ¬¬ACC
  -- ¬¬acc {x} ¬¬accx = acc (λ y Ryx → ¬¬acc (λ ¬accy → ¬¬accx λ {  (acc xa) → ¬accy (xa y Ryx) } ))

  -- open LogicOps

  -- isWFmin→isWFacc : isWFmin R → isWFacc R
  -- isWFmin→isWFacc wfMin x with wfMin K⊤ tt
  -- ... | (n ,, _ , y∈NF) with wfMin (is_-accessible_ R) (acc λ y Ryn → ∅ (y∈NF y tt Ryn) )
  -- ... | m ,, acc macc , m∉acc = {!   !}
  --   Need: ¬¬ on the outside
  --
  DNSacc→isWFmin→¬¬isWFacc : ¬¬ACC → isWFmin R → isWFacc- R
  DNSacc→isWFmin→¬¬isWFacc DNSacc wfMin x xnac with wfMin K⊤ {x} tt
  ... | (n ,, _ , n∈NF) with wfMin (λ z → (R ⋆) z x × ¬ is R -accessible z) (ε⋆ , xnac)
  ... | m ,, (R*mx , m∉acc) , H = m∉acc (acc λ y Ryx → DNSacc (λ ynacc → H y ((Ryx ,⋆ R*mx) , ynacc ) Ryx ) )

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

  -- DNSacc→isWFmin-→isWFacc- = {!   !}


  -- No idea about this one.
  isWFmin-→¬¬isWFmin : ¬¬ACC → isWFmin- R → ¬¬ (isWFmin R)
  isWFmin-→¬¬isWFmin ¬¬Acc isWFmin- ¬isWFmin = {!   !}
  -- isWFmin-→¬¬isWFmin ¬¬Acc isWFmin- ¬isWFmin = ¬isWFmin (λ P {a} a∈P  → a ,, a∈P , λ b b∈P Rba → isWFmin- P a∈P λ {(c ,, c∈P , cIsMin) → {!   !}})

  -- Requires ¬(∀n)R(sn,n) → (∃n)¬R(sn,n), IE, Markov Principle + Decidability of R
  isWFseq-→¬¬isWFseq : isWFseq- R → ¬¬ isWFseq R
  isWFseq-→¬¬isWFseq WFs ¬isWFseq = ¬isWFseq λ s → {! WFs s  !}

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
