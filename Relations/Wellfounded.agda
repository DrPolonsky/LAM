-- {-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq

module Relations.Wellfounded where

open import Relations.WFDefinitions public
open import Relations.WeakWFDefinitions public

module BasicImplications {A : Set} {R : 𝓡 A} where

  -- Accessibility is the least inductive predicate
  acc⊆ind : ∀ (φ : 𝓟 A) → R -inductive φ → R -accessible ⊆ φ
  acc⊆ind φ φisRind x (acc IH) = φisRind x (λ y Ryx → acc⊆ind φ φisRind y (IH y Ryx) )

  -- acc⊆WFseq : R -accessible ⊆ WFseq R
  -- acc⊆WFseq a (acc ac) s s0=a = acc⊆WFseq (s 1) {!   !} {!   !} {!   !}
  --
  ¬acc : ∀ {x : A} → x ∉ R -accessible → ¬ (∀ y → R y x → y ∈ R -accessible)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  ¬ind : ∀ (P : 𝓟 A) → R -inductive P → ∀ x → ¬ (P x) → ¬ (∀ y → R y x → P y)
  ¬ind P Pind x ¬Px ∀y = ¬Px (Pind x ∀y )

  wf→irrefl : R isWF → ∀ x → ¬ R x x
  wf→irrefl RisWF x = go x (RisWF x) where
    go : ∀ y → y ∈ R -accessible → ¬ R y y
    go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

  -- implications between the base definitions
  isWFacc→isWFind : R isWFacc → R isWFind
  isWFacc→isWFind wfAcc x φ φ-ind = acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : R isWFind → R isWFacc
  isWFind→isWFacc wfInd x = wfInd x (WFacc R ) λ y → acc

  isWFmin→isWFminDNE : R isWFmin → R isWFminDNE
  isWFmin→isWFminDNE RisWFmin P PDNE = RisWFmin P

  isWFminDNE→isWFminEM : R isWFminDNE → R isWFminEM
  isWFminDNE→isWFminEM RisWFminDNE P PEM = RisWFminDNE P (dec→¬¬Closed P PEM )

  isWFmin→isWFseq : R isWFmin → R isWFseq
  isWFmin→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) (s zero) (zero ,, refl)
  ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

open BasicImplications

module WeakImplications {A : Set} (R : 𝓡 A) where
  -- Implications between weaker well-foundedness notions

  -- Remark.  The converse of this is exactly the DNS for accessibility
  ¬¬isWFacc→isWFacc- :  ¬¬ (R isWFacc) → isWFacc- R
  ¬¬isWFacc→isWFacc- ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- The converse of this is exactly the DNS for all inductive φ
  ¬¬isWFind→isWFind- : ¬¬ (R isWFind) → isWFind- R
  ¬¬isWFind→isWFind- ¬¬WFiR   = λ φ φind x ¬φx → ¬¬WFiR (λ isWFiR → ¬φx (isWFiR x φ φind))

  -- Not provable
  -- isWFseq-→¬¬isWFseq : isWFseq- R →  ¬¬ (R isWFseq)
  -- isWFseq-→¬¬isWFseq RisWFseq- ¬RisWF = ¬RisWF (λ s → {!   !} )

  ¬¬isWFseq→isWFseq- : ¬¬ (R isWFseq) → isWFseq- R
  ¬¬isWFseq→isWFseq- ¬¬WFs = λ s sdec  → ¬¬WFs (λ WFs → snd (WFs s) (sdec (fst (WFs s)) ) )

  ¬¬isWFmin→isWFmin- : ¬¬ (R isWFmin) → isWFmin- R
  ¬¬isWFmin→isWFmin- ¬¬WFmR   = λ P p ¬Σ → ¬¬WFmR (λ WFmR → ¬Σ (WFmR P _ p ) )

  isWFminDNE→isWFminDNE- : R isWFminDNE → isWFminDNE- R
  isWFminDNE→isWFminDNE- a b c d e = e (a b c _ d)

  isWFacc-→isWFind- : isWFacc- R → isWFind- R
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- R → isWFacc- R
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → y ∈ R -accessible) (λ x → acc)

  isWFacc-→isWFmin- : isWFacc- R → isWFmin- R
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → x ∈ R -accessible → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  -- redundant [AP]
  isWFind-→isWFmin- : isWFind- R → isWFmin- R
  isWFind-→isWFmin- RisWFind- P {d} d∈P =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
        φ-ind : R -inductive φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin-→isWFseq- : isWFmin- R → isWFseq- R
  isWFmin-→isWFseq- RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] (d ∈ R - B -minimal)
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  -- redundant [AP]
  isWFacc-→isWFseq- : isWFacc- R → isWFseq- R
  isWFacc-→isWFseq- RisWFacc- s0 s0-inc =
    RisWFacc- (s0 0) (λ s00∈acc → f (s0 0) s00∈acc s0 s0-inc refl ) where
      f : ∀ x → x ∈ R -accessible → ∀ s → s ∈ R -decreasing → ¬ (s 0 ≡ x)
      f x (acc xacc) s s-inc s0=x =
        f (s 1) (xacc (s 1) (transp (R (s 1)) s0=x (s-inc 0) ) )
          (s ∘ succ) (λ n → s-inc (succ n)) refl

  isWFmin-→isWFminDNE- : isWFmin- R → isWFminDNE- R
  isWFmin-→isWFminDNE- RisWFmin- P  = λ _ → RisWFmin- P

  --  Double check this solution as it went from being long to simple.
  isWFminDNE-→isWFmin- : isWFminDNE- R → isWFmin- R
  isWFminDNE-→isWFmin- RisWFminDNE- P {d} d∈P ¬∃minP with RisWFminDNE- (∁ (∁ P)) (λ x y z → y λ w → w z ) (λ z → z d∈P)
  ... | c = c λ { (x ,, ¬x∉P , H) → ¬x∉P (λ x∈P →
                   ¬∃minP (x ,, x∈P , λ y y∈P Ryx → H y (λ z → z y∈P) Ryx ) )  }

  ¬¬lemma : ∀ (X : Set) (Q : 𝓡 X) (P : 𝓟 X) (a : X) → ¬¬ (Σ[ b ∈ X ] (Q b a × P b) ⊔ (∀ b → Q b a → ¬ P b))
  ¬¬lemma X Q P a ¬⊔ = ¬⊔ (in2 λ b Qba b∈P → ¬⊔ (in1 (b ,, Qba , b∈P) ) )

  ¬¬lemmaA : ∀ (P : 𝓟 A) (a : A) → ¬¬ (Σ[ b ∈ A ] (R b a × P b) ⊔ (∀ b → R b a → ¬ P b))
  ¬¬lemmaA P a ¬⊔ = ¬⊔ (in2 λ b Rba b∈P → ¬⊔ (in1 (b ,, Rba , b∈P) ) )

  -- ¬¬lemmaC : ∀ (P : 𝓟 A) (a : A) → ¬¬ (Σ[ b ∈ A ] (R b a × ¬ P b) ⊔ (∀ b → R b a → P b))
  -- ¬¬lemmaC P a ¬⊔ = ¬⊔ (in2 λ b Rba → {!   !} )
  --
  ¬¬lemmaC : ∀ (P : 𝓟 A) → (∁ (∁ P) ⊆ P) → (a : A) →
        ¬¬ (    (Σ[ bRba ∈ (Σ[ b ∈ A ] R b a) ] (¬ P (fst bRba)))
             ⊔  (∀ (bRba :  Σ[ b ∈ A ] R b a)    → P (fst bRba)))
  ¬¬lemmaC P CCP⊆P a ¬⊔ = ¬⊔ (in2 λ { (b ,, Rba) → CCP⊆P b (λ b∉P → ¬⊔ (in1 ((b ,, Rba) ,, b∉P ) ) )  } )

  -- 28th April: Should we scrap this goal?
  -- 30th April: Move it to an "experiments" file
  isWFminDNE-→isWFacc- : isWFminDNE- R → isWFacc- R
  isWFminDNE-→isWFacc- RisWFminDNE- x x∉acc = {!   !}
    -- RisWFminDNE- (∁ (R -accessible)) p x∉acc f
    -- where p = λ a b c → b (λ d → d c)
    --       f : ¬ Σ[ m ∈ A ] (m ∈ R - (∁ (R -accessible)) -minimal)
    --       f (m ,, m∉acc , mmin) = {!   !}

  -- Similarly should we scrap this or move it to a misc folder?
  -- Same, probably unprovable, but should be moved there
  -- This seems like a hard one that still deserves to be looked at.
  isWFseq-→isWFminDNE- : isWFseq- R → isWFminDNE- R
  isWFseq-→isWFminDNE- RisWFseq- P CCP⊆P {a} a∈P ¬∃minP =
    -- ¬¬lemma ℕ (λ m n → m ≡ succ n) (λ n → Σ-syntax A λ b → b ∈ P) 0 f
    ¬¬lemmaA (λ x → x ∈ P) a f
    where
      f : _
      f (in1 (b ,, Rba , b∈P)) = {!   !} -- isWFseq-→isWFminDNE- RisWFseq- P CCP⊆P b∈P ¬∃minP
      f (in2 all) = ¬∃minP (a ,, a∈P , λ y y∈P Rya → all y Rya (y∈P ) )
      nns : ℕ → ¬¬ Σ[ b ∈ A ] (b ∈ P)
      nns 0        ne = ne (a ,, a∈P)
      nns (succ k) ne = nns k (λ {(b ,, b∈P) → ¬¬lemmaA P b
          (case (λ {(c ,, Rcb , c∈P) → ne (c ,, c∈P)})
                λ H → ¬∃minP ((b ,, b∈P , λ y y∈P Ryb → H y Ryb y∈P )) ) })
    -- nns (succ k) ne = nns k (λ {(b ,, b∈P) → ¬¬lemmaC P CCP⊆P b
    --     (case (λ {((c ,, Rcb) ,, c∉P) → ¬∃minP (b ,, b∈P , {!   !} ) })
    --           {!   !} ) })
    -- nns : ¬ (ℕ → Σ[ b ∈ A ] (b ∈ P)) → ℕ → Σ[ b ∈ A ] (b ∈ P)
    -- nns ¬s 0 = (a ,, a∈P)
    -- nns ¬s (succ n) = {!   !}
    -- s : ℕ → Σ[ b ∈ A ] (b ∈ P)
    -- s 0 = (a ,, a∈P)
    -- s (succ n) = {!   !}

  -- isWFminDNE→isWFacc- :
  -- requires shifting double-negation of accessibility through one R-step,
  -- see FB→isWFminDNE-→isWFacc- in the finitely bounded submodule

  deMorgan : 𝓟 A → Set
  deMorgan P = ∀ a → (Σ[ bRba ∈ (Σ[ b ∈ A ] R b a) ] (¬ P (fst bRba)))
                  ⊔  (∀ (bRba :  Σ[ b ∈ A ] R b a)    → P (fst bRba))

  -- April 28th: Do we want to include this notion of WF?
  -- April 30th: Let's move it to misc,
  -- perhaps we will have a generic "isWFmin" parametrized by a higher-order
  -- property of predicates Φ ∈ (EM, DNE, deMorgan, coRec, etc.)
  isWFminDM : Set₁
  isWFminDM = ∀ P → deMorgan P → Σ[ m ∈ A ] (m ∈ (R - P -minimal))

  -- isWFminDM→isWFacc : isWFminDM → R isWFacc
  -- isWFminDM→isWFacc wfdm x = acc f where
  --   f : _
  --   f y Ryx with wfdm P = {!   !}

  -- April 28th: Are these ToDos still something we want or shall we delete them?
  {-
  To do:
  - WFmin[ind]
  - WFmin[CCind]
  - replace implications WFseq- -> WFacc- and WFDNE- -> WFacc- to use CCaccInd
  - from WFacc and strong decidability of acc (acc∈cored), prove wf[ind]
  -}


open WeakImplications public

-- Implications relying on decidability of minimality.
module WFMinDecImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where

  -- April 28th: Delete?
  -- April 30th: Let's move it to misc/open problems
  isMinDec→isWFacc→isWFminEM : R isWFacc → R isWFminEM
  isMinDec→isWFacc→isWFminEM RisWFacc P Pdec a = f a (RisWFacc a) ε⋆ where
    f : ∀ x → x ∈ R -accessible → (R ⋆) x a → a ∈ P → Σ[ m ∈ A ] (m ∈ R - P -minimal)
    f x (acc xa) R*xa a∈P with dM x
    ... | in1 (y ,, Ryx) = f y (xa y Ryx) (Ryx ,⋆ R*xa) a∈P
    ... | in2 x∈NF = {!   !}

  dMseq : A → ℕ → A
  dMseq a0 zero = a0
  dMseq a0 (succ n) with dM (dMseq a0 n)
  ... | in1 (b ,, bRsn) = b
  ... | in2 x = dMseq a0 n

  ¬¬∃seqDec : ∀ a → ¬¬ (   (Σ[ k ∈ ℕ ] ∀ x → ¬ R x (dMseq a k))
                         ⊔ (∀ k → R (dMseq a (succ k)) (dMseq a k)))
  ¬¬∃seqDec a ¬EM = ¬EM (in2 f) where
    f : (dMseq a) ∈ R -decreasing
    f k with dM (dMseq a k) | dMseq a (succ k) in e
    ... | in1 (c ,, Rcsk) | b = transp (~R R (dMseq a k)) e Rcsk
    ... | in2 x∈NF | b = ∅ (¬EM (in1 (k ,, x∈NF)))

  -- If the above was provable, this would be the next question.
  isMinDec→isWFseq-→isWFminDNE- : isWFseq- R → isWFminDNE- R
  isMinDec→isWFseq-→isWFminDNE- RisWFseq- P Pdne {a} a∈P ¬∃minP = ¬¬∃seqDec a f
    where f : ((Σ[ k ∈ ℕ ] ∀ x → ¬ R x (dMseq a k)) ⊔ (dMseq a) ∈ R -decreasing) → ⊥
          f (in1 (k ,, sk∈NF)) = {!   !}
          f (in2 sdec) = RisWFseq- (dMseq a) sdec

  -- this might be slightly easier to prove (or not)
  -- can be moved to misc
  isMinDec→isWFseq→isWFminDNE- : R isWFseq → isWFminDNE- R
  isMinDec→isWFseq→isWFminDNE- RisWFseq P Pdne {a} a∈P ¬∃minP
    with RisWFseq (dMseq a)
  ... | k ,, kmin
    with dM (dMseq a k) | dMseq a (succ k) in e
  ... | in1 H | b = {!   !}
  ... | in2 x | b = {!   !}


  -- isMinDec→isWFacc→isWFmin : R isWFacc → R isWFmin
  -- isMinDec→isWFacc→isWFmin RisWFacc P a = f a (RisWFacc a) where
  --   f : ∀ x → x ∈ R -accessible → Σ[ m ∈ A ] (m ∈ R - P -minimal)
  --   f x R*ax (acc xacc) with dM x
  --   ... | in1 (y ,, Ryx) = f y (xacc y {! Ryx  !} )
  --   ... | in2 a∈NF = a ,, a∈P , λ y _ → a∈NF y

  -- isMinDec→isWFseq-→isWFminDNE- : isWFseq- R → isWFminDNE- R
  -- isMinDec→isWFseq-→isWFminDNE- RisWFseq- P Pdne {a} a∈P ¬∃minP =
  --   RisWFseq- (dMseq a) sdec where
  --     sdec : (dMseq a) ∈ R -decreasing
  --     sdec n with dMseq a n in e
  --     ... | c = ?

      -- sdec zero with dM a | dMseq a 1 in e
      -- ... | in1 (b ,, Rba) | d = transp (λ z → R z a) e Rba
      -- ... | in2 a∈NF | d = ∅ (¬∃minP (a ,, (a∈P , λ y _ → a∈NF y ) ) )
      -- sdec (succ n) with dMseq a (succ n) in e -- dM (dMseq a n)
      -- ... | c = {!   !}
      -- with dM (dMseq a n) | dMseq a (succ n) in e
      -- ... | x | y = {!   !}

      -- sdec n with dMseq a n | dM (dMseq a n)
      -- ... | p | q = ?

  --   with RisWFseq- (dMseq a)
  -- ... | (k ,, kmin) = ?

  --   FB→DNS R (∁ P) a (RisFB a) {!   !} λ H → ¬∃minP (a ,, a∈P , λ y y∈P Rya → H y Rya y∈P )
  -- isWFseq-→isWFminDNE- RisWFseq- P Pdne {a} a∈P ¬∃minP = RisWFseq- s sdec
  --   where s : ℕ → A
  --         s zero = a
  --         s (succ n) = {!   !}
  --         sdec : s ∈ R -decreasing
  --         sdec = {!   !}

  -- isMinDec→isWFseq→isWFminDNE : R isWFseq → R isWFminDNE
  -- isMinDec→isWFseq→isWFminDNE RisWFseq P Pdne a a∈P
  --   with RisWFseq (dMseq a)
  -- ... | k ,,  p = {!   !}
  --   with dMseq a k
  -- ... | c = {!   !}

  -- ... | in1 (x ,, Ryx) | x∈NF = ∅ (x∈NF Ryx)
  -- ... | in2 sk∈NF | _ = {!   !}

  -- -- This seems to lead to the same issue as above
  -- isWFseq-→isWFmin- : isWFseq- R → isWFminDNE- R
  -- isWFseq-→isWFmin- RisWFseq P CCP⊆P {a} a∈P ¬Σmin = RisWFseq (dMseq a) s-dec where
  --   s-dec : (R -decreasing) (dMseq a)
  --   s-dec 0 with dM a
  --   ... | in1 (y ,, Rya) = Rya
  --   ... | in2 no = ∅ (¬Σmin (( a ,, a∈P , (λ y _ Rya → no y Rya) )) )
  --   s-dec (succ n) with dM (dMseq a (succ n))
  --   ... | in1 (y ,, yRsn) = yRsn
  --   ... | in2 snRmin = ∅ (snRmin (dMseq a n) {!   !} )


  {- It seems we need the following lemma. -}
  -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero) → ∀ (n : ℕ) → ¬ (P (s n))
  --              → Σ[ m  ∈ ℕ ] → ¬ P (s m) × ∀ (k : ℕ) → k < m → P (s k)

  -- lemmaMin : ∀ (P : 𝓟 A) (s : ℕ → A) → P (s zero)

  -- isWFseq→isWFmin : isWFseq R → isWFmin R
  -- isWFseq→isWFmin RisWFseq P {a} a∈P with RisWFseq (dMseq a)
  -- ... | n ,, snRn with dM (dMseq a n)
  -- ... | in1 (y ,, yRsn) = ∅ (snRn yRsn)
  -- ... | in2 snRmin = {!   !}

  -- This is obviously provable with decidability
  -- isMinDec→isWFacc→isWFminEM : R isWFacc → R isWFminEM
  -- isMinDec→isWFacc→isWFminEM RisWFacc P Pdec a = f a (RisWFacc a) where
  --   f : ∀ x → x ∈ R -accessible → x ∈ P → Σ[ m ∈ A ] (m ∈ R - P -minimal)
  --   f x (acc xa) x∈P with dM x
  --   ... | in1 (y ,, Ryx) = {!   !}
  --   ... | in2 x∈NF = {!   !}

  -- FB→¬¬isWFseq-→isWFminDNE- : ¬¬(R isWFseq) → isWFminDNE- R
  -- FB→¬¬isWFseq-→isWFminDNE- ¬¬RisWFseq P Pdne {a} a∈P ¬∃minP = ¬¬RisWFseq f
  --   where s : ℕ → A
  --         s zero = a
  --         s (succ n) = {!   !}
  --         f : ¬ R isWFseq
  --         f RisWFseq = FB→DNS R (∁ P) a (RisFB a) {!   !}
  --                         λ H → ¬∃minP (a ,, a∈P , λ y y∈P Rya → H y Rya y∈P )
  --

  -- only provable for finitely branching relations
  -- isWFseq→isWFminEM : R isWFseq → R isWFminEM
  -- isWFseq→isWFminEM RisWFseq P Pdec a a∈P = {!   !}
  --   where s : ℕ → A
  --         s

open import Relations.FinitelyBranching
-- Implications relying on finite branching of the relation.
module FBImplications {A : Set} {R : 𝓡 A} (RisFB : R isFB) where

  FB→isWFminDNE-→isWFacc- : isWFminDNE- R → isWFacc- R
  FB→isWFminDNE-→isWFacc- RisWF x₀ x₀∉acc =
    RisWF (∁ (R -accessible)) (?) x₀∉acc f
      where f : ¬ Σ-syntax A (R - ∁ (R -accessible)-minimal)
            f (z ,, z∉acc , z∈min) =
              FB→DNS R (R -accessible) z (RisFB z)
                     (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                     λ za → z∉acc (acc za)
  --
  -- When FB holds, ¬¬-accessibility is inductive
  FB→ind∁∁acc : R -inductive (∁ ∁ R -accessible)
  FB→ind∁∁acc x H x∉acc = FB→DNS R (R -accessible) x (RisFB x) H (λ f → x∉acc (acc f) )

  -- For finitely branching relations, isDec implies MinDec
  open import Lists
  FB→isDec→isMinDec : R isDec → R isMinDec
  FB→isDec→isMinDec RisDec x₀ with decList∃ (~R R x₀) (λ _ → RisDec) (fst (RisFB x₀))
  ... | in2 ∄y = in2 (λ y Ryx₀ →
   ∄y (List∃intro (~R R x₀) (fst (RisFB x₀)) y (snd (RisFB x₀) y Ryx₀ , Ryx₀)))
  ... | in1 ∃y with List∃elim (~R R x₀) (fst (RisFB x₀)) ∃y
  ... | (y ,, _ , Ryx₀) = in1 (y ,, Ryx₀ )

  FB→isWFminDNE→isWFseq : R isWFminDNE → R isWFseq
  FB→isWFminDNE→isWFseq wfMinDNE s = {!    !} where
    RisWFseq- : isWFseq- R
    RisWFseq- = isWFmin-→isWFseq- R (isWFminDNE-→isWFmin- R (isWFminDNE→isWFminDNE- R wfMinDNE))
    P : 𝓟 A
    P x = Σ[ n ∈ ℕ ] (x ≡ s n × ¬ (s ∘ add n) ∈ R -decreasing)
    ps0 : P (s 0)
    ps0 = 0 ,, (refl , RisWFseq- _ )
    CCP⊆P : ¬¬Closed P
    CCP⊆P x ¬x∉P = {!    !}

  -- with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) (s zero) (zero ,, refl)
  -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )



open FBImplications public

module MinimalComplement {A : Set} (R : 𝓡 A) where
  _-coreductive_ : 𝓟 A → Set
  _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P)

  Cor→ind¬¬ : ∀ (P : 𝓟 A) → _-coreductive_ P → R -inductive (∁ (∁ P))
  Cor→ind¬¬ P Pco x xind ¬Px with Pco x ¬Px
  ... | (y ,, Ryx , ¬Py) = xind y Ryx ¬Py

  -- Cor→¬¬ind : ∀ (P : 𝓟 A) → _-coreductive_ P → ¬¬Closed P → R -inductive P
  -- Cor→¬¬ind P ¬¬cP ciP x IHx = ¬¬cP x (λ ¬px → f (ciP x ¬px) ) where
  --   f : Σ[ y ∈ A ] (R y x × ¬ P y) → ⊥
  --   f (y ,, Ryx , ¬Py) = ¬Py (IHx y Ryx)

  -- MinDec→CCacc∈coreductive : R isMinDec → _-coreductive_ (∁ R -accessible)
  -- MinDec→CCacc∈coreductive RisMD x x∉acc with RisMD x
  -- ... | in1 (y ,, Ryx) = y ,, Ryx , {!   !}
  -- ... | in2 x∈NF with = {!   !}

  -- MinDec→CCacc∈coreductive : R isMinDec → _-coreductive_ (∁ (∁ R -accessible))
  -- MinDec→CCacc∈coreductive RisMD x ¬x∉acc with RisMD x
  -- ... | in1 (y ,, Ryx) = y ,, Ryx , λ ¬y∈acc → ¬x∉acc (λ x∉acc → {!  !} )
  -- ... | in2 x∈NF = {!   !}

  -- A variation of ``minimal'' with focus on the complement of the given predicate
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )

  -- isWFmin+, but restricted to coreductive predicates
  isWFminCor+ : Set₁
  isWFminCor+ = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x))

  -- a weaker variation
  isWFminCor : Set₁
  isWFminCor = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∈ R - ∁ P -minimal)

  -- Implications involving complements/coreductive
  isWFmin+→isWFind- : isWFmin+ → isWFind- R
  isWFmin+→isWFind- RisWF P Pind x ¬px with RisWF P ¬px
  ... | (y ,, ¬py , yind) = ¬py ((Pind y yind))

  isWFmin+→isWFmin- : isWFmin+ → isWFmin- R
  isWFmin+→isWFmin- Rmin+ P {d} p ¬∃minP with Rmin+ (∁ P ) (λ x → x p)
  ... | (a ,, ¬¬Pa , aMin) = ¬¬Pa (λ pa → ¬∃minP ((a ,, pa , λ y Py Rya → aMin y Rya Py )) )

  -- 28th April: TODO needs fixing.
  isWFmin+→isWFminDNE : isWFmin+ → R isWFminDNE
  isWFmin+→isWFminDNE RisWFmin+ P ∁∁P⊆P a a∈P with RisWFmin+ (∁ P) (λ a∉P → a∉P a∈P)
  ... | x ,, ¬¬x∈P , xmin = {!   !} --  x ,, {!   ∁∁P⊆P!} , ?
  -- ... |  (x ,, ∁∁P⊆P x ¬¬x∈P , λ y y∈P Ryx → xmin y Ryx y∈P )

  isWFminDNE→isWFminCor+ : R isWFminDNE → isWFminCor+
  isWFminDNE→isWFminCor+ RisWFminDNE P Pco {a} a∉P
    with  RisWFminDNE (∁ P) DNS¬ a a∉P
    where DNS¬ = λ x ¬Px ¬¬Px → {!   !}
  ... | (y ,, ¬Py , ymin) with Pco y ¬Py
  ... | (z ,, Rzy , ¬Pz) = ∅ (ymin z ¬Pz Rzy)

  isWFminCor+→isWFminCor : isWFminCor+ → isWFminCor
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  isWFminCor→Cor¬¬ : isWFminCor → ∀ P → _-coreductive_ P → ∀ x → ¬¬ P x
  isWFminCor→Cor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  isWFminDNE→Cor¬¬ : R isWFminDNE → ∀ P → _-coreductive_ P → ∀ a → ¬¬ P a
  isWFminDNE→Cor¬¬ RisWFmin = isWFminCor→Cor¬¬
    (isWFminCor+→isWFminCor (isWFminDNE→isWFminCor+  RisWFmin))

  CorSequence : ∀ P → _-coreductive_ P → Σ[ a ∈ A ] (a ∉ P) → ℕ → Σ[ e ∈ A ] (e ∉ P)
  CorSequence P CI aH zero = aH
  CorSequence P CI (a ,, Ha) (succ n) with CorSequence P CI (a ,, Ha) n
  ... | (a' ,, Ha') with CI a' Ha'
  ... | (x ,, Rxa , x∉P) = (x ,, x∉P)

  CorSequence-inc : ∀ P → (PCor : _-coreductive_ P) (init : Σ[ a ∈ A ] (a ∉ P)) →
                           (R -decreasing) (fst ∘ CorSequence P PCor init)
  CorSequence-inc P PCor init k with CorSequence P PCor init k
  ... | (a ,, Ha) with PCor a Ha
  ... | (x ,, Rxa , x∉P) = Rxa

  -- A Noteworthy Consequence
  accCorec→isWFseq-→isWFacc- : _-coreductive_ (R -accessible) → isWFseq- R → isWFacc- R
  accCorec→isWFseq-→isWFacc- AccisCor RisWFseq- a a∉acc = RisWFseq- s s-inc where
    s     = fst ∘ CorSequence     (R -accessible) AccisCor (a ,, a∉acc)
    s-inc = CorSequence-inc (R -accessible) AccisCor (a ,, a∉acc)

  isWFseq-→isWFminCor+ : isWFseq- R → isWFminCor+
  isWFseq-→isWFminCor+ RisWFseq P CI {a} ¬pa
    with (CorSequence P CI (a ,, ¬pa)) | RisWFseq (fst ∘ CorSequence P CI (a ,, ¬pa)) (CorSequence-inc P CI (a ,, ¬pa))
  ... | c | H = ∅ H

  -- redundant
  -- isWFseq→isWFminCor+ : R isWFseq → isWFminCor+
  -- isWFseq→isWFminCor+ RisWFseq P CI {a} ¬pa
  --   with (CorSequence P CI (a ,, ¬pa)) | RisWFseq (fst ∘ CorSequence P CI (a ,, ¬pa))
  -- ... | s | (n ,, Rs) with snd (CI (fst (s n)) (snd (s n)))
  -- ... | (c1 , c2) = ∅ (Rs c1)

  -- The status of isWFmin+: Unprovable implications

  -- isWFmin→isWFmin+  : isWFmin R → isWFmin+ R
  -- Problem: can only conclude the minimum element is ¬¬P
  -- isWFmin→isWFmin+ RisWF P ¬pa with RisWF (∁ P) ¬pa
  -- ... | (m ,, ¬pm , H) = (m ,, ¬pm , {!   !} )

  -- same issue, can only conclude ¬¬pm
  -- isWFminDNE→isWFmin+ : isWFminDNE R → isWFmin+ R
  -- isWFminDNE→isWFmin+ RisWF P ¬pa
  --   with RisWF (∁ P) (λ x z z₁ → z (λ z₂ → z₂ z₁)) ¬pa
  -- ... | (m ,, ¬pm , h) = (m ,, ¬pm , λ x Rxm → {!   !} )

  -- accCor→isWFind→isWFmin+ : _-coreductive_ (R -accessible) → R isWFacc → isWFmin+
  -- accCor→isWFind→isWFmin+ accCi RisWF P {a} = f a (RisWF a)
  --   where f : ∀ (x : A) (xa : x ∉ R -accessible) → ¬ (P x) →
  --                       Σ[ z ∈ A ] (z ∉ P × (∀ y → R y z → P y))
  --         f x (acc xa) x∉P with accCi x
  --         ... | (y ,, Rxy , y∉acc) = f y {!   !} {!   !}



module ClassicalImplications {A : Set} (R : 𝓡 A) where

  {- We will consider four decidability hypotheses here:
  1. isDec    : ∀xy. Rxy ⊔ ¬Rxy
  2. isMinDec : ∀x. (∃y. Ryx) ⊔ (∀y.¬Ryx)
  3. AccDNE   : ∀x. ¬x∉acc → x∈acc
  4. AccCor   : R -coreductive (R -accessible)
  -- (Recall that, for FB relations, 1 → 2)
  -}

  -- 1. For decidable relations, sequential well-foundedness is implied by the standard one
  isDec→isWFacc→isWFseq : R isDec → R isWFacc → R isWFseq
  isDec→isWFacc→isWFseq dR wfAcc s = f s (s zero) (wfAcc (s zero)) refl where
    f : ∀ (s : ℕ → A) (x : A) (x-acc : x ∈ R -accessible) (x=s0 : x ≡ s zero)
              → Σ[ k ∈ ℕ ] (¬ R (s (succ k)) (s k))
    f s x (acc xa) x=s0 with dR {s 1} {x}
    ... | in2 ¬Ryx = 0 ,, λ Rs1s0 → ¬Ryx (transp (R (s 1)) (~ x=s0) Rs1s0)
    ... | in1  Ryx with f (s ∘ succ) (s 1) (xa (s 1) Ryx) refl
    ... | i ,, p = succ i ,, p

  isDec→isWFind→isWFseq : R isDec → R isWFind → R isWFseq
  isDec→isWFind→isWFseq dR wfInd = isDec→isWFacc→isWFseq dR (isWFind→isWFacc wfInd)

  -- 2. Implications relying on decidability of minimality.
  module WFseqImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where
  {-  Very hard to imply isWFseq, almost nothing is provable.
      isWFminDNE→isWFseq requires: ¬¬Closed (Σa:ℕ. s n ≡ a)
      isWFmin+→isWFseq requires: same as above
      isWFminEM→isWFseq requires: decidability of the above predicate
      isWFminCor→isWFseq cannot find the index in the sequence
      isWFmin→isWFseq is provable with no additional assumptions
    -}

    -- [AP. This section should be deleted. Everything provable moved elsewhere.]


      -- isWFminDNE→isWFseq : isWFminDNE R → isWFseq R
      -- isWFminDNE→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) ¬¬CP {s zero } (zero ,, refl)
      --   where ¬¬CP = {!   !}
      -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

      -- isWFmin+→isWFseq : isWFmin+ R → isWFseq R
      -- isWFmin+→isWFseq RisWF s with RisWF (∁ (λ z → Σ[ k ∈ ℕ ] (s k ≡ z))) ¬¬s0∈P
      --       where ¬¬s0∈P = λ z → z (0 ,, refl)
      -- ... | (m ,, ¬¬m∈P , mmin) = {!   !} -- ∅ (¬¬m∈P λ { (k ,, sk=m) → {!   !} } )

      -- isWFminCor→isWFseq : isWFminCor R → isWFseq R
      -- isWFminCor→isWFseq RisWF s
      --   with RisWF (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) Cor {s zero } (zero ,, refl)
      --   where Cor : R -coreductive (λ a → Σ[ n ∈ ℕ ] (s n ≡ a))
      --         Cor x x∉s = {!   !}
      -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

  module WFDNE {A : Set} (R : 𝓡 A) where
  -- 3. Implications relying on ¬¬-closure of accessibility
  AccDNE : Set
  AccDNE = ¬¬Closed (R -accessible)

  -- April 28th: Todo fix this
  DNEacc→isWFminDNE→isWFacc : AccDNE → R isWFminDNE → R isWFacc
  DNEacc→isWFminDNE→isWFacc dne wfDNE x = {! dne!}
    where f : ¬¬ (x ∈ R -accessible)
          f = {!   !}
    --  dne x f where
    -- f : ¬¬ (x ∈ R -accessible)
    -- f = ?
  --   f x∉acc with wfDNE (∁ (R -accessible)) (λ y nnny ya → nnny (λ z → z ya)) x x∉acc
  --   ... | (y ,, y∉acc , yIH) = y∉acc (acc λ z Rzy → dne z (λ z∉acc → yIH z z∉acc Rzy ) )

  -- April 28th: Todo Fix this
  -- Double negation shift for accessibility (global)
  isWFacc-→¬¬isWFacc : AccDNE → isWFacc- R → ¬¬ (R isWFacc)
  isWFacc-→¬¬isWFacc AccDNE RisWFacc- ¬RisWFacc  = ¬RisWFacc λ x → {!   !}
    -- ¬RisWFacc λ x → AccDNE x (RisWFacc- x)

  {-
  ¬¬isWFacc→isWFacc : AccDNE → ¬¬ (R isWFacc) → R isWFacc
  ¬¬isWFacc→isWFacc AccDNE ¬¬isWFaccR = λ x → AccDNE x (λ ¬accx → ¬¬isWFaccR (λ ∀acc → ¬accx (∀acc x ) ))

  ¬¬isWFind→isWFind : AccDNE → ¬¬ (R isWFind) → R isWFind
  ¬¬isWFind→isWFind AccDNE ¬¬isWFindR = isWFacc→isWFind (¬¬isWFacc→isWFacc (AccDNE) g )
    where g = λ ¬Racc → ¬¬isWFindR (λ Rind → ¬Racc (isWFind→isWFacc Rind ) )

  -- Non-terminating proof of AccDNE:
  -- AccDNE : AccDNE
  -- AccDNE {x} AccDNEx = acc (λ y Ryx → AccDNE (λ ¬accy → AccDNEx λ {  (acc xa) → ¬accy (xa y Ryx) } ))

  -- isWFmin→isWFacc : isWFmin R → isWFacc R
  -- isWFmin→isWFacc wfMin x with wfMin K⊤ tt
  -- ... | (n ,, _ , y∈NF) with wfMin (_-accessible_ R) (acc λ y Ryn → ∅ (y∈NF y tt Ryn) )
  -- ... | m ,, acc macc , m∉acc = {!   !}
  --   Need: ¬¬ on the outside

  -- DNSacc→isWFmin→¬¬isWFacc : AccDNE → R isWFmin → isWFacc- R
  -- DNSacc→isWFmin→¬¬isWFacc DNSacc wfMin x xnac with wfMin K⊤ x tt
  -- ... | (n ,, _ , n∈NF) with wfMin (λ z → (R ⋆) z x × (x ∉ R -accessible)) _ (ε⋆ , xnac)
  -- ... | m ,, (R*mx , m∉acc) , H = m∉acc (acc λ y Ryx → DNSacc (λ ynacc → H y ((Ryx ,⋆ R*mx) , ynacc ) Ryx ) )

  -- DNSacc→isWFmin-→isWFacc- = {!   !}

  -- Not provable without DNEacc;
  -- A stronger implication (with isWFminDNE-) follows with FB.
  -- isWFminDNE→isWFacc- : isWFminDNE R → isWFacc- R
  -- isWFminDNE→isWFacc- RisWFminDNE x x∉acc
  --   with RisWFminDNE (∁ (_-accessible_ R)) (λ x nnnx xacc → nnnx λ z → z xacc ) x∉acc
  -- ... | (y ,, y∉acc , ymin) =  {!   !}

{-  ***  TO DELETE: ***

-- Implications relating to minimality

-- isWFminDNE→isWFind- RisWFmin φ φ-ind a₀ ¬φa₀
--   with RisWFmin (∁ φ) (λ x ¬¬¬φx φx → ¬¬¬φx (λ n → n φx)) ¬φa₀
-- ... | (a ,, ¬φa , Rxa→¬¬φx) = ¬¬Ey {!   !}
--     where ¬¬Ey : ¬¬ Σ[ y ∈ A ] (R y a × ¬ (φ y))
--           ¬¬Ey f = {!   !}
--   --
-- [AP: Delete]  [Solution in "AccDNE" section ]

-- isWFind→isWFminDNE : isWFind R → ∀ (P : 𝓟 A) → Cor P → ¬¬
-- isWFind→isWFminDNE RisWFi P ¬¬P→P {a₀} =
--   let φ = ∁ P
--       ¬¬φ→φ : ¬¬Closed φ
--       ¬¬φ→φ = λ x z z₁ → z (λ z₂ → z₂ z₁)
--       φ-ind : is R -inductive φ
--       φ-ind a H pa =  ¬¬φ→φ a (λ ¬¬pa → {!   !} ) pa
--       WFφ = {! RisWFi φ φ-ind   !}
--    in {!   !}

-- isWFind→isWFmin : MinDec → isWFind R → isWFmin R
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

--   -- Even with the global decidability assumption,
--   -- and restriction to ¬¬-closed predicates, this is not yet provable
--   -- Missing piece: deciding whether ∃y.(Rxy × Py)
--   -- If yes, that would give the rec. call.  Otherwise, the min. elt. is x.
--   -- Don't see how decidability of P can be avoided if we want an explicit witness.
-- MinDec→isWFacc→isWFminDNE : MinDec → isWFacc R → isWFminDNE R
-- MinDec→isWFacc→isWFminDNE dM RisWFacc P ¬¬P→P {d} d∈P = f d (RisWFacc d) d∈P where
--   f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
--   f x (acc xac) x∈P with dM x
--   ... | in2 xIsMin = x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx)
--   -- ... | in1 (y ,, Ryx) = λ px → f y (xac y Ryx) (¬¬P→P {!   !} {!   !} )
--   ... | in1 (y ,, Ryx) = f y (xac y Ryx) (¬¬P→P y λ ¬Py → {!   !} )

-- MinDec→FB→isWFacc→isWFminDNE : MinDec → FB R → isWFacc R → isWFminDNE R
-- MinDec→FB→isWFacc→isWFminDNE dM fb RisWFacc P ¬¬P→P {d} d∈P = f d (RisWFacc d) d∈P where
--   f : ∀ x → is R -accessible x → x ∈ P → Σ[ a ∈ A ] is R - P -minimal a
--   f x (acc xac) x∈P with dM x
--   ... | in2 xIsMin = x ,, (x∈P , λ y Py Ryx → xIsMin y Ryx)
--   -- ... | in1 (y ,, Ryx) = λ px → f y (xac y Ryx) (¬¬P→P {!   !} {!   !} )
--   ... | in1 (y ,, Ryx) = f y (xac y Ryx) (¬¬P→P y λ ¬Py → {!   !} )

-- isWFminCor→isWFminDNE : isWFminCor+ R → isWFminDNE R
-- isWFminCor→isWFminDNE RisWF P dneP {m} m∈P
--   with RisWF (∁ P) CP-Cor (λ z → z m∈P)
--     where CP-Cor = λ x ¬¬px → {!   !}
-- ... | (x ,, ¬¬px , xmin) = x ,, (dneP x ¬¬px) , λ y y∈P Ryx → xmin y (λ z → z y∈P) Ryx

  -- No idea about this one.
  -- isWFmin-→¬¬isWFmin : AccDNE → isWFmin- R → ¬¬ (isWFmin R)
  -- isWFmin-→¬¬isWFmin AccDNE isWFmin- ¬isWFmin = {!   !}
  -- isWFmin-→¬¬isWFmin AccDNE isWFmin- ¬isWFmin = ¬isWFmin (λ P {a} a∈P  → a ,, a∈P , λ b b∈P Rba → isWFmin- P a∈P λ {(c ,, c∈P , cIsMin) → {!   !}})

  -- Requires ¬(∀n)R(sn,n) → (∃n)¬R(sn,n), IE, Markov Principle + Decidability of R
  -- isWFseq-→¬¬isWFseq : isWFseq- R → ¬¬ isWFseq R
  -- isWFseq-→¬¬isWFseq WFs ¬isWFseq = ¬isWFseq λ s → {! WFs s  !}

  -- Not provable, almost certainly
  isWFmin→isWFacc- : AccDNE → isWFmin R → isWFacc- R
  isWFmin→isWFacc- AccDNE RisWFmin d ¬disRacc with RisWFmin (λ x → ¬ is R -accessible x) (¬disRacc)
  ... | m ,, ¬misRacc , mismin =
    let f : ¬ ((y : A) → R y m → is R -accessible y) → ¬ ((y : A) → (is R -accessible y → ⊥) → R y m → ⊥)
        f ¬H G = {!   !}
      in f (¬acc R ¬misRacc ) mismin

  isWFmin-→isWFind- : AccDNE → isWFmin- R → isWFind- R
  isWFmin-→isWFind- AccDNE RisWFmin- φ φ-ind x ¬φx = RisWFmin- (λ v → ¬ (φ v)) ¬φx f
    where f : ¬ Σ[ d ∈ A ] is R - (∁ φ) -minimal d
          f (d ,, ¬φd , ¬φ⊆¬↓d) = {!   !}

  -- The next two implications are valid only for ¬¬-closed φ
  isWFmin→isWFind- : isWFmin R → isWFind- R
  isWFmin→isWFind- RisWFmin φ φ-ind x ¬φx with RisWFmin (λ y → ¬ φ y) ¬φx
  ... | d ,, (¬φd , d-min) = {!   !}
-}
-}
