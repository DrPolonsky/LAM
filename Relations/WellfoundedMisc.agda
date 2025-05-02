-- This file contains both potential avenues to explore and dead ends. 
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq


module Relations.WellfoundedMisc where 

open import Relations.WFDefinitions public
open import Relations.WeakWFDefinitions public
open import Relations.Wellfounded public

    
module ToExplore {A : Set} {R : 𝓡 A} where
  isWFminDNE-→isWFacc- : isWFminDNE- R → isWFacc- R
  isWFminDNE-→isWFacc- RisWFminDNE- x x∉acc = RisWFminDNE- (∁ (R -accessible)) p x∉acc f
    where p = λ a b c → b (λ d → d c)
          f : ¬ Σ[ m ∈ A ] (m ∈ R - (∁ (R -accessible)) -minimal)
          f (m ,, m∉acc , mmin) = {!   !}

  -- Probably unprovable, this seems like a hard one that still deserves to be looked at.
  isWFseq-→isWFminDNE- : isWFseq- R → isWFminDNE- R
  isWFseq-→isWFminDNE- RisWFseq- P CCP⊆P {a} a∈P ¬∃minP =
    -- ¬¬lemma ℕ (λ m n → m ≡ succ n) (λ n → Σ-syntax A λ b → b ∈ P) 0 f
    ¬¬lemmaA R (λ x → x ∈ P) a f
    where
      f : _
      f (in1 (b ,, Rba , b∈P)) = {!   !} -- isWFseq-→isWFminDNE- RisWFseq- P CCP⊆P b∈P ¬∃minP
      f (in2 all) = ¬∃minP (a ,, a∈P , λ y y∈P Rya → all y Rya (y∈P ) )
      nns : ℕ → ¬¬ Σ[ b ∈ A ] (b ∈ P)
      nns 0        ne = ne (a ,, a∈P)
      nns (succ k) ne = nns k (λ {(b ,, b∈P) → ¬¬lemmaA R P b
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

module ToExploreMinDecImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where
    isMinDec→isWFacc→isWFminEM : R isWFacc → R isWFminEM
    isMinDec→isWFacc→isWFminEM RisWFacc P Pdec a = f a (RisWFacc a) ε⋆ where
        f : ∀ x → x ∈ R -accessible → (R ⋆) x a → a ∈ P → Σ[ m ∈ A ] (m ∈ R - P -minimal)
        f x (acc xa) R*xa a∈P with dM x
        ... | in1 (y ,, Ryx) = f y (xa y Ryx) (Ryx ,⋆ R*xa) a∈P
        ... | in2 x∈NF = {!     !}
 
--   -- If ¬¬∃seqDec was provable, this would be the next question.
--     isMinDec→isWFseq-→isWFminDNE- : isWFseq- R → isWFminDNE- R
--     isMinDec→isWFseq-→isWFminDNE- RisWFseq- P Pdne {a} a∈P ¬∃minP = ¬¬∃seqDec a f
--       where f : ((Σ[ k ∈ ℕ ] ∀ x → ¬ R x (dMseq a k)) ⊔ (dMseq a) ∈ R -decreasing) → ⊥
--             f (in1 (k ,, sk∈NF)) = {!   !}
--             f (in2 sdec) = RisWFseq- (dMseq a) sdec

--   -- this might be slightly easier to prove (or not)
--   -- can be moved to misc
--     isMinDec→isWFseq→isWFminDNE- : R isWFseq → isWFminDNE- R
--     isMinDec→isWFseq→isWFminDNE- RisWFseq P Pdne {a} a∈P ¬∃minP
--         with RisWFseq (dMseq a)
--     ... | k ,, kmin
--         with dM (dMseq a k) | dMseq a (succ k) in e
--     ... | in1 H | b = {!   !}
--     ... | in2 x | b = {!   !}

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


    

module MinimalComplementMisc {A : Set} (R : 𝓡 A) where
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


module DeadEnds {A : Set} {R : 𝓡 A} where 
  -- Not provable
  -- isWFseq-→¬¬isWFseq : isWFseq- R →  ¬¬ (R isWFseq)
  -- isWFseq-→¬¬isWFseq RisWFseq- ¬RisWF = ¬RisWF (λ s → {!   !} )

  -- ¬¬lemmaC : ∀ (P : 𝓟 A) (a : A) → ¬¬ (Σ[ b ∈ A ] (R b a × ¬ P b) ⊔ (∀ b → R b a → P b))
  -- ¬¬lemmaC P a ¬⊔ = ¬⊔ (in2 λ b Rba → {!   !} )

  -- isWFminDNE→isWFacc- :
  -- requires shifting double-negation of accessibility through one R-step,
  -- see FB→isWFminDNE-→isWFacc- in the finitely bounded submodule



-- Everything below here are things I think we want to delete but I want to double check:
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