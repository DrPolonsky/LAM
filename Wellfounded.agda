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


{- 6.26  Exercise A1.18 from the accessible point of view.
-}


module WellFoundedness {A : Set} (R : 𝓡 A) where

  -- An element is R-accessible if all elements R-below it are R-accessible
  data is_-accessible_ : 𝓟 A where
    acc : ∀ {x : A} → (∀ y → R y x → is_-accessible_ y) → is_-accessible_ x

  -- A relation is well-founded if every element is accessible
  isWFacc : Set
  isWFacc = ∀ (x : A) → is_-accessible_ x

  is_-inductive_ : 𝓟 A → Set
  is_-inductive_ φ = ∀ x → (∀ y → R y x → φ y) → φ x

  -- The constructive concept of a well-founded relation
  isWFind : Set₁
  isWFind = ∀ (φ : 𝓟 A) → is_-inductive_ φ → ∀ x → φ x

  is_-_-minimal_ : 𝓟 A → 𝓟 A
  -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
  is_-_-minimal_ φ x = x ∈ φ × (∀ y → y ∈ φ → R y x → ⊥)

  isWFmin : Set₁
  isWFmin = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∈ P → Σ[ m ∈ A ] is_-_-minimal_ P m

  is_-decreasing_ : 𝓟 (ℕ → A)
  is_-decreasing_ s = ∀ n → ~R R (s n) (s (succ n)) -- xₙ > xₙ₊₁

  -- The classical concept of a well-founded relation [TeReSe]
  isWFseq : Set
  isWFseq = ∀ (s : ℕ → A) → ¬ (is_-decreasing_ s)


  -- Relations between definitions of well-foundedness
  acc⊆ind : ∀ (φ : 𝓟 A) → is_-inductive_ φ → is_-accessible_ ⊆ φ
  acc⊆ind φ φisR-ind x (acc IH) = φisR-ind x (λ y Ryx → acc⊆ind φ φisR-ind y (IH y Ryx) )

  isWFacc→isWFind : isWFacc → isWFind
  isWFacc→isWFind wfAcc φ φ-ind = λ x → acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : isWFind → isWFacc
  isWFind→isWFacc wfInd = wfInd is_-accessible_ (λ x → acc {x})

  isWFmin- : Set₁
  isWFmin- = ∀ (P : 𝓟 A) → ∀ {d : A} → d ∈ P → ¬¬ (Σ[ y ∈ A ] is_-_-minimal_ P y)

  isWFind- : Set₁
  isWFind- = ∀ (φ : 𝓟 A) → (is_-inductive_ φ) → ∀ x → ¬¬ (φ x)

  isWFacc- : Set
  isWFacc- = ∀ x → ¬¬ (is_-accessible_ x)

  isWFacc-→isWFind- : isWFacc- → isWFind-
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- → isWFacc-
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → is_-accessible_ y) (λ x → acc)

  -- Follows from the one below
  -- isWFacc→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFacc R → isWFmin- R
  -- isWFacc→isWFmin- R RisWFacc P {d} d∈P = f d d∈P (RisWFacc d) where
  --   f : ∀ x → x ∈ P → is R -accessible x → _
  --   f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  isWFacc-→isWFmin- : isWFacc- → isWFmin-
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → is_-accessible_ x → ¬¬ Σ[ y ∈ A ] (is_-_-minimal_ P y)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  -- Follows from the one below
  -- isWFind→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFind R → isWFmin- R
  -- isWFind→isWFmin- {D} R RisWFind P d∈P = -- ¬Σmin =
  --   let φ : 𝓟 D
  --       φ x = x ∈ P → ¬¬ Σ[ y ∈ D ] (is R - P -minimal y)
  --       φ-ind : is R -inductive φ
  --       φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
  --     in RisWFind φ φ-ind _ d∈P

  isWFind-→isWFmin- : isWFind- → isWFmin-
  isWFind-→isWFmin- RisWFind- P {d} d∈P = -- ¬Σmin =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (is_-_-minimal_ P y)
        φ-ind : is_-inductive_ φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

  -- Follows from the ones above
  -- isWFind→WFseq : isWFind → isWFseq
  -- isWFind→WFseq RisWF s sIsR-Dec =
  --   let φ : 𝓟 A
  --       φ a = ∀ n → ¬ a ≡ s n -- a ∉ Im [ s ]
  --       φ-ind : is_-inductive_ φ
  --       φ-ind x IH m x≡sm = IH (s (succ m))
  --             (transp (R (s (succ m))) (~ x≡sm) (sIsR-Dec m)) (succ m) refl
  --    in RisWF φ φ-ind (s zero) zero refl

  isWFmin-→isWFseq : isWFmin- → isWFseq
  isWFmin-→isWFseq RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] is_-_-minimal_ B d
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))


  ¬acc : ∀ {x : A} → ¬ (is_-accessible_ x) → ¬ (∀ y → R y x → is_-accessible_ y)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

open WellFoundedness public

-- module June26 {D : Set} (R : 𝓡 D) where
--
--   is_-unbounded_ : 𝓟 D → Set
--   is_-unbounded_ φ = ∀ x → x ∈ φ → Σ[ y ∈ D ] (y ∈ φ × R y x)
--
--   isWFbnd : Set₁
--   isWFbnd = ∀ (P : 𝓟 D) → is_-unbounded_ P → ∀ x → x ∉ P
--
--   Easy
--   ∁∁indWF : isWFind R → ∀ (P : 𝓟 D) → is R -inductive P → is R -inductive (∁ (∁ P))
--   ∁∁indWF RisWF P PisRind x H ¬Px = ¬Px (RisWF P PisRind x)
--
--   Hard
--   ∁∁ind : ∀ (P : 𝓟 D) → is R -inductive P → is R -inductive (∁ (∁ P))
--   ∁∁ind P PisRind x H ¬Px = ¬Px {!   !}
--
--   Obvious
--   isWFacc→isWFacc- : isWFacc R → isWFacc- R
--   isWFacc→isWFacc- isWFacc x ¬accx = ¬accx (isWFacc x)
--
-- isWFbnd→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFbnd R → isWFmin- R
-- isWFbnd→isWFmin- R RisWFbnd φ {d} d∈φ ¬Σ = RisWFbnd φ (λ x x∈φ → {!   !} ) d d∈φ
--
-- isWFbnd→isWFind- : ∀ {D} (R : 𝓡 D) → isWFbnd R → isWFind- R
-- isWFbnd→isWFind- R isWFbndR φ φ-ind x ¬φx =
-- isWFbndR (∁ φ) (λ y ¬φy → {!   !} ) x ¬φx
--
-- isWFind→isWFbnd : ∀ {D} (R : 𝓡 D) → isWFind R → isWFbnd R
-- isWFind→isWFbnd R isWFindR φ φ-ubd x x∈φ = {!   !}
-- open June26

module ClassicalProperties {D : Set} (R : 𝓡 D) where

-- Double negation shift for accessibility
isWFacc-→¬¬isWFacc :  ∀ {D} (R : 𝓡 D) → isWFacc- R → ¬¬ (isWFacc R)
isWFacc-→¬¬isWFacc {D} R RisWFacc- ¬RisWFacc = {!   !}

¬¬isWFacc→isWFacc- :  ∀ {D} (R : 𝓡 D) → ¬¬ (isWFacc R) → isWFacc- R
¬¬isWFacc→isWFacc- R ¬¬wfAccR = λ x ¬accx → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

-- A strengthening of the above, probably unprovable
isWFacc-→isWFacc : ∀ {D} (R : 𝓡 D) → isWFacc- R → isWFacc R
isWFacc-→isWFacc R RisWF x = {!   !}

isWFacc→isWFmin : ∀ {D} (R : 𝓡 D) → isWFacc R → isWFmin R
isWFacc→isWFmin R RisWFacc P {d} d∈P = f d d∈P (RisWFacc d) where
  f : ∀ x → x ∈ P → is R -accessible x → _
  f x x∈P (acc xac) = {! f y   !}

isWFind→isWFmin : ∀ {D} (R : 𝓡 D) → isWFind R → isWFmin R
isWFind→isWFmin {D} R RisWFind P d∈P =
  let S = Σ[ y ∈ D ] (is R - P -minimal y)
      φ : 𝓟 D
      φ x = x ∈ P → Σ[ y ∈ D ] (y ∈ P × ∀ z → z ∈ P → R z y → S)
      φ-ind : is R -inductive φ
      φ-ind x IH x∈P = {!   !}
    in {!   !} -- RisWFind φ φ-ind _ d∈P

isWFmin→isWFacc- : ∀ {D} (R : 𝓡 D) → isWFmin R → isWFacc- R
isWFmin→isWFacc- {D} R RisWFmin d ¬disRacc with RisWFmin (λ x → ¬ is R -accessible x) (¬disRacc)
... | m ,, ¬misRacc , mismin =
  let f : ¬ ((y : D) → R y m → is R -accessible y) → ¬ ((y : D) → (is R -accessible y → ⊥) → R y m → ⊥)
      f ¬H G = {!   !}
    in f (¬acc R ¬misRacc ) mismin

-- The next two implications are valid only for ¬¬-closed φ
isWFmin→isWFind- : ∀ {D} (R : 𝓡 D) → isWFmin R → isWFind- R
isWFmin→isWFind- {D} R RisWFmin φ φ-ind x ¬φx with RisWFmin (λ y → ¬ φ y) ¬φx
... | d ,, (¬φd , d-min) = {!   !}

isWFmin-→isWFind- : ∀ {D} (R : 𝓡 D) → isWFmin- R → isWFind- R
isWFmin-→isWFind- {D} R RisWFmin- φ φ-ind x ¬φx = RisWFmin- (λ v → ¬ (φ v)) ¬φx f
  where f : ¬ Σ[ d ∈ D ] is R - (∁ φ) -minimal d
        f (d ,, ¬φd , ¬φ⊆¬↓d) = {!   !}

isWFseq→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFseq R → isWFmin- R
isWFseq→isWFmin- R RisWFseq = {!   !}
-- isWFseq→isWFmin- {D} R RisWFseq P {d} d∈P ¬Σmin = RisWFseq f f-dec where
--   -- ∀¬min : ∀ x → x ∈ P →
--   f : ℕ → D
--   f⊆P : ∀ n → f n ∈ P
--   f-dec : is R -decreasing f
--   f zero = d
--   f (succ n) = {!   !}
--   f-dec n = {!   !}
--   f⊆P zero = d∈P
--   f⊆P (succ n) = {!   !}



{- Before 6.26


inductive⁺ : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is (R ⁺) -inductive φ → is R -inductive φ
inductive⁺ R φ φ-ind x H = {!   !}

WF+ : ∀ {A} (R : 𝓡 A) → isWF R → isWF (R ₊)
WF+ {A} R iswfR φ φisR+ind x = ψ→φ where
  ψ : 𝓟 A
  ψ x = φ x × ∀ y → (R ⁺) x y → φ y
  ψ-ind : is R -inductive ψ
  f : ∀ w v → (R ₊) v w → φ v
  f w v (ax₊ Ryw) = {!   !}
  f w v (R+vy ₊, Ryw) = {!   !}
  ψ-ind u ↓u⊆ψ = (φisR+ind u λ { y (ax₊ Ryu) → pr1 (↓u⊆ψ y Ryu) ; y (R+yy' ₊, Ry'u) → {!   !} } ) , {!   !}
  ψ→φ = pr1 (iswfR ψ ψ-ind x)

-- WF+ : ∀ {A} (R : 𝓡 A) → isWF R → isWF (R ₊)
-- WF+ {A} R iswfR φ φisR+ind x = ψ→φ where
--   ψ : 𝓟 A
--   ψ x = ((∀ y → (R ₊) y x → φ y) → φ x) → φ x
--   ψ-ind : is R -inductive ψ
--   f : ∀ w v → (R ₊) v w → φ v
--   f w v (ax₊ Ryw) = {!   !}
--   f w v (R+vy ₊, Ryw) = {!   !}
--   ψ-ind u ↓u⊆ψ H = H (f u) --  (λ y → λ {  (ax₊ Ryu) → ↓u⊆ψ y Ryu (φisR+ind y) ; (R+yu ₊, Rzu) → {!  !} } ) -- x∈ψ {!   !} {!   !} {!   !}
--   ψ→φ = iswfR ψ ψ-ind x (φisR+ind x)

is⊆ind : ∀ {A} (R1 R2 : 𝓡 A) → R1 ⊆ R2
            → ∀ (P : 𝓟 A) → is R1 -inductive P → is R2 -inductive P
is⊆ind R1 R2 R12 P R1ind x H = R1ind x (λ y R1yx → H y (R12 y x R1yx ) )

is⊇indWF : ∀ {A} (R1 R2 : 𝓡 A) → R1 ⊆ R2 → isWF R1
            → ∀ (P : 𝓟 A) → is R2 -inductive P → is R1 -inductive P
is⊇indWF R1 R2 R12 wfR1 P R1ind x H = R1ind x {!   !}

-- is-ind⊆ : ∀ {A} (R : 𝓡 A) (P Q : 𝓟 A)
--             → P ⊆ Q → is R -inductive P → is R -inductive Q
-- is-ind⊆ R P Q P⊆Q Pind x H = P⊆Q x (Pind {!   !} {!   !} )
--
-- WF⊆     : ∀ {A} (R : 𝓡 A) (P Q : 𝓟 A) → isWF R
--             → P ⊆ Q → is R -inductive Q → is R -inductive P
-- WF⊆ R P Q wfR P⊆Q Qind = {!   !}

-- WF+ : ∀ {A} (R : 𝓡 A) → isWF R → isWF (R ⁺)
-- WF+ {A} R iswfR φ φisR⁺ind x = ψ→φ where
--   ψ : 𝓟 A
--   ψ x = ((∀ y → (R ⁺) y x → φ y) → φ x) → φ x
--   ψ-ind : is R -inductive ψ
--   ψ-ind u ↓u⊆ψ H = H (λ y R+yu → {!   !} ) -- x∈ψ {!   !} {!   !} {!   !}
--   ψ→φ = iswfR ψ ψ-ind x (φisR⁺ind x)

  -- ψ : 𝓟 A
  -- ψ x = (∀ y → (R ⁺) y x → φ y)
  -- ψ-ind : is R -inductive ψ
  -- ψ-ind x x∈ψ y R+yx = φisR⁺ind y (λ z R+zy → {!   !} ) -- iswfR ψ {!   !} x



    -- φ' : 𝓟 A
    -- φ' z = (∀ w → R w z → φ w) → (∀ v → (R ⁺) v z → φ v)
    -- φ'isRind : is R -inductive φ'
    -- φ'isRind y H Hy v (ax⁺ x) = Hy v x
    -- φ'isRind y H Hy v (Rvu ,⁺ R+uy) = {!   !} -- φ'isRind y H Hy _ R+uy
    -- ∀φ' : ∀ x → φ' x
    -- ∀φ' x = iswfR φ' φ'isRind x
    -- in λ x → φisR⁺ind x λ y R+yx → ∀φ' y {!   !}
    -- in λ x → φisR⁺ind x λ y R+yz → φ'isRind y (λ z Rzy H → {!   !} ) {!   !}

-- Want: everything accessible from x in reverse is true.

-- is_-_-minimal_ : ∀ {S : Set} (R : 𝓡 S) (A : 𝓟 S) → 𝓟 S
-- is R - A -minimal x = x ∈ A × (∀ y → y ∈ A → R y x → ⊥)
-- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)

lemmaA18φ : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
lemmaA18φ S R A x = (x ∈ A) → Σ[ y ∈ S ] (is R - A -minimal y)
-- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

lemmaA18φ-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (lemmaA18φ S R A)
lemmaA18φ-ind S R A s H s∈A = {!   !}

¬¬lemmaA18φ-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (λ x → ¬¬ (lemmaA18φ S R A x))
¬¬lemmaA18φ-ind S R A s H s∈A = {!   !}

lemmaA18φ2 : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
lemmaA18φ2 S R A x = x ∈ A → ∀ y → R y x → y ∈ A → Σ[ z ∈ S ] (is R - A -minimal z)
-- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

lemmaA18φ2-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (lemmaA18φ2 S R A)
lemmaA18φ2-ind S R A s H s∈A y Rys y∈A with H y Rys y∈A
... | c =  (y ,, y∈A , λ z z∈A Rzy → {! c z  !} )

¬¬lemmaA18φ2-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (λ x → ¬¬ (lemmaA18φ2 S R A x))
¬¬lemmaA18φ2-ind S R A s H s∈A = s∈A (λ s∈A2 → {!   !} )

lemmaA18φ3 : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
lemmaA18φ3 S R A x = x ∈ A → ∀ y → R y x → y ∈ A → Σ[ z ∈ S ] (is R - A -minimal z)
-- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

lemmaA18φ3-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (lemmaA18φ3 S R A)
lemmaA18φ3-ind S R A s H s∈A y Rys y∈A with H y Rys y∈A
... | c =  (y ,, y∈A , λ z z∈A Rzy → {! c z  !} )

¬¬lemmaA18φ3-ind : ∀ (S : Set) (R : 𝓡 S) (A : 𝓟 S) → is R -inductive (λ x → ¬¬ (lemmaA18φ3 S R A x))
¬¬lemmaA18φ3-ind S R A s H s∈A = s∈A (λ s∈A2 → {!   !} )

-- ¬¬A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
--          → ¬¬ Σ[ y ∈ S ] is R - A -minimal y
-- ¬¬A18→ {S} R WFR A x x∈A ¬miny =
--     let φ    = λ y → y ∈ A → ∀ z → z ∈ A → ¬¬ R z y
--         WFRφ : is R -inductive φ
--         WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, y∈A , λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A z z∈A (λ Rzy1 → H y1 Ry1y y1∈A z z∈A {!   !} ) )
--      in  WFR φ WFRφ x x∈A x x∈A (WFR (λ z → (x : R z z) → ⊥) (λ x z x₁ → z x x₁ x₁) x)

A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
         → Σ[ y ∈ S ] is R - A -minimal y
A18→ {S} R WFR A x x∈A =
  let φ    = lemmaA18φ S R A
      WFRφ : is R -inductive φ
      WFRφ y H y∈A = {!   !} -- ¬miny (y ,, y∈A , λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A z z∈A (λ Rzy1 → H y1 Ry1y y1∈A z z∈A {!   !} ) )
   in {!   !}

↓R-dec : ∀ (S : Set) (R : 𝓡 S) → 𝓟 S
↓R-dec S R x = ¬ (∀ y → ¬ R y x) → Σ[ y ∈ S ] R y x
-}




-- Proofs involving classical logic
module ClassicalPropertiesOfRelations where
  open import Classical

  -- This part will be moved elsewhere
  module Preliminaries where
    -- ¬¬Closed : ∀ {A} → 𝓟 A → Set
    -- ¬¬Closed P = ∀ x → ¬¬ P x → P x
    --
    -- ¬¬Lemma : ∀ X → ¬¬ (¬¬ X → X)
    -- ¬¬Lemma X = λ ¬¬X→X → ¬¬X→X (λ ¬¬X → ∅ (¬¬X λ x → ¬¬X→X (K x)))
    --
    -- ¬¬∃→¬∀¬ : ∀ {A} (P : 𝓟 A) → ¬¬ (Σ[ x ∈ A ] P x) → ¬ (∀ x → ¬ P x)
    -- ¬¬∃→¬∀¬ P h x→¬Px = h λ { (y ,, yP) → x→¬Px y yP }
    --
    -- ¬∀¬→¬¬∃ : ∀ {A} (P : 𝓟 A) → ¬ (∀ x → ¬ P x) → ¬¬ (Σ[ x ∈ A ] P x)
    -- ¬∀¬→¬¬∃ P ¬∀¬ ¬∃ = ¬∀¬ λ x Px → ¬∃ (x ,, Px)
    --
    -- DeMorgan∀∃ : Set → Set₁
    -- DeMorgan∀∃ A = ∀ (P : 𝓟 A) → ¬ (∀ x → P x) → Σ[ x ∈ A ] (¬ P x)
    --
    -- MP : ∀ {A} (P : 𝓟 A) → Set
    -- MP {A} P = (∀ x → P x ⊔ ¬ P x) → ¬ (∀ x → ¬ P x) → Σ[ x ∈ A ] P x

    -- DM∀∃ : ∀ {A} (R : 𝓡 A) → Set₁
    -- DM∀∃ {A} R = ∀ x → ∀ (φ : 𝓟 A) → DeMorgan∀∃rel (~R R x) φ

    -- DeMorg→¬¬Closed : ∀ {A} {B : 𝓟 A} → DeMorgan∀∃ A → ¬ (¬¬Closed B) → ⊥
    -- DeMorg→¬¬Closed {A}{B} DeMorg ¬nnC with DeMorg (λ x → ¬¬ (B x) → B x) ¬nnC
    -- ... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

    -- ⟪ is \<<
    _⟪_ : ∀ {A} → 𝓟 A → 𝓟 A → Set
    P ⟪ Q = ¬ (P ⊆ Q) → Σ[ y ∈ _ ] (P y × ¬ Q y)

    -- A relation is well-supported if, for every element in its domain,
    -- and every property, if it's not the case that every element related to x
    -- has the property, then we can exhibit one that doesn't.
    WellSupported : ∀ {A} → 𝓡 A → Set₁
    WellSupported R = ∀ x → ∀ φ → dec φ → (~R R x ⟪ φ)

  open Preliminaries

  module MarkovRelations {A} (R : 𝓡 A) (RisWS : WellSupported R) where

--  Proving that isWFseq → isWFacc
-- Question: Does DeMorgan∀∃ A imply that every predicate on A is decidable?
-- Question: Do we need it to be this general?

    ¬acc→seq : ∀ x → ¬ is R -accessible x → ℕ → A
    ¬acc→seq x ¬accx zero = {!   !}
    ¬acc→seq x ¬accx (succ n) = {!   !}

    isWFseq→isWFacc : isWFseq R → ∀ x → ¬¬ (is R -accessible x)
    isWFseq→isWFacc WFseqR x ¬accx = ¬accx (acc λ y Ryx → {!   !} )

    -- with RisWS x (λ z → R z x) {!   !} (λ H → ¬accx (acc (λ y Ryx → ∅ {!   !})))
    -- ... | y ,, Ryx , pr4 = pr4 Ryx

      -- let ws = RisWS x (λ y → ¬ (is R -accessible y)) λ H → ¬accx {!   !}
      --  in {!   !}

-- Feel free to assume ∀ x → ¬ (φ x) ∨ ¬¬ (φ x)

-- MPrel : ∀ {A} (B P : 𝓟 A) → Set
-- MPrel {A} B P = (∀ x → B x → P x ⊔ ¬ P x) → ¬ (∀ x → B x → ¬ P x) → Σ[ x ∈ A ] (B x × P x)
--
-- fromΣ : ∀ {A} {B : 𝓟 A} {C : Set} → Σ[ x ∈ A ] B x → (∀ x → B x → C) → C
-- fromΣ (x ,, p) f = f x p
--
-- is-ind¬¬ : ∀ {A : Set} (R : 𝓡 A) (φ : 𝓟 A) → (∀ x → DeMorgan∀∃rel (~R R x) φ)  → is R -inductive (λ x → φ x) → is R -inductive (λ x → ¬¬ φ x)
-- is-ind¬¬ R φ DM φ-ind x H ¬φx =
--   let φ-ind' : ¬ (∀ z → R z x → φ z)
--       φ-ind' =  λ G → ¬φx (φ-ind x G )
--       DMcont = DM x φ-ind'
--    in fromΣ DMcont (λ y p → H y (pr1 p) (pr2 p) )
--
-- -- Not provable unless an assumption is added, find the assumption!
-- open import Classical
--
-- MPrel→DMrel : ∀ {A} (B P : 𝓟 A) → MPrel B P → EM A →  DeMorgan∀∃rel B P
-- MPrel→DMrel {A} B P MPBP (in1 x) ¬B⊆P  = {!   !}
-- MPrel→DMrel {A} B P MPBP (in2 ¬x) ¬B⊆P = {!   !}
-- -- MPrel→DMrel B P MPBP WEM ¬B⊆P with MPBP (λ x Bx → in2 λ Px → ¬B⊆P (λ x₁ x₂ → {!   !})) {!   !}
-- -- ... | y ,, By , Py = y ,, By , λ Py → ¬B⊆P λ x Bx → {!   !}

{-
-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
DeMorgan∀∃→DeMorgan∀∃rel : {A : Set} → (B P : 𝓟 A) → DeMorgan∀∃ A → DeMorgan∀∃rel B P
DeMorgan∀∃→DeMorgan∀∃rel {A} B P DeMorg ¬B⊆P with DeMorg {!   !} (λ x→Px → ¬B⊆P (λ x x∈B → x→Px x))
... | x ,, ¬Px = x ,, ( {!   !} , ¬Px) -- (∅ (¬B⊆P {!   !}) , ¬Px)

¬ind→step : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ
             → (∀ x → DeMorgan∀∃rel (~R R x) φ)
             → ∀ x → ¬ φ x → Σ[ y ∈ A ] (~R R x y × ¬ φ y)
¬ind→step R φ φ-ind DeMorg x ¬φx = DeMorg x (λ ↓x⊆φ → ¬φx (φ-ind x ↓x⊆φ ) )

¬ind→seq1 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → ¬ φ x
              → ℕ → A
¬ind→seq2 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → (∀ n → ¬ φ (¬ind→seq1 {A} R φ φ-ind DeMorg x ¬φx n))
¬ind→seq3 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → is R -decreasing (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)

¬ind→seq1 R φ φ-ind DeMorg x ¬φx zero = x
¬ind→seq1 R φ φ-ind DeMorg x ¬φx (succ n) = fst (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n))

¬ind→seq2 R φ φ-ind DeMorg x ¬φx  zero = ¬φx
¬ind→seq2 R φ φ-ind DeMorg x ¬φx (succ n) = pr2 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

-- Not mutually recursive with seq1 and seq2
¬ind→seq3 R φ φ-ind DeMorg x ¬φx n = pr1 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

-- ¬ind→seq = ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) →

WFisWFseq- : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → isWFseq R → is R -inductive φ → (¬¬Closed φ)
                → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → φ x
WFisWFseq- R φ RisWFseq φ-ind DNEφ DeMorg x = DNEφ x
  (λ ¬φx → RisWFseq (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)
                    (¬ind→seq3 R φ φ-ind DeMorg x ¬φx) )

-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
-- Question: Does either of them imply ¬¬Closed φ (possibly using φ is R-inductive)
-- NOT PROVABLE!
DeMorgan∀∃rel→¬¬Closed : ∀ {A} → (B P : 𝓟 A) → DeMorgan∀∃rel B P → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed B P DeMorgRel x ¬¬Bx with DeMorgRel (λ B⊆P →  ¬¬Bx λ Bx → {!   !})
... | y ,, By , ¬Py = {!   !}

DeMorgan∀∃rel→¬¬Closed2 : ∀ {A} → (B : 𝓟 A) → (H : ∀ (P : 𝓟 A) → DeMorgan∀∃rel B P) → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed2 = {!   !}
-}

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg (λ x → ¬¬ (B x) → B x) (λ H → ¬¬Bx (λ Bx → {!   !} ))
-- ... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg B (λ x→Bx → ¬¬Bx (λ Bx → {!   !}))

-- Question: If φ is decidable, does the implication WF→WFseq follow automatically.

-- is_-minimal_ : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S
-- -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
-- is R -minimal {S} x = ∀ y → R y x → ⊥

-- weaklyBounded : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S → Set
-- weaklyBounded R A = Σ[ a ∈ A ] → is R -minimal a

{-
module A18Constructive where

  is_-_-minimal_ : ∀ {S : Set} (R : 𝓡 S) (A : 𝓟 S) → 𝓟 S
  -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
  is R - A -minimal x = x ∈ A × (∀ y → y ∈ A → R y x → ⊥)

  lemmaA18φ : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
  lemmaA18φ S R A x = (x ∈ A) → Σ[ y ∈ S ] (is R - A -minimal y)

  -- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

  A18←seq : ∀ {S : Set} (R : 𝓡 S) → (∀ (A : 𝓟 S) → nonEmpty A → Σ[ x ∈ S ] (x ∈ A × is R - A -minimal x))
           → isWFseq R
  A18←seq R H s s-dec with H (λ x → Σ[ n ∈ ℕ ] (s n ≡ x)) ((s zero ,, zero ,, refl ))
  ... | x ,, (n ,, sn≡x) , ((m ,, sm=x) , p) = p (s (succ n)) (succ n ,, refl ) (transp (R (s (succ n))) sn≡x (s-dec n) )

  A18← : ∀ {S : Set} (R : 𝓡 S) → (∀ (A : 𝓟 S) → nonEmpty A → Σ[ x ∈ S ] (x ∈ A × is R - A -minimal x))
           → ∀ φ → is R -inductive φ → ∀ x → ¬¬ φ x
  -- A18← R H φ φ-ind x ¬φx =

  A18← R H φ φ-ind x ¬φx with H (λ z → ¬ φ z) ((x ,, ¬φx))
  ... | y ,, ¬φy , (_ , pr4) = ¬φy (φ-ind y λ z Rzy → φ-ind z {!   !} )

  A18→ : ∀ {S : Set} (R : 𝓡 S) → isWFind R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
           → ¬¬ Σ[ y ∈ S ] is R - A -minimal y
  A18→ {S} R WFR A x x∈A ¬miny =
    let φ    = λ y → y ∈ A → ∀ z → z ∈ A → ¬¬ R z y
        -- φ₂ : 𝓟 S
        -- φ₂ = λ z → (R z z) → ⊥
        WFRφ : is R -inductive φ
        WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, (y∈A , (λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A y1 y1∈A
                                               λ _ →  H y1 Ry1y y1∈A y1 y1∈A
                                                    (WFR (λ z → (x : R z z) → ⊥) (λ w H₂ Rww → H₂ w Rww Rww) y1))))
        -- WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, y∈A , λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A z z∈A (λ Rzy1 → H y1 Ry1y y1∈A z z∈A {!     !} ) )
        -- WFRφ₂ : is R -inductive φ₂
        -- WFRφ₂ y H Rxx = H y Rxx Rxx
     in  WFR φ WFRφ x x∈A x x∈A (WFR (λ z → (x : R z z) → ⊥) (λ x z x₁ → z x x₁ x₁) x)
-}


-- ↓R-dec : ∀ (S : Set) (R : 𝓡 S) → 𝓟 S
-- ↓R-dec S R x = ¬ (∀ y → ¬ R y x) → Σ[ y ∈ S ] R y x

-- lemmaA18 : ∀ S R A → (∀ a → ↓R-dec S R a) → is R -inductive (lemmaA18φ S R A) -- (λ _ → Σ S (is R - A -minimal_)) -- this is quite messy. don't really understand what I have
-- lemmaA18 S R A ↓Rdec x H x∈A with ↓Rdec x {!   !}
-- ... | y ,, Ryx = {!   !}
-- lemmaA18 {S} R {A} x H with H x {!   !}
-- ... | y ,, Ay , H2 = y ,, Ay , H2

-- A.1.8
-- A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
--          → Σ[ y ∈ S ] is R - A -minimal y
-- A18→ {S} R WFR A x x∈A =
--   let WFRφ = WFR (lemmaA18φ S R A) (lemmaA18 S R A ?) x
--    in WFRφ x∈A -- pr2 WFRφ
-- A18→ {S} R WFR A a a∈A = pr2 (WFR φ {!   !} a ) where
--               φ : S → Set
--               φ x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)


-- A18→ {S} R WFR A a a∈A = WFR φ (lemmaA18 R) a where   -- (λ _ → Σ S (is_-_-minimal_ R A))
--                         φ : (x : S) → Set
--                         φ = λ _ → Σ S (is R - A -minimal_ )
  -- Hint. Use WFR with φ x := x ∈ A → Σ[ y ∈ A ] (is R - A -minimal y)
  -- Try to prove this φ is R-inductive.
  -- Otherwise, try φ x := x ∈ A × Σ[ y ∈ A ] (is R - A -minimal y)
-- A18→ R WFR x y Ryx = WFR (λ x₁ → ⊥) (λ x₁ h → h y {!   !}) x

-- For the converse, try to prove "Every non-empty A contains a R-minimal element" → "isWFseq R"





-- The End
