module Wellfounded where

open import Logic
open import Lifting
open import Predicates
open import Relations

{- 2024.06.28.
Questions to investigate.
1. Does ¬¬ R-accessible x → R-accessible x ?
2. Does ¬¬WFacc R → WFacc R ?
3. Does WFacc- R → ¬¬WFacc R ?
4. What's the role of ¬¬-closedness in the implication WFmin→WFind ?
5. How should the "minimality" concept be changed to be useful?
6. Does WFseq → WFmin- ?
-}


{- 6.26  Exercise A1.18 from the accessible point of view.
-}

module June26 {D : Set} (R : 𝓡 D) where

  is_-_-minimal_ : 𝓟 D → 𝓟 D
  -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
  is_-_-minimal_ φ x = x ∈ φ × (∀ y → y ∈ φ → R y x → ⊥)

  isWFmin : Set₁
  isWFmin = ∀ (P : 𝓟 D) → ∀ {d : D} → d ∈ P → Σ[ y ∈ D ] is_-_-minimal_ P y

  isWFmin- : Set₁
  isWFmin- = ∀ (P : 𝓟 D) → ∀ {d : D} → d ∈ P → ¬¬ (Σ[ y ∈ D ] is_-_-minimal_ P y)

  isWFind- : Set₁
  isWFind- = ∀ (φ : 𝓟 D) → (is_-inductive_ R φ) → ∀ x → ¬¬ (φ x)

  isWFacc- : Set
  isWFacc- = ∀ x → ¬¬ (is R -accessible x)

  acc⊆ind : ∀ (φ : 𝓟 D) → is R -inductive φ → is_-accessible_ R ⊆ φ
  acc⊆ind φ φisR-ind x (acc IH) = φisR-ind x (λ y Ryx → acc⊆ind φ φisR-ind y (IH y Ryx) )

  -- ind⊆acc : ∀ (φ : 𝓟 D) → is R -inductive φ →

  isWFacc-→isWFind- : isWFacc- → isWFind-
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- → isWFacc-
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → is R -accessible y) (λ x → acc)

  ¬acc : ∀ {x : D} → ¬ (is R -accessible x) → ¬ (∀ y → R y x → is R -accessible y)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  -- Easy
  -- ∁∁indWF : isWFind R → ∀ (P : 𝓟 D) → is R -inductive P → is R -inductive (∁ (∁ P))
  -- ∁∁indWF RisWF P PisRind x H ¬Px = ¬Px (RisWF P PisRind x)

  -- Hard
  -- ∁∁ind : ∀ (P : 𝓟 D) → is R -inductive P → is R -inductive (∁ (∁ P))
  -- ∁∁ind P PisRind x H ¬Px = ¬Px {!   !}

  -- Obvious
  -- isWFacc→isWFacc- : isWFacc R → isWFacc- R
  -- isWFacc→isWFacc- isWFacc x ¬accx = ¬accx (isWFacc x)

open June26

-- lemma-acc :  ∀ {D} (R : 𝓡 D) → isWFacc R → ∀ x
--                → (∀ y → R y x → ¬¬ (is R -accessible y)) → → ¬¬ (is R -accessible x)
-- lemma-acc wfR

-- Double negation shift for accessibility
isWFacc-→¬¬isWFacc :  ∀ {D} (R : 𝓡 D) → isWFacc- R → ¬¬ (isWFacc R)
isWFacc-→¬¬isWFacc {D} R RisWFacc- ¬RisWFacc = {!   !}

-- A strengthening of the above, probably unprovable
isWFacc-→isWFacc : ∀ {D} (R : 𝓡 D) → isWFacc- R → isWFacc R
isWFacc-→isWFacc R RisWF x = {!   !}

isWFacc→isWFmin : ∀ {D} (R : 𝓡 D) → isWFacc R → isWFmin R
isWFacc→isWFmin R RisWFacc P {d} d∈P = f d d∈P (RisWFacc d) where
  f : ∀ x → x ∈ P → is R -accessible x → _
  f x x∈P (acc xac) = {! f y   !}

isWFacc→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFacc R → isWFmin- R
isWFacc→isWFmin- R RisWFacc P {d} d∈P = f d d∈P (RisWFacc d) where
  f : ∀ x → x ∈ P → is R -accessible x → _
  f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

isWFacc-→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFacc- R → isWFmin- R
isWFacc-→isWFmin- {D} R RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
  where f : ∀ x → x ∈ P → is R -accessible x → ¬¬ Σ[ y ∈ D ] (is R - P -minimal y)
        f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

isWFind→isWFmin : ∀ {D} (R : 𝓡 D) → isWFind R → isWFmin R
isWFind→isWFmin {D} R RisWFind P d∈P =
  let S = Σ[ y ∈ D ] (is R - P -minimal y)
      φ : 𝓟 D
      φ x = x ∈ P → Σ[ y ∈ D ] (y ∈ P × ∀ z → z ∈ P → R z y → S)
      φ-ind : is R -inductive φ
      φ-ind x IH x∈P = {!   !}
    in {!   !} -- RisWFind φ φ-ind _ d∈P

isWFind→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFind R → isWFmin- R
isWFind→isWFmin- {D} R RisWFind P d∈P = -- ¬Σmin =
  let φ : 𝓟 D
      φ x = x ∈ P → ¬¬ Σ[ y ∈ D ] (is R - P -minimal y)
      φ-ind : is R -inductive φ
      φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
    in RisWFind φ φ-ind _ d∈P

isWFind-→isWFmin- : ∀ {D} (R : 𝓡 D) → isWFind- R → isWFmin- R
isWFind-→isWFmin- {D} R RisWFind- P {d} d∈P = -- ¬Σmin =
  let φ : 𝓟 D
      φ x = x ∈ P → ¬¬ Σ[ y ∈ D ] (is R - P -minimal y)
      φ-ind : is R -inductive φ
      φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
    in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

-- isWFmin→isWFacc : ∀ {D} (R : 𝓡 D) → isWFmin R → isWFacc R
-- isWFmin→isWFacc {D} R RisWFmin = ?

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

isWFmin-→isWFseq : ∀ {D} (R : 𝓡 D) → isWFmin- R → isWFseq R
isWFmin-→isWFseq {D} R RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
  where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
        f : ¬ Σ[ d ∈ D ] is R - B -minimal d
        f (d ,, dRBmin) with pr1 dRBmin
        ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                              (transp (R (s (succ n))) sn≡d (s-dec n))

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
