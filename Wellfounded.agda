module Wellfounded where

open import Logic
open import Predicates
open import Relations

inductive⁺ : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is (R ⁺) -inductive φ → is R -inductive φ
inductive⁺ R φ φ-ind x H = {!   !}

WF+ : ∀ {A} (R : 𝓡 A) → isWF R → isWF (R ₊)
WF+ {A} R iswfR φ φisR+ind x = ψ→φ where
  ψ : 𝓟 A
  ψ x = ((∀ y → (R ₊) y x → φ y) → φ x) → φ x
  ψ-ind : is R -inductive ψ
  f : ∀ w v → (R ₊) v w → φ v
  f w v (ax₊ Ryw) = {!   !}
  f w v (R+vy ₊, Ryw) = {!   !}
  ψ-ind u ↓u⊆ψ H = H (f u) --  (λ y → λ {  (ax₊ Ryu) → ↓u⊆ψ y Ryu (φisR+ind y) ; (R+yu ₊, Rzu) → {!  !} } ) -- x∈ψ {!   !} {!   !} {!   !}
  ψ→φ = iswfR ψ ψ-ind x (φisR+ind x)

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
