module Wellfounded where

open import Logic
open import Predicates
open import Relations

inductive⁺ : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is (R ⁺) -inductive φ → is R -inductive φ
inductive⁺ R φ φ-ind = {!   !} 

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
