module LambdaExamples where

open import Logic
open import Lifting
open import Lambda

module TypedExamples (O : Set) where

  A : Set
  A = (O → O) → O → O
  m : A
  -- m = λ (f : O → O) (x : O) → x
  -- m = λ (f : O → O) (x : O) → f x
  m = λ (f : O → O) (x : O) → f (f x )

  B : Set → Set → Set
  B α β = ((α → β) → α) → (α → β) → β

  b : ∀ α β → B α β
  b α β = λ x y → y (x y )
  b α β = λ x y → y (x λ z → y z )
  b α β = λ x y → y (x λ z → y (x λ z' → y z )  )
  b α β = λ x y → y (x λ z → y (x λ z' → y z' )  )
  b α β = λ x y → y (x λ z → y (x λ z' → y (x λ z'' → y z )  )  )
  b α β = λ x y → y (x λ z → y (x λ z' → y (x λ z'' → y z' )  )  )
  b α β = λ x y → y (x λ z → y (x λ z' → y (x λ z'' → y z'' )  )  )

--
-- data 𝔹 : Set where
--   bT : 𝔹
--   bF : 𝔹
--
-- -- V = 𝔹 where v₀ = bF and v₁ = bT
--
-- -- term1 = "λx. (v₀ (x v₁))"
-- term1 : Λ 𝔹
-- term1 = abs (app (var (i bF) ) (app (var o ) (var (i bT) ) ) )
--
-- -- term2 = "λxλy.y(λz.z(λa.ax)y)x"
-- term2 : Λ₀
-- term2 = abs (abs (app (app (var o ) (abs (app (app (var o) (abs (app (var o) (var (i (i (i o ) ) ) ) ) ) ) (var (i o)) ) ) ) (var (i o ) ) ) )
