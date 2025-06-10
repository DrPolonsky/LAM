{-# OPTIONS --guardedness #-}
module Homega.LambdaHomega where

open import Logic
open import Lifting
open import Lambda
open import Reduction
open import Relations.Core

open import Homega.Unsolvable
open import Homega.LambdaH
open import Homega.OmegaRule


_=βΩω_ : ΛRel
_=βΩω_ = ωTh (_=𝓗_)

data _=𝓗ω_ {X : Set} : Λ X → Λ X → Set where
  Ω𝓗 : ∀ {s t : Λ X} → s =𝓗 t → s =𝓗ω t
  _,𝓗ω_ : ∀ {u v w : Λ X} → ωΛRel _=𝓗ω_ u v → v =𝓗ω w → u =𝓗ω w

var𝓗ω : ∀ {X} (x : X) → var x =𝓗ω var x
var𝓗ω x = Ω𝓗 refl𝓗

-- Conjecture
𝓗ω-standardization : ∀ {X} {s t : Λ X} → s =βΩω t → s =𝓗ω t
𝓗ω-standardization = {!   !}

-- abs𝓗ω : ∀ {X} {r1 r2 : Λ (↑ X)} → r1 =𝓗ω r2 → abs r1 =𝓗ω abs r2
-- abs𝓗ω (Ω𝓗 x) = Ω𝓗 (abs𝓗 x)
-- abs𝓗ω (om ,𝓗ω r12) = (λ ξ → abs𝓗ω {! om (lift ξ)   !} ) ,𝓗ω (abs𝓗ω r12)
--
-- refl=𝓗Ω : ∀ {X} → reflR (_=𝓗ω_ {X})
-- refl=𝓗Ω (var x) = Ω𝓗 refl𝓗
-- refl=𝓗Ω (app s t) = {!   !}
-- refl=𝓗Ω (abs r) = {!   !}
-- symm=𝓗Ω : ∀ {X} → symmR (_=𝓗ω_ {X})
-- symm=𝓗Ω = {!   !}
-- tran=𝓗Ω : ∀ {X} → tranR (_=𝓗ω_ {X})
-- tran=𝓗Ω = {!   !}
