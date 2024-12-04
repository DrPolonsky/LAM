{-# OPTIONS --type-in-type #-}

open import Logic
open import Lifting
open import Datatypes
open import Predicates using (𝓟)
open import Relations.Core using (Rel)

-- Bootstrapping isomorphisms
module QADT.IsoBoot where

data 𝕌 (V : Set) : Set where
  𝕍∙ : V → 𝕌 V
  ⊥∙ : 𝕌 V
  ⊤∙ : 𝕌 V
  ×∙ : 𝕌 V → 𝕌 V → 𝕌 V
  ⊔∙ : 𝕌 V → 𝕌 V → 𝕌 V

SetEnv : Set → Set
SetEnv V = V → Set

RelEnv : ∀ {V : Set} → Rel (SetEnv V) (SetEnv V)
RelEnv {V} ρ0 ρ1 = ∀ v → Rel (ρ0 v) (ρ1 v)

-- idEnv : ∀ {V} (ρ : SetEnv V) → RelEnv ρ ρ
-- idEnv ρ = {!   !}

SetEnvElem : ∀ {V} → SetEnv V → Set
SetEnvElem {V} ρ = ∀ v → ρ v

RelEnvProof : ∀ {V} {ρ0 ρ1 : SetEnv V} → RelEnv ρ0 ρ1 → SetEnvElem ρ0 → SetEnvElem ρ1 → Set
RelEnvProof {V} {ρ0} {ρ1} ρ* e0 e1 = ∀ (v : V) → ρ* v (e0 v) (e1 v)

⟦_⟧Set : ∀ {V} → 𝕌 V → SetEnv V → Set
⟦ 𝕍∙ x ⟧Set ρ = ρ x
⟦ ⊥∙ ⟧Set ρ = ⊥
⟦ ⊤∙ ⟧Set ρ = ⊤
⟦ ×∙ A B ⟧Set ρ = ⟦ A ⟧Set ρ × ⟦ B ⟧Set ρ
⟦ ⊔∙ A B ⟧Set ρ = ⟦ A ⟧Set ρ ⊔ ⟦ B ⟧Set ρ

⟦_⟧Rel : ∀ {V} (A : 𝕌 V) {ρ0 ρ1 : SetEnv V}
          → RelEnv ρ0 ρ1 → Rel (⟦ A ⟧Set ρ0) (⟦ A ⟧Set ρ1)
⟦ 𝕍∙ x ⟧Rel ρ* = ρ* x
⟦ ⊥∙ ⟧Rel ρ* ()
⟦ ⊤∙ ⟧Rel ρ* _ _ = ⊤
⟦ ×∙ A B ⟧Rel ρ* (a0 , b0) (a1 , b1) = ⟦ A ⟧Rel ρ* a0 a1 × ⟦ B ⟧Rel ρ* b0 b1
⟦ ⊔∙ A B ⟧Rel ρ* (in1 a0) (in1 a1) = ⟦ A ⟧Rel ρ* a0 a1
⟦ ⊔∙ A B ⟧Rel ρ* (in1 _) (in2 _) = ⊥
⟦ ⊔∙ A B ⟧Rel ρ* (in2 _) (in1 _) = ⊥
⟦ ⊔∙ A B ⟧Rel ρ* (in2 b0) (in2 b1) = ⟦ B ⟧Rel ρ* b0 b1



data 𝕌* {V : Set} : 𝕌 V → 𝕌 V → Set where
  𝕍* : ∀ v → 𝕌* (𝕍∙ v) (𝕍∙ v)
  ⊥* : 𝕌* ⊥∙ ⊥∙
  ⊤* : 𝕌* ⊤∙ ⊤∙
  ×* : ∀ {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1) → 𝕌* (×∙ A0 B0) (×∙ A1 B1)
  ⊔* : ∀ {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1) → 𝕌* (⊔∙ A0 B0) (⊔∙ A1 B1)

-- ⟦_⟧*Set : ∀ {V} {A B : 𝕌 V} → 𝕌* A B → (ρ : SetEnv V) (idρ : RelEnv ρ ρ) → Rel (⟦ A ⟧Set ρ) (⟦ B ⟧Set ρ)
-- ⟦ 𝕍* v ⟧*Set ρ a b = {!   !}
-- ⟦ ⊤* ⟧*Set ρ a b = {!   !}
-- ⟦ ×* A* A*₁ ⟧*Set ρ a b = {!   !}
-- ⟦ ⊔* A* A*₁ ⟧*Set ρ a b = {!   !}

refl𝕌* : ∀ {V : Set} (A : 𝕌 V) → 𝕌* A A
refl𝕌* (𝕍∙ x) = 𝕍* x
refl𝕌* ⊥∙ = ⊥*
refl𝕌* ⊤∙ = ⊤*
refl𝕌* (×∙ A B) = ×* (refl𝕌* A) (refl𝕌* B)
refl𝕌* (⊔∙ A B) = ⊔* (refl𝕌* A) (refl𝕌* B)

⟦_⟧*Set : ∀ {V} {A B : 𝕌 V} → 𝕌* A B → {ρ0 ρ1 : SetEnv V} (ρ* : RelEnv ρ0 ρ1)
           → Rel (⟦ A ⟧Set ρ0) (⟦ B ⟧Set ρ1)
⟦ 𝕍* v ⟧*Set ρ* = ρ* v
⟦ ⊥* ⟧*Set ρ* ()
⟦ ⊤* ⟧*Set ρ* _ _ = ⊤
⟦ ×* A* B* ⟧*Set ρ* (a0 , b0) (a1 , b1) = ⟦ A* ⟧*Set ρ* a0 a1 × ⟦ B* ⟧*Set ρ* b0 b1
⟦ ⊔* A* B* ⟧*Set ρ* (in1 a0) (in1 a1) = ⟦ A* ⟧*Set ρ* a0 a1
⟦ ⊔* A* B* ⟧*Set ρ* (in1 _) (in2 _) = ⊥
⟦ ⊔* A* B* ⟧*Set ρ* (in2 _) (in1 _) = ⊥
⟦ ⊔* A* B* ⟧*Set ρ* (in2 b0) (in2 b1) = ⟦ B* ⟧*Set ρ* b0 b1

-- ⟦_⟧*Rel : ∀ {V} {A B : 𝕌 V} (R : 𝕌* A B) → {ρ0 ρ1 : SetEnv V} (ρ* : RelEnv ρ0 ρ1)
--            → (e0 : SetEnvElem ρ0) (e1 : SetEnvElem ρ1)
--            → RelEnvProof ρ* e0 e1 → ⟦ R ⟧*Set ρ* e0 e1

-- ⟦_⟧*Rel : ∀ {V} {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) → {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1)
--             →  𝕌* A B → (ρ : SetEnv V) → Rel (⟦ A ⟧Set ρ) (⟦ B ⟧Set ρ)

SetEnv𝕌 : ∀ V → SetEnv V
SetEnv𝕌 V = λ v → 𝕌 V

RelEnv𝕌* : ∀ V → RelEnv (SetEnv𝕌 V) (SetEnv𝕌 V)
RelEnv𝕌* V = λ v → 𝕌*

T𝕌⁰ : ∀ (A : 𝕌 ⊥) → Rel (⟦ A ⟧Set ∅) (⟦ A ⟧Set ∅)
T𝕌⁰ A = ⟦ A ⟧Rel λ ()

T𝕌 : ∀ {V} (A : 𝕌 V) (ρ : SetEnv V) → Rel (⟦ A ⟧Set ρ) (⟦ A ⟧Set ρ)
T𝕌 A ρ = {!   !}

-- Id𝕌 ρ = 𝕌*
--
--
-- Eq𝕌 : ∀ {V} → Rel (𝕌 V) (𝕌 V)
-- Eq𝕌 {V} = {!   !}






-- the end
