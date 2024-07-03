module DimensionAlgebra where

open import Logic
open import Lifting
open import Predicates
open import RelationsCore

{-
The following encodes the sequence
"propositions, binary relations, quaternary relations, senary relations, ..."
evenRel : Set₁ → ℕ → Set₁
evenRel A zero = Set
evenRel A (succ n) = A → A → evenRel A n

-- Inductive definition of an n-relation
Rel* : ℕ → Set₁ → Set₁
Rel* zero A = A
Rel* (succ n) A = A → A → Rel* n A
-}

data Rel* (D : Set) : ℕ → Set where
  Dom : D → Rel* D zero
  Hom : ∀ n → (D → D → Rel* D n) → Rel* D (succ n)

Indℕ : ∀ {P : 𝓟 ℕ} → P zero → (∀ n → P n → P (succ n)) → ∀ n → P n
Indℕ p0 pS zero = p0
Indℕ p0 pS (succ n) = pS n (Indℕ p0 pS n)

Set* : ℕ → Set₁
Set* zero = Set
Set* (succ n) = Set* n → Set* n → Set

data Cell* : ∀ (n : ℕ) (S : Set* n) → Set where
  zeroCell : ∀ S → S                         → Cell* zero S
  -- succCell : ∀ S (n : ℕ) → Cell* (succ n) (λ x y → )

nCube : Set₁ → ℕ → Set₁
nCube A zero = A
nCube A (succ n) = nCube A n → nCube A n → Set

-- Uniformly Stratified Types
nFrame : Set₁ → Set₁
nFrame A = ∀ n → nCube A n

nCell : ∀ {A} → nFrame A → ℕ → Set₁
nCell Φ zero = {! Φ zero   !}
nCell Φ (succ n) = {!   !}

{-
To do
1. Define an "n-cube of types".  0-cells are types. 1-cells are equivalences. etc.
2. Define an "n-cube of terms", which would in some sense "inhabit" the former.
3. Define higher groupoid operators on the cubes
4. Validate every law of the dimension algebra
5. Construct a model in Set*
-}
