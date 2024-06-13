module Lifting where

open import Logic

-- LIFTING MONAD
-- ↑ is \u
-- ↑ X = X + 1 (in types) = X ⊔ {*} (in sets) = Maybe X (in Haskell)
data ↑ (A : Set) : Set where
  i : A → ↑ A
  o : ↑ A

-- The generic eliminator for ↑
io : ∀ {A B : Set} → (A → B) → B → ↑ A → B
io f b (i x) = f x
io f b o = b

-- The map function AKA functorial action
↑→ : ∀ {A B : Set} → (A → B) → ↑ A → ↑ B
↑→ f (i x) = i (f x)
↑→ f o = o

-- Preservation of identity
↑→≅I : ∀ {A} {f : A → A} → f ≅ I → ↑→ f ≅ I
↑→≅I f≅I (i x) = cong i (f≅I x)
↑→≅I f≅I o     = refl

-- Presevation of pointwise equality
↑→≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → ↑→ f ≅ ↑→ g
↑→≅ fg (i x) = cong i (fg x)
↑→≅ fg o = refl

-- Preservation of composition
↑→∘ : ∀ {A B C : Set} (f : A → B) (g : B → C) → ↑→ (g ∘ f) ≅ ↑→ g ∘ ↑→ f
↑→∘ f g (i x) = refl
↑→∘ f g o = refl

-- Combination of the two properties above
↑→≅∘ : ∀ {A B C} (f : A → B) (g : B → C) {h} → (h ≅ g ∘ f) → (↑→ h ≅ ↑→ g ∘ ↑→ f)
↑→≅∘ f g h≅g∘f = tran≅ (↑→≅ h≅g∘f) (↑→∘ f g)

-- Naturality of the i constructor
i-nat : ∀ {A B : Set} → (f : A → B) → i ∘ f ≅ ↑→ f ∘ i
i-nat f x = refl

-- INTEGERS AND FINITE SETS
-- ℕ is \bN
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

Fin : ℕ → Set
Fin zero = ⊥
Fin (succ n) = ↑ (Fin n)

∘^ : ∀ {A : Set} → ℕ → (A → A) → (A → A)
∘^ zero f = I
∘^ (succ n) f = f ∘ (∘^ n f)
