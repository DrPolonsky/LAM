open import BasicLogic
open import SetOperations
open import BasicDatatypes
open import Functions

module AlgebraicStructures where

isAssociative : ∀ {A : Set} → Pred (A → A → A)
isAssociative _⊙_ = ∀ x y z → (x ⊙ y) ⊙ z ≡ x ⊙ (y ⊙ z)

isCommutative : ∀ {A : Set} → Pred (A → A → A)
isCommutative _⊙_ = ∀ x y → x ⊙ y ≡ y ⊙ x

isIdempotent : ∀ {A : Set} → Pred (A → A → A)
isIdempotent _⊙_ = ∀ x → x ⊙ x ≡ x

record Semigroup {A : Set} (_⊙_ : A → A → A) : Set where
  constructor SGRP
  field
    assoc : isAssociative _⊙_

  _⊙≡_ : ∀ x {y} {z} → y ≡ z → x ⊙ y ≡ x ⊙ z
  x ⊙≡ refl y = refl (x ⊙ y)

  _≡⊙_ : ∀ {x} {y} → x ≡ y → ∀ z → x ⊙ z ≡ y ⊙ z
  refl x ≡⊙ z = refl (x ⊙ z)

  isUnit : A → Set
  isUnit e = ∀ x → (e ⊙ x ≡ x) ∧ (x ⊙ e ≡ x)

  unitsAreUnique : ∀ e e' → isUnit e → isUnit e' → e ≡ e'
  unitsAreUnique e1 e2 ue1 ue2 = pr2 (ue2 e1) ~! pr1 (ue1 e2)

record Monoid {A : Set} (_⊙_ : A → A → A) : Set where
  constructor MON
  field
    sgrp : Semigroup _⊙_
    unit : A
    unitLaw : Semigroup.isUnit sgrp unit

  isInverse : (A → A) → Set
  isInverse i = ∀ x → (x ⊙ i x) ≡ unit ∧ (i x ⊙ x) ≡ unit

  -- inversesAreUnique : ∀ (i i' : A → A) → isInverse i → isInverse i' → i ≅ i'
  -- inversesAreUnique i1 i2 inv1 inv2 x = {!   !}

record Group {A : Set} (_⊙_ : A → A → A) : Set where
  constructor GRP
  field
    mon : Monoid _⊙_
    inv : A → A
    invLaw : Monoid.isInverse mon inv

record AbelianGroup {A : Set} (_⊙_ : A → A → A) : Set where
  constructor ABGRP
  field
    grp : Group _⊙_
    comm : isCommutative _⊙_

record ICMonoid {A : Set} (_⊙_ : A → A → A) : Set where
  constructor ICMON
  field
    mon  : Monoid _⊙_
    comm : isCommutative _⊙_
    idem : isIdempotent  _⊙_

-- ⊕ is \o+, ⊙ is \o.
record Ring {A : Set} (_⊕_ : A → A → A) (_⊙_ : A → A → A) : Set where
  constructor RING
  field
    abgrp⊕ : AbelianGroup _⊕_
    mon⊙ : Monoid _⊙_
    distL : ∀ x y z → x ⊙ (y ⊕ z) ≡ (x ⊙ y) ⊕ (x ⊙ z)
    distR : ∀ x y z → (x ⊕ y) ⊙ z ≡ (x ⊙ z) ⊕ (y ⊙ z)

-- ℤ is \bZ
data ℤ : Set where
  pos : ℕ → ℤ
  neg₁ : ℕ → ℤ       -- neg₁ n represents -(n+1)

addℤ : ℤ → ℤ → ℤ
addℤ (pos zero)       y              = y
addℤ (pos (succ x))  (pos y)         = pos (succ (x + y))
addℤ (pos (succ x))  (neg₁ zero)     = pos x
addℤ (pos (succ x))  (neg₁ (succ y)) = addℤ (pos x) (neg₁ y)
addℤ (neg₁ x)        (pos zero)      = neg₁ x
addℤ (neg₁ zero)     (pos (succ y))  = pos y
addℤ (neg₁ (succ x)) (pos (succ y))  = addℤ (neg₁ x) (pos y)
addℤ (neg₁ x)        (neg₁ y)        = neg₁ (succ (x + y))

zeroℤ : ℤ
zeroℤ = pos 0

negℕ : ℕ → ℤ
negℕ 0 = pos 0
negℕ (succ x) = neg₁ x

negℤ : ℤ → ℤ
negℤ (pos zero) = pos zero
negℤ (pos (succ n)) = neg₁ n
negℤ (neg₁ n) = pos (succ n)
