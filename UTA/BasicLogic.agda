module BasicLogic where


-- Basic Combinators

I : ∀ {A : Set} → A → A
I x = x

K : ∀ {A B : Set} → A → B → A
K x y = x

-- ∘ is \circ or \o
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)
infixl 25 _∘_


-- Logical Connectives

-- ⊤ is \top
data ⊤ : Set where
  tt : ⊤

-- ⊥ is \bot
data ⊥ : Set where

-- Next time:
exFalso : ∀ {A : Set} → ⊥ → A
exFalso ()

-- ∧ is \and
data _∧_ (A B : Set) : Set where
  _,_ : A → B → A ∧ B
infixr 12 _∧_

pr1 : ∀ {A B : Set} → A ∧ B → A
pr1 (x , y) = x

pr2 : ∀ {A B : Set} → A ∧ B → B
pr2 (x , y) = y

-- ∨ is \or
data _∨_ (A B : Set) : Set where
  in1 : A → A ∨ B
  in2 : B → A ∨ B
infixr 10 _∨_

case : ∀ {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
case f g (in1 x) = f x
case f g (in2 y) = g y

-- ¬ is \lnot  (** NOTE the l in \lnot **)
¬_ : Set → Set
¬_ A = A → ⊥
infix 30 ¬_

-- ↔ is \<->
_↔_ : Set → Set → Set
A ↔ B = (A → B) ∧ (B → A)

infixl 8 _↔_

-- Classical Principles
EM : Set → Set
EM A = A ∨ ¬ A

WEM : Set → Set
WEM A = ¬ A ∨ ¬ ¬ A

DNE : Set → Set
DNE A = ¬ ¬ A → A

-- Equality
-- ≡ is \==
data _≡_ {A : Set} : A → A → Set where
  refl : ∀ (x : A) → x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}
infix 19 _≡_

~ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
~ (refl _) = refl _

_!_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl _ ! yz = yz

_!~_ : ∀ {A : Set} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p !~ q = p ! ~ q

_~!_ : ∀ {A : Set} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
p ~! q = ~ p ! q

transp : ∀ {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
transp P (refl _) p = p

infixl 18 _!_

-- Extensional equality of functions
-- ≅ is \~=

_≅_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ≅ g = ∀ x → f x ≡ g x

ext : ∀ {A B : Set} (f : A → B) → ∀ {x y : A} → x ≡ y → f x ≡ f y
ext f (refl x) = refl (f x)
