-- {-# OPTIONS --cubical-compatible #-}

module Logic where

-- BASIC COMBINATORS
I : ∀ {A : Set} → A → A
I x = x

K : ∀ {A B : Set} → A → B → A
K x y = x

KI : ∀ {A B : Set} → A → B → B
KI = K I

-- ∘ is \o
_∘_ : ∀ {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)

-- PROPOSITIONAL CONSTANTS AND CONNECTIVES
-- ⊤ is \top
data ⊤ : Set where
  tt : ⊤

-- ⊥ is \bot
data ⊥ : Set where

-- ∅ is \emptyset
∅ : ∀ {A : Set} → ⊥ → A
∅ ()

-- × is \x
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pr1 : A
    pr2 : B
open _×_ public

-- ⊔ is \lub or \sqcup
data _⊔_ (A B : Set) : Set where
  in1 : A → A ⊔ B
  in2 : B → A ⊔ B

case : ∀ {A B C : Set} → (A → C) → (B → C) → A ⊔ B → C
case f g (in1 x) = f x
case f g (in2 y) = g y

-- ¬ is \lnot
¬_ : Set → Set
¬_ A = A → ⊥

¬¬_ : Set → Set
¬¬_ A = ¬ (¬ A)

-- ↔ is \<->
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

-- EQUALITY
-- ≡ is \== or \equiv
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

~ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
~ refl = refl

_!_ : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
refl ! bc = bc

_!~_ : ∀ {A : Set} {x y z : A} → x ≡ y → z ≡ y → x ≡ z
p !~ q = p ! ~ q

_~!_ : ∀ {A : Set} {x y z : A} → y ≡ x → y ≡ z → x ≡ z
p ~! q = ~ p ! q

transp : ∀ {A : Set} (B : A → Set) {a1 a2 : A} → a1 ≡ a2 → B a1 → B a2
transp B refl = I

cong : ∀ {A B : Set} (f : A → B) {a1 a2 : A} → a1 ≡ a2 → f a1 ≡ f a2
cong f refl = refl

cong2 : ∀ {A B C : Set} (f : A → B → C)
         {a1 a2 : A} → a1 ≡ a2 → {b1 b2 : B} → b1 ≡ b2 → f a1 b1 ≡ f a2 b2
cong2 f refl refl = refl

cong3 : ∀ {A B C D : Set} (f : A → B → C → D) {a1 a2 b1 b2 c1 c2}
          → a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → f a1 b1 c1 ≡ f a2 b2 c2
cong3 f refl refl refl = refl

-- POINTWISE EQUALITY OF FUNCTIONS
-- ≅ is \~= or \cong
_≅_ : ∀ {A B : Set} (f g : A → B) → Set
f ≅ g = ∀ x → f x ≡ g x

refl≅ : ∀ {A B : Set} {f : A → B} → f ≅ f
refl≅ x = refl
symm≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → g ≅ f
symm≅ fg x = ~ (fg x)
tran≅ : ∀ {A B : Set} {f g h : A → B} → f ≅ g → g ≅ h → f ≅ h
tran≅ fg gh x = (fg x) ! (gh x)

infix 10 _↔_
infix 14 _⊔_
infix 15 _×_
infix 18 _≡_
infix 18 _≅_
infix 22 _!_
infix 25 _∘_
infix 10 _,_
infix 17 ¬_

-- SIGMA TYPE
open import Agda.Builtin.Sigma 

Σ-syntax : (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- THE END
