module UnaryPredicates where

open import Logic

-- The type of predicates on a given set A, AKA the powerset of A
-- (Note that the output A → Set is a type in a bigger universe Set₁)

𝓟 : Set → Set₁
𝓟 A = A → Set

-- Membership relation
-- ∈ is \in
_∈_ : ∀ {A : Set} → A → 𝓟 A → Set
a ∈ P = P a
infix 18 _∈_

-- ∉ is \inn
_∉_ : ∀ {A : Set} → A → 𝓟 A → Set
a ∉ P = ¬ a ∈ P

-- Subset relation
-- ⊆ is \sub=
_⊆_ : ∀ {A : Set} → 𝓟 A → 𝓟 A → Set
A ⊆ B = ∀ x → x ∈ A → x ∈ B
infix 16 _⊆_

-- Creating a new module to lighten up the notation
module LogicOps {U : Set} where

  -- The empty subset ∅ ⊆ U.
  -- Corresponds to the constantly-false predicate.
  K⊥ : 𝓟 U
  K⊥ _ = ⊥

  -- The full subset U ⊆ U.
  -- Corresponds to the constantly-true predicate.
  K⊤ : 𝓟 U
  K⊤ _ = ⊤

  -- Logical operators on subsets
  -- ∩ is \cap
  _∩_ : 𝓟 U → 𝓟 U → 𝓟 U
  A ∩ B = λ x  →  x ∈ A  ×  x ∈ B
  infix 17 _∩_

  -- Union.  Corresponds to disjunction.
  -- ∪ is \cup
  _∪_ : 𝓟 U → 𝓟 U → 𝓟 U
  A ∪ B = λ x  →  x ∈ A  ⊔  x ∈ B
  infix 17 _∪_

  -- Complement. Corresponds to negation.
  -- ∁ is \C
  ∁_ : 𝓟 U → 𝓟 U
  ∁ A = λ x → x ∉ A
  infix 19 ∁_

  -- Extensional equivalence of predicates.
  -- ⇔ is \<=>
  _⇔_ : 𝓟 U → 𝓟 U → Set
  A ⇔ B = A ⊆ B × B ⊆ A

  infix 15 _⇔_

  predEq : ∀ {A B : 𝓟 U} →   A ⇔ B   ↔   ∀ x → x ∈ A ↔ x ∈ B
  predEq = ( (λ A≃B → λ x → (λ ax → pr1 A≃B x ax ) , (λ bx → pr2 A≃B x bx ) )
           , (λ AB → (λ x xa → pr1 (AB x) xa) , (λ x xb → pr2 (AB x) xb)) )

open LogicOps public

-- dec : ∀ {A} → 𝓟 A → Set
-- dec P = ∀ x → EM (P x) -- P x ∨ ¬ P x
