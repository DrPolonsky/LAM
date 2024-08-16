module SetOperations where

open import BasicLogic

-- The type of predicates on a given set A, AKA the powerset of A
-- (Note that the output A → Set is a type in a bigger universe Set₁)
Pred : Set → Set₁
Pred A = A → Set

-- Membership relation
-- ∈ is \in
_∈_ : ∀ {U : Set} → U → Pred U → Set
a ∈ A = A a
infix 15 _∈_

-- Subset relation
-- ⊆ is \sub=
_⊆_ : ∀ {U : Set} → Pred U → Pred U → Set
A ⊆ B = ∀ x → x ∈ A → x ∈ B
infix 15 _⊆_

-- Extensional equivalence of sets
-- ⇔ is \<=>
_⇔_ : ∀ {U : Set} → Pred U → Pred U → Set
A ⇔ B = ∀ x → A x ↔ B x
infix 15 _⇔_

-- Two sets are extensionally equal iff they are subsets of each other
setEq : ∀ {U : Set} {A B : Pred U} →    A ⇔ B  ↔  A ⊆ B ∧ B ⊆ A
setEq = (λ AB → ( (λ x xa → pr1 (AB x) xa ) , λ x xb → pr2 (AB x) xb ))
                , (λ A≃B → λ x → (λ ax → pr1 A≃B x ax ) , (λ bx → pr2 A≃B x bx ) )

-- Creating a new module to lighten up the notation
module LogicOps {U : Set} where

  -- The empty subset ∅ ⊆ U.
  -- Corresponds to the constantly-false predicate.
  -- ∅ is \emptyset
  ∅ : Pred U
  ∅ _ = ⊥

  -- The full subset U ⊆ U.
  -- Corresponds to the constantly-true predicate.
  -- K⊤ is K\top
  -- (I will eventually come up with a better symbol for this.)
  K⊤ : Pred U
  K⊤ _ = ⊤

  -- Logical operators on subsets
  -- Intersection.  Corresponds to conjunction.
  -- ∩ is \cap
  _∩_ : Pred U → Pred U → Pred U
  A ∩ B = λ x → A x ∧ B x
  infixl 17 _∩_

  -- Union.  Corresponds to disjunction.
  -- ∪ is \cup
  _∪_ : Pred U → Pred U → Pred U
  A ∪ B = λ x → A x ∨ B x
  infixl 17 _∪_

  -- Complement. Corresponds to negation.
  -- - is -
  -_ : Pred U → Pred U
  - A = λ x → ¬ A x
  infix 19 -_

  -- Extensional equivalence of predicates.
  -- ⇔ is \<=>
