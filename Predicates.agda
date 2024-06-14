module Predicates where

-- open import LogicLevels
open import Logic
open import Lifting
open import Lambda

-- The type of n-ary predicates on A
𝓟^ : ℕ → Set → Set₁
𝓟^ zero     A = Set
𝓟^ (succ n) A = A → 𝓟^ n A

-- The type of unary predicates on A, AKA the powerset of A
𝓟 : Set → Set₁
𝓟 = 𝓟^ 1

-- The type of binary predicates, AKA relations, on A
𝓡 : Set → Set₁
𝓡 = 𝓟^ 2

-- The functorial action of 𝓟^
𝓟^← : ∀ {n : ℕ} {A B : Set} → (A → B) → 𝓟^ n B → 𝓟^ n A
𝓟^← {zero}   f P = P
𝓟^← {succ n} f P = λ a → 𝓟^← f (P (f a))

module LogicOps {A : Set} where
  -- Constantly true predicate
  K⊤ : ∀ {n} → 𝓟^ n A
  K⊤ {zero}   = ⊤
  K⊤ {succ n} = λ _ → K⊤

  -- Constantly false predicate
  K⊥ : ∀ {n} → 𝓟^ n A
  K⊥ {zero}   = ⊥
  K⊥ {succ n} = λ _ → K⊥

  -- Intersection
  _∩_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A → 𝓟^ n A
  _∩_ {zero}   P Q =          P × Q
  _∩_ {succ n} P Q = λ a → (P a ∩ Q a)

  -- Union
  _∪_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A → 𝓟^ n A
  _∪_ {zero}   P Q =          P ⊔ Q
  _∪_ {succ n} P Q = λ a → (P a ∪ Q a)

  -- Complement
  ∁_ : ∀ {n} → 𝓟^ n A → 𝓟^ n A
  ∁_ {zero}   P = ¬ P
  ∁_ {succ n} P = λ x → ∁ (P x)

  -- Subset relation
  _⊆_ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n A → Set
  _⊆_ {zero}   P Q = P → Q
  _⊆_ {succ n} P Q = ∀ x → P x ⊆ Q x

  -- Extensional equivalence of predicates
  _⇔_ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n A → Set
  A ⇔ B = A ⊆ B × B ⊆ A

  infix 15 _⇔_
  infix 16 _⊆_
  infix 17 _∩_
  infix 17 _∪_
  infix 19 ∁_
open LogicOps public

module Lifting^ where
  o^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (↑ A)
  o^ {zero}         = ⊤
  o^ {succ n} (i x) = K⊥
  o^ {succ n} o     = o^

  i^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (↑ A)
  i^ {zero}   P       = P
  i^ {succ n} P (i x) = i^ (P x)
  i^ {succ n} P o     = K⊥

  ↑^ : ∀  {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (↑ A)
  ↑^ P = i^ P ∪ o^
open Lifting^ public

module Lambda^ where
  var^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (Λ A)
  var^ {zero}   P         = P
  var^ {succ n} P (var x) = var^ (P x)
  var^ {succ n} P _       = K⊥

  app^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (Λ A) → 𝓟^ n (Λ A) → 𝓟^ n (Λ A)
  app^ {zero}   P Q             = P × Q
  app^ {succ n} P Q (app t1 t2) = app^ (P t1) (Q t2)
  app^ {succ n} P Q _           = K⊥

  abs^ : ∀ {n : ℕ} {A : Set} → 𝓟^ n (Λ (↑ A)) → 𝓟^ n (Λ A)
  abs^ {zero}   P         = P
  abs^ {succ n} P (abs t) = abs^ (P t)
  abs^ {succ n} P _       = K⊥

  Λ^ : ∀  {n : ℕ} {A : Set} → 𝓟^ n A → 𝓟^ n (Λ A)
  Λ^ {zero}   {A} P             = P
  Λ^ {succ n} {A} P (var x)     = var^ (P x)
  Λ^ {succ n} {A} P (app t1 t2) = app^ (Λ^ P t1) (Λ^ P t2)
  Λ^ {succ n} {A} P (abs t0)    = abs^ (Λ^ (↑^ P) t0)
open Lambda^ public
