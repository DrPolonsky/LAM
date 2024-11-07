module Datatypes where

open import Logic
open import Lifting

-- INTEGERS AND FINITE SETS
-- ℕ is \bN
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

add : ℕ → ℕ → ℕ
add zero y = y
add (succ x) y = succ (add x y)

max : ℕ → ℕ → ℕ
max zero y = y
max x zero = x
max (succ x) (succ y) = succ (max x y)

Fin : ℕ → Set
Fin zero = ⊥
Fin (succ n) = ↑ (Fin n)

∘^ : ∀ {A : Set} → ℕ → (A → A) → (A → A)
∘^ zero f = I
∘^ (succ n) f = f ∘ (∘^ n f)


-- Booleans
-- 𝔹 is \bB
-- 𝑩 is \MIB, ℬ is \McB
data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

le : ℕ → ℕ → 𝔹
le zero y = true
le (succ x) zero = false
le (succ x) (succ y) = le x y

if_then_else_ : ∀ {A : Set} → 𝔹 → A → A → A
if true  then x else y = x
if false then x else y = y

and : 𝔹 → 𝔹 → 𝔹
and true true = true
and _ _ = false
or : 𝔹 → 𝔹 → 𝔹
or x y = if x then true else y
not : 𝔹 → 𝔹
not x = if x then false else true

eqℕ : ℕ → ℕ → 𝔹
eqℕ x y = and (le x y) (le y x)

-- Lists
-- ∷ is \::
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
{-# BUILTIN LIST List #-}

infixr 21 _∷_

any : ∀ {A} → (A → 𝔹) → List A → 𝔹
any f [] = false
any f (x ∷ xs) = if f x then true else any f xs

exList : List ℕ
exList = 1 ∷ 2 ∷ 3 ∷ []

List→ : ∀ {A B : Set} → (A →  B) → List A → List B
List→ f [] = []
List→ f (x ∷ xs) = f x ∷ List→ f xs

[1-n] : ℕ → List ℕ
[1-n] zero = []
[1-n] (succ n) = (succ n) ∷ [1-n] 0

foldList : ∀ {A B : Set} → B → (A → B → B) → List A → B
foldList z f [] = z
foldList z f (x ∷ xs) = f x (foldList z f xs)

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

merge : ∀ {A} → List A → List A → List A
merge xs [] = xs
merge [] ys = ys
merge (x ∷ xs) (y ∷ ys) = x ∷ y ∷ merge xs ys

lazyProd : ∀ {A B} → List A → List B → List (A × B)
lazyProd xs [] = []
lazyProd [] ys = []
lazyProd (x ∷ xs) (y ∷ ys) = (x , y) ∷ merge (lazyProd xs (y ∷ ys))
                  (List→ (λ z → (x , z)) ys)

filter : ∀ {A} → (A → 𝔹) → List A → List A
filter f [] = []
filter f (x ∷ xs) = if f x then (filter f xs) else x ∷ (filter f xs)

elem : ∀ {A} → (A → A → 𝔹) → A → List A → 𝔹
elem dA a [] = false
elem dA a (x ∷ xs) = or (dA a x) (elem dA a xs)

take : ∀ {A} → ℕ → List A → List A
take zero _ = []
take (succ n) [] = []
take (succ n) (x ∷ xs) = x ∷ take n xs

length : ∀ {A} → List A → ℕ
length [] = 0
length (_ ∷ xs) = succ (length xs)
