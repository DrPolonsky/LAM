-- Most of the stuff in this file is compiled from Lecture4,
-- with some later additions and edits for consistency

module BasicArithmetic where

open import BasicLogic

-- 𝔹 is \bB
-- 𝑩 is \MIB, ℬ is \McB
data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

¬t≡f : ¬ (true ≡ false)
¬t≡f ()

t≢f : ∀ x → x ≡ true → x ≡ false → ⊥
t≢f x xt xf = ¬t≡f ((~ xt) ! xf )

if_then_else_ : ∀ {A : Set} → 𝔹 → A → A → A
if true  then x else y = x
if false then x else y = y
-- if_then_else_ true  = λ x y → x
-- if_then_else_ false = λ x y → y

and : 𝔹 → 𝔹 → 𝔹
and true true = true
and _ _ = false
or : 𝔹 → 𝔹 → 𝔹
or x y = if x then true else y
not : 𝔹 → 𝔹
not x = if x then false else true

-- ℕ is \bN
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

succ≡ : ∀ {m n : ℕ} → m ≡ n → succ m ≡ succ n
succ≡ (refl m) = refl (succ m)

even : ℕ → 𝔹
even zero = true
even (succ n) = not (even n)

odd : ℕ → 𝔹
odd = λ x → not (even x)

-- returns true if the input is zero, false otherwise
isZero : ℕ → 𝔹
isZero zero = true
isZero (succ x) = false

add : ℕ → ℕ → ℕ
add zero y = y
add (succ x) y = succ (add x y)

mul : ℕ → ℕ → ℕ
mul zero y = zero
mul (succ x) y = add y (mul x y)

-- sub x y returns x-y if x ≥ y , returns zero otherwise
sub : ℕ → ℕ → ℕ
sub x zero = x
sub zero (succ y) = zero
sub (succ x) (succ y) = sub x y

-- le x y returns true if x ≤ y
le : ℕ → ℕ → 𝔹
le x y = isZero (sub x y)

-- eq x y returns true if x = y
eq : ℕ → ℕ → 𝔹
eq x y = and (le x y) (le y x)

-- div x y returns x/y rounded down to the nearest integer
{-# TERMINATING #-}
div : ℕ → ℕ → ℕ
div x zero = zero
div x (succ y) = if (le x y) then zero else succ (div (sub x (succ y)) (succ y))

-- mod x y returns the remainder of x divided by y
mod : ℕ → ℕ → ℕ
mod x y = sub x (mul y (div x y))

_+_ : ℕ → ℕ → ℕ
-- _+_ = add
zero     + m = m
(succ n) + m = succ (n + m)

infixl 30 _+_

lemma1comm+ : ∀ y → y ≡ y + zero
lemma1comm+ zero = refl zero
lemma1comm+ (succ y) = succ≡ (lemma1comm+ y )

lemma2comm+ : ∀ x y → succ (y + x) ≡ (y + succ x)
lemma2comm+ x zero = refl (succ x)
lemma2comm+ x (succ y) = succ≡ (lemma2comm+ x y)

comm+ : ∀ (x y : ℕ) → x + y ≡ y + x
comm+ zero y = lemma1comm+ y
comm+ (succ x) y = succ≡ (comm+ x y) ! lemma2comm+ x y

assoc+ : ∀ x y z → x + (y + z) ≡ (x + y) + z
assoc+ zero y z = refl (y + z)
assoc+ (succ x) y z = succ≡ (assoc+ x y z)

_≡+_ : ∀ {x} {y} → x ≡ y → ∀ z → x + z ≡ y + z
_≡+_ (refl _) z = refl _

_+≡_ : ∀ x {y} {z} → y ≡ z → x + y ≡ x + z
_+≡_ x (refl _) = refl _

_≡+≡_ : ∀ {x1 x2 y1 y2} → x1 ≡ x2 → y1 ≡ y2 → x1 + y1 ≡ x2 + y2
refl _ ≡+≡ refl _ = refl _



_*_ : ℕ → ℕ → ℕ
infixl 32 _*_
zero * y = zero
succ x * y = y + x * y

data _≤_ : ℕ → ℕ → Set where
  zero≤ : ∀ x → zero ≤ x
  succ≤ : ∀ {x y} → x ≤ y → succ x ≤ succ y

-- refl≤ : ∀ n → n ≤ n
-- refl≤ = {!   !}
-- tran≤ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
-- tran≤ lm mn = {!   !}
--
-- _≤≡_ : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
-- xy ≤≡ yz = {!   !}
-- _≡≤_ : ∀ {x y z} → x ≡ y → y ≤ z → x ≤ z
-- xy ≡≤ yz = {!   !}
--
-- _+≤_ : ∀ x {y} {z} → y ≤ z → x + y ≤ x + z
-- x +≤ yz = {!   !}
--
-- _≤+_ : ∀ {x} {y} → x ≤ y → ∀ z → x + z ≤ y + z
-- xy ≤+ z = {!   !}

-- minimum of two numbers
min : ℕ → ℕ → ℕ
min zero y = zero
min x zero = zero
min (succ x) (succ y) = succ (min x y)
-- maximum of two numbers
max : ℕ → ℕ → ℕ
max zero y = y
max x zero = x
max (succ x) (succ y) = succ (max x y)
