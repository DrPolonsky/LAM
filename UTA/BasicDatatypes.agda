-- Most of the stuff in this file is compiled from Lecture4,
-- with some later additions and edits for consistency

module BasicDatatypes where

open import BasicLogic

-- 𝔹 is \bB
-- 𝑩 is \MIB, ℬ is \McB
data 𝔹 : Set where
  true : 𝔹
  false : 𝔹

¬t≡f : ¬ (true ≡ false)
¬t≡f ()

t≢f : ∀ x → x ≡ true → x ≡ false → ⊥
t≢f x xt xf = ¬t≡f (xt ~! xf)

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

-- ext𝔹 : ∀ {A} (f : 𝔹 → A) → f ≡ λ { true → f true ; false → f false}
-- ext𝔹 f = {!   !}

-- ext𝔹 : ∀ {A} (f g : 𝔹 → A) → f ≅ g → f ≡ g
-- ext𝔹 f g fg =
--   let {!   !}
--
-- eta : ∀ {A B : Set} (f : A → B) → f ≡ λ x → f x
-- eta f = refl f
--
-- eta𝔹 : ∀ {A : Set} (f : 𝔹 → A) → (λ x → f x) ≡ λ { true → f true ; false → f false }
-- eta𝔹 f = refl _

-- ℕ is \bN
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Even : ℕ → Set where
  EvenZero : Even zero
  EvenSucc : ∀ n → Even n → Even (succ (succ n))


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
eqℕ : ℕ → ℕ → 𝔹
eqℕ x y = and (le x y) (le y x)

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

refl≤ : ∀ n → n ≤ n
refl≤ zero = zero≤ zero
refl≤ (succ n) = succ≤ (refl≤ n)
asym≤ : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
asym≤ (zero≤ _) (zero≤ .zero) = refl zero
asym≤ (succ≤ mn) (succ≤ nm) = succ≡ (asym≤ mn nm)
tran≤ : ∀ {l m n} → l ≤ m → m ≤ n → l ≤ n
tran≤ (zero≤ _) mn = zero≤ _
tran≤ (succ≤ lm) (succ≤ mn) = succ≤ (tran≤ lm mn)

_≤≡_ : ∀ {x y z} → x ≤ y → y ≡ z → x ≤ z
xy ≤≡ refl _ = xy
_≡≤_ : ∀ {x y z} → x ≡ y → y ≤ z → x ≤ z
refl _ ≡≤ yz = yz

_+≤_ : ∀ x {y} {z} → y ≤ z → x + y ≤ x + z
zero +≤ zero≤ _ = zero≤ _
zero +≤ succ≤ yz = succ≤ yz
succ x +≤ yz = succ≤ (x +≤ yz )

_≤+_ : ∀ {x} {y} → x ≤ y → ∀ z → x + z ≤ y + z
_≤+_ {x} {y} xy z = (comm+ x z ≡≤ (z +≤ xy)) ≤≡ comm+ z y

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

data Fin : ℕ → Set where
  here : ∀ n → Fin (succ n)
  down : ∀ {n} → Fin n → Fin (succ n)

-- ∷ is \::
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

null : ∀ {A} → List A → Set
null [] = ⊤
null _ = ⊥

infixr 21 _∷_

exList : List ℕ
exList = 1 ∷ 2 ∷ 3 ∷ []

fold : ∀ {A B : Set} → B → (A → B → B) → List A → B
fold z f [] = z
fold z f (x ∷ xs) = f x (fold z f xs)

_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

bindList : ∀ {A B : Set} → (A → List B) → List A → List B
bindList g [] = []
bindList g (x ∷ xs) = g x ++ bindList g xs

-- append : ∀ {A} → List (List A) → List A
-- append [] = []
-- append (x ∷ xs) = x ++ append xs

data occurs {A : Set} (a : A) : List A → Set where
  atHead : ∀ (xs : List A)                       → occurs a (a ∷ xs)
  inTail : ∀ (b : A) (xs : List A) → occurs a xs → occurs a (b ∷ xs)

data dup {A : Set} : List A → Set where
  dHead : ∀ (a : A) (xs : List A) → occurs a xs → dup (a ∷ xs)
  dTail : ∀ (a : A) (xs : List A) → dup xs      → dup (a ∷ xs)
  -- if the head of the list occurs in the tail, there's a duplicate
  -- otherwise, if the

occursMap : ∀ {A B : Set} {x : A}
              → (L : List A) → (f : A → B) → occurs x L 
              → occurs (f x) (map f L)
occursMap L f (atHead xs) = atHead (map f xs)
occursMap L f (inTail y xs occ) = inTail (f y) (map f xs) (occursMap xs f occ)  