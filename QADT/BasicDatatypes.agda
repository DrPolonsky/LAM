-- Most of the stuff in this file is compiled from Lecture4,
-- with some later additions and edits for consistency

module QADT.BasicDatatypes where

-- open import QADT.BasicLogic
open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import QADT.Functions

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

exFalsoFin : ∀ {A : Set} → Fin 0 → A
exFalsoFin ()

-- dec≡ : Set → Set
-- dec≡ A = ∀ (x y : A) → EM (x ≡ y) where open import Classical using (EM)

down≡ : ∀ n {x y : Fin n} → down x ≡ down y → x ≡ y
down≡ n {x} {.x} (refl .(down x)) = refl x

decFin : ∀ n → dec≡ (Fin n)
decFin zero = λ x y → exFalsoFin x
decFin (succ n) (here .n) (here .n) = in1 (refl (here n))
decFin (succ n) (here .n) (down y) = in2 (λ {()} )
decFin (succ n) (down x) (here .n) = in2 (λ ())
decFin (succ n) (down x) (down y) = case (λ x₁ → in1 (cong down x₁) ) (λ y → in2 (λ z → y (down≡ n z ) ) )  (decFin n x y)

-- ∷ is \::
data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
{-# BUILTIN LIST List #-}

infixr 21 _∷_

exList : List ℕ
exList = 1 ∷ 2 ∷ 3 ∷ []

List→ : ∀ {A B : Set} → (A →  B) → List A → List B
List→ f [] = []
List→ f (x ∷ xs) = f x ∷ List→ f xs

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

lazyProd : ∀ {A B} → List A → List B → List (A ∧ B)
lazyProd xs [] = []
lazyProd [] ys = []
lazyProd (x ∷ xs) (y ∷ ys) = (x , y) ∷ merge (lazyProd xs (y ∷ ys))
                  (List→ (λ z → (x , z)) ys)

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
