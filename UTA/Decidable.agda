
module Decidable where

open import BasicLogic
open import BasicDatatypes
open import SetOperations
open import Functions

-- Properties of boolean-valued predicates on A

-- A predicate is decidable if it is either true or false on every input
dec : ∀ {A} → Pred A → Set
dec P = ∀ x → EM (P x) -- P x ∨ ¬ P x

-- Alternatively, we can ask for a boolean-valued function, which,
-- on input x, returns "true" if and only if P x.
-- 𝔹 is \bB
decBy : ∀ {A} → Pred A → Pred (A → 𝔹)
decBy {A} P = λ (f : A → 𝔹) → ∀ x → f x ≡ true ↔ P x

-- Part 1.1
-- ¬t≡f : ¬ (true ≡ false)
-- ¬t≡f = {!   !}
--
-- t≢f : ∀ x → x ≡ true → x ≡ false → ⊥
-- t≢f x xt xf = {!   !}

decBy2dec : ∀ {A} (P : Pred A) (f : A → 𝔹) → decBy P f → dec P
decBy2dec P f d x with f x in fx
... | true  = in1 (pr1 (d x) fx )
... | false = in2 (λ z → t≢f (f x) (pr2 (d x) z ) fx )

decFun : ∀ {A} (P : Pred A) → dec P → A → 𝔹
decFun P dp x = case (K true) (K false) (dp x)

dec2decBy : ∀ {A} (P : Pred A) (dp : dec P) → decBy P (decFun P dp)
dec2decBy P dp x with dp x
... | in1 y = (λ _ → y) , (λ _ → refl _)
... | in2 z = (λ {()} ) , λ p → exFalso (z p )

-- Part 1.2
-- Prove that equality on the booleans and in/equality on the integers are decidable.
-- Use as many helper lemmas as you need.
-- You may also import/in1ine your proofs from the previous Homework.

dec𝔹 : ∀ (x y : 𝔹) → EM (x ≡ y)
dec𝔹 true true = in1 (refl true)
dec𝔹 true false = in2 (λ ())
dec𝔹 false true = in2 (λ ())
dec𝔹 false false = in1 (refl false)

succ≡inv : ∀ {x} {y} → succ x ≡ succ y → x ≡ y
succ≡inv {x} {.x} (refl .(succ x)) = refl x

decℕ : ∀ (x y : ℕ) → EM (x ≡ y)
decℕ zero zero = in1 (refl zero)
decℕ zero (succ y) = in2 (λ ())
decℕ (succ x) zero = in2 (λ ())
decℕ (succ x) (succ y) with decℕ x y
... | in1 xy = in1 (ext succ xy )
... | in2 nxy = in2 (λ sxy → nxy (succ≡inv sxy ) )

succ≤inv : ∀ {x} {y} → succ x ≤ succ y → x ≤ y
succ≤inv (succ≤ sxy) = sxy

dec≤ℕ : ∀ (x y : ℕ) → EM (x ≤ y)
dec≤ℕ zero y = in1 (zero≤ y)
dec≤ℕ (succ x) zero = in2 (λ ())
dec≤ℕ (succ x) (succ y) = case (λ x≤y → in1 (succ≤ x≤y ) ) (λ ¬x≤y → in2 (λ sx≤sy → ¬x≤y (succ≤inv sx≤sy) ) ) (dec≤ℕ x y)

dec≡ : Set → Set
dec≡ A = ∀ (x : A) → dec (_≡_ x)

down≡inv : ∀ {n} {x y : Fin n} → down x ≡ down y → x ≡ y
down≡inv (refl (down x)) = refl x

decFin : ∀ {n} → dec≡ (Fin n)
decFin {.(succ n)} (here n) (here .n) = in1 (refl (here n))
decFin {.(succ n)} (here n) (down k) = in2 (λ {()})
decFin {.(succ _)} (down l) (here _) = in2 (λ {()})
decFin {.(succ _)} (down l) (down k) = case (in1 ∘ ext down) (λ l≢k → in2 (λ dl=dk → l≢k (down≡inv  dl=dk) ) ) (decFin l k)

cons≡ : ∀ {A} {x y : A} → x ≡ y → {xs ys : List A} → xs ≡ ys → (x ∷ xs) ≡ (y ∷ ys)
cons≡ (refl x) (refl xs) = refl (x ∷ xs)

decOccurs : ∀ {A} → dec≡ A → ∀ (x : A) → dec (occurs x)
decOccurs dA x [] = in2 (λ {()})
decOccurs dA x (y ∷ ys) = case (λ x=y → in1 (transp (λ z → occurs x (z ∷ ys)) x=y (atHead ys) ) )
                               (λ x≠y → case (λ x∈ys →  in1 (inTail y ys x∈ys ) )
                                             (λ x∉ys → in2 λ {  (atHead .ys) → x≠y (refl x)
                                                              ; (inTail .y .ys occ) → x∉ys occ } )
                                             (decOccurs dA x ys) )
                               (dA x y)

decDup : ∀ {A} → dec≡ A → dec (dup {A})
decDup dA [] = in2 (λ {()})
decDup dA (x ∷ xs) with decOccurs dA x xs
... | in1 x∈xs = in1 (dHead x xs x∈xs)
... | in2 x∉xs with decDup dA xs
... | in1 yes = in1 (dTail x xs yes)
... | in2 no = in2 (λ { (dHead _ .xs occ) → x∉xs occ
                      ; (dTail .x .xs d) → no d })

module UnDec {A : Set} (P : Pred A) where
  P⊤P  : (A → 𝔹) → Set
  P⊥P  : (A → 𝔹) → Set
  P⊤P¬ : (A → 𝔹) → Set
  PP⊤  : (A → 𝔹) → Set
  PP⊥  : (A → 𝔹) → Set
  PP⊤¬ : (A → 𝔹) → Set

  P⊤P  f = ∀ x →   f x ≡ true   →        P x
  P⊥P  f = ∀ x →   f x ≡ false  →      ¬ P x
  P⊤P¬ f = ∀ x →   f x ≡ true   →   ¬ (¬ P x)
  PP⊤  f = ∀ x →        P x     →   f x ≡ true
  PP⊥  f = ∀ x →      ¬ P x     →   f x ≡ false
  PP⊤¬ f = ∀ x →   ¬ (¬ P x)    →   f x ≡ true

  P⊤P→PP⊥  : ∀ f →    P⊤P   f   →   PP⊥   f
  PP⊥→P⊤P¬ : ∀ f →    PP⊥   f   →   P⊤P¬  f
  P⊤P¬→PP⊥ : ∀ f →    P⊤P¬  f   →   PP⊥   f
  PP⊤→P⊥P  : ∀ f →    PP⊤   f   →   P⊥P   f
  P⊥P→PP⊤¬ : ∀ f →    P⊥P   f   →   PP⊤¬  f
  PP⊤¬→PP⊤ : ∀ f →    PP⊤¬  f   →   PP⊤   f

  P⊤P→PP⊥↔P⊤P¬ : ∀ f →   (P⊤P f → PP⊥ f) ∧ (PP⊥ f ↔ P⊤P¬ f)
  PP⊤↔P⊥P↔PP⊤¬ : ∀ f →   (PP⊤ f ↔ P⊥P f) ∧ (P⊥P f ↔ PP⊤¬ f)

  P⊤P→PP⊥↔P⊤P¬ f = (   P⊤P→PP⊥ f  , (PP⊥→P⊤P¬ f , P⊤P¬→PP⊥ f))
  PP⊤↔P⊥P↔PP⊤¬ f =   ( PP⊤→P⊥P  f , PP⊤¬→PP⊤ f ∘ P⊥P→PP⊤¬ f )
                    , ( P⊥P→PP⊤¬ f , PP⊤→P⊥P  f ∘ PP⊤¬→PP⊤ f )

  P⊤P→PP⊥  f ptp  x npx with f x in q
  ... | true  = exFalso (npx (ptp x q) )
  ... | false = refl _
  PP⊥→P⊤P¬ f ppb  x ft npx = t≢f (f x) ft (ppb x npx)
  P⊤P¬→PP⊥ f ptpn x npx with f x in q
  ... | true  = exFalso (ptpn x q npx)
  ... | false = refl _
  PP⊤→P⊥P  f ppt  x fx px = t≢f (f x) (ppt x px) fx
  P⊥P→PP⊤¬ f pbp  x nnpx with f x in q
  ... | true  = refl _
  ... | false = exFalso (nnpx (pbp x q) )
  PP⊤¬→PP⊤ f pptn x px = pptn x (λ np → np px)

  -- Notions of decidability
  wdec : Set
  wdec = ∀ x → ¬ P x ∨ ¬ (¬ P x)

  dec→wdec : dec P → wdec
  dec→wdec d x with d x
  ... | in1 y = in2 (λ p → p y)
  ... | in2 z = in1 z

  ¬wdec→¬dec : ¬ wdec → ¬ (dec P)
  ¬wdec→¬dec nw d = nw (dec→wdec d)

  -- Remark. wdec(P) ↔ dec(¬P)
  record dec2 : Set where
    constructor d2
    field
      d2fun : A → 𝔹
      d2ptp : P⊤P d2fun
      d2pfp : P⊥P d2fun

  record dec3 : Set where
    constructor d3
    field
      d3fun : A → 𝔹
      d3ppt : PP⊤ d3fun
      d3ppf : PP⊥ d3fun

  open dec2
  open dec3

  dec→dec2  : dec  P → dec2
  dec2→dec  : dec2 → dec P
  wdec→dec3 : wdec → dec3
  dec3→wdec : dec3 → wdec
  ndec  : (¬  (dec P))   ↔   ∀ f → ¬ (P⊤P f ∧ P⊥P f)
  nwdec : (¬ wdec)   ↔   ∀ f → ¬ (PP⊤ f ∧ PP⊥ f)

  dec→dec2 d = d2 fn pt pb where
    fn = λ x → case (λ _ → true) (λ _ → false) (d x)
    pt : P⊤P fn
    pt x _ with d x
    pt x _  | in1 p = p
    pt x () | in2 q
    pb : P⊥P fn
    pb x _ with d x
    pb x () | in1 q
    pb x _  | in2 q = q

  dec2→dec (d2 fn pt pb) x with fn x in q
  ... | true = in1 (pt x q)
  ... | false = in2 (pb x q)

  wdec→dec3 w = d3 fn pt pb where
    fn = λ x → case (λ _ → false) (λ _ → true) (w x)
    pt : PP⊤ fn
    pt x p with w x
    ... | in1 q = exFalso (q p)
    ... | in2 q = refl _
    pb : PP⊥ fn
    pb x p with w x
    ... | in1 q = refl _
    ... | in2 q = exFalso (q p)

  dec3→wdec (d3 fn pt pf) x with fn x in q
  ... | true  = in2 (λ np → t≢f (fn x) q (pf x np) )
  ... | false = in1 (λ px → t≢f (fn x) (pt x px) q )

  ndec = (ndec+ , ndec-) where
    ndec+ = λ {nd f (pt , pb) → nd (dec2→dec (d2 f pt pb) )}
    ndec- = λ nd2 dc → let d2 = dec→dec2 dc in nd2 (d2fun d2) (d2ptp d2 , d2pfp d2)

  nwdec = (nwdec+ , nwdec-) where
    nwdec+ = λ {nw f (pt , pf) → nw (dec3→wdec (d3 f pt pf) )}
    nwdec- = λ nd3 wd → let d3 = wdec→dec3 wd in nd3 (d3fun d3) (d3ppt d3 , d3ppf d3)

  dne : Set
  dne = ∀ x → ¬ (¬ P x) → P x

  dne→wdec→dec : dne → wdec → dec P
  dne→wdec→dec d w x with w x
  ... | in1 y = in2 y
  ... | in2 z = in1 (d x z)

  nndne : ∀ {X} → ¬ ¬ (¬ ¬ X → X)
  nndne = λ y → y (λ np → exFalso (y (exFalso (np λ p → y (λ _ → p) ) ) ) )

  -- Fun fact!
  densef : ∀ (f : A → 𝔹) → (∀ x → (¬ (¬ P x) → P x) → f x ≡ true) → ∀ x → f x ≡ true
  -- densef f h x = {!   !}
  densef f h x with f x | h x
  ... | true  | c1 = refl _
  ... | false | c2 = exFalso (nndne (g λ () ))
    where g : ¬ (false ≡ true) → ¬ (¬ (¬ P x) → P x)
          g yes np = t≢f false (c2 np) (refl _)

  moredense : ∀ (F : Set → Set) → (∀ X → (¬ (¬ X) → X) → F X) → ∀ X → (F X → ⊥) → ⊥
  moredense F h X = λ nfx → nndne (λ nnnnx → nfx (h X nnnnx) )

open UnDec

∀dne→∀dec : ∀ {A} → (∀ (P : Pred A) → dne P) → ∀ (P : Pred A) → dec P
∀dne→∀dec ∀dne P x = ∀dne (λ y → EM (P y)) x (λ ¬EMPx → ¬EMPx (in2 λ p → ¬EMPx (in1 p) ) )
