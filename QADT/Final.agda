{-# OPTIONS --type-in-type #-}

module Final where

open import Isomorphisms
open import BasicLogic
open import BasicDatatypes
open import Functions

data ADT (n : ℕ) : Set where
  𝕍 : Fin n → ADT n
  𝟎 : ADT n
  𝟏 : ADT n
  _×_ : ADT n → ADT n → ADT n
  _⊔_ : ADT n → ADT n → ADT n
  μ : ADT (succ n) → ADT n

infixr 28 _×_
infixr 27 _⊔_

Env : ℕ → Set₁
Env n = Fin n → Set

decEnv : ∀ {n} → Env n → Set
decEnv ρ = ∀ x → dec≡ (ρ x)

EmptyEnv : Env 0
EmptyEnv ()

ρ₀ : Env 0
ρ₀ = EmptyEnv

coskip : ∀ {n} {k} {A : Set k} → (Fin n → A) → Fin (succ n) → A → (Fin (succ n) → A)
coskip f (here _) a (here _) = a
coskip f (here _) a (down y) = f y
coskip {.(succ n)} f (down x) a (here (succ n)) = f (here n)
coskip {succ n} f (down x) a (down y) = coskip (λ x₁ → f (down x₁ ) ) x a y

extEnvGen : ∀ {n : ℕ} → (Fin (succ n)) → Set → Env n → Env (succ n)
extEnvGen {n} x A ρ y = coskip ρ x A y

extEnv : ∀ {n : ℕ} → Set → Env n → Env (succ n)
extEnv {n} A ρ y = extEnvGen (here _) (A ) ρ y

{-# NO_POSITIVITY_CHECK  #-}
data LFP (F : Set → Set) : Set where
  lfp : F (LFP F) → LFP F

Functor : (Set → Set) → Set₁
Functor F = ∀ {X Y : Set} → (X → Y) → F X → F Y

{-# TERMINATING #-}
fold : ∀ {F : Set → Set} (Fmap : Functor F) {A : Set} (a : F A → A) → LFP F → A
fold Fmap a (lfp x) = a (Fmap (fold Fmap a) x )

NatFun : Functor (λ X → X ∨ ⊤)
NatFun f (in1 x) = in1 (f x)
NatFun f (in2 x) = in2 x

⟦_⟧_ : ∀ {n : ℕ} → ADT n → Env n → Set
⟦ 𝕍 x ⟧ e = e x
⟦ 𝟎 ⟧ e = ⊥
⟦ 𝟏 ⟧ e = ⊤
⟦ x × y ⟧ e = ⟦ x ⟧ e ∧ ⟦ y ⟧ e
⟦ x ⊔ y ⟧ e = ⟦ x ⟧ e ∨ ⟦ y ⟧ e
⟦ μ x ⟧ e = LFP λ X → ⟦ x ⟧ (extEnv X e)

decADT : ∀ {n} (a : ADT n) (ρ : Env n) → dec≡ (⟦ a ⟧ ρ)
decADT a ρ = {!   !}

Env→ : ∀ {n : ℕ} → Env n → Env n → Set
Env→ ρ σ = ∀ x → ρ x → σ x

ConsEnv→ : ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : Env n} (e12 : Env→ e1 e2)
             → Env→ (extEnv X e1) (extEnv Y e2)
ConsEnv→ f e12 (here _) = f
ConsEnv→ f e12 (down x) = e12 x

reflEnv→ : ∀ {n} (e : Env n) → Env→ e e
reflEnv→ e x = I

NatTran : (Set → Set) → (Set → Set) → Set₁
NatTran F G = ∀ X → F X → G X

LFP→ : ∀ (f g : Set → Set) → Functor f → NatTran f g → LFP f → LFP g
LFP→ f g fmap fg = fold fmap (λ z → lfp (fg (LFP g) z) )

⟦_⟧→_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : Env n} → Env→ ρ σ → (⟦ e ⟧ ρ → ⟦ e ⟧ σ)
⟦ 𝕍 x ⟧→ ρσ = ρσ x
⟦ 𝟎 ⟧→ ρσ = I
⟦ 𝟏 ⟧→ ρσ = I
(⟦ (e1 × e2) ⟧→ ρσ) (x , y) = ( (⟦ e1 ⟧→ ρσ) x , (⟦ e2 ⟧→ ρσ) y )
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in1 x) = in1 ((⟦ e1 ⟧→ ρσ) x)
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in2 y) = in2 ((⟦ e2 ⟧→ ρσ) y)
⟦_⟧→_ (μ e) {ρ} {σ} ρσ = LFP→ (λ X → ⟦ e ⟧ extEnv X ρ) (λ X → ⟦ e ⟧ extEnv X σ)
  (λ f → ⟦ e ⟧→ ConsEnv→ f (reflEnv→ ρ ) ) λ X → (⟦ e ⟧→ ConsEnv→ I ρσ )

foldADT : ∀ {n} (a : ADT (succ n)) (ρ : Env n) (X : Set) (f : ⟦ a ⟧ (extEnv X ρ) → X)
          → ⟦ μ a ⟧ ρ → X
foldADT {n} a ρ X = fold (λ f →  ⟦ a ⟧→ ConsEnv→ f (reflEnv→ ρ ) )

Nat' : ADT 0
Nat' = μ (𝟏 ⊔ 𝕍 (here 0) )

List' : ADT 1
List' = μ (𝟏 ⊔ (𝕍 (down (here 0)) × 𝕍 (here 1) ) )

Nat : Set
Nat = ⟦ Nat' ⟧ EmptyEnv

one : Nat
one = lfp (in2 (lfp (in1 tt ) ) )


Env≃ : ∀ {n : ℕ} → Env n → Env n → Set
Env≃ ρ σ = ∀ x → ρ x ≃ σ x

_enviso∘_ : ∀ {n : ℕ} {ρ σ ψ : Env n} → Env≃ ρ σ → Env≃ σ ψ → Env≃ ρ ψ
_enviso∘_ {n} {ρ} {σ} {ψ} e1 e2 x with e1 x | e2 x
... | e1x | e2x = e1x iso∘ e2x

reflEnv : ∀ {n} (ρ : Env n)  → Env≃ ρ ρ
reflEnv ρ x = id≃ (ρ x)

{-# TERMINATING #-}
LFP≃ : ∀ (f g : Set → Set) → (∀ x y (xy : x ≃ y) → f x ≃ g y) → LFP f ≃ LFP g
LFP≃ f g h = iso i j ij ji where
  i : LFP f → LFP g
  i (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h)
  ... | iso f+ f- f-+ f+- = lfp (f+ x )
  j : LFP g → LFP f
  j (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h)
  ... | iso f+ f- f-+ f+- = lfp (f- x )
  ij : (x : LFP f) → j (i x) ≡ x
  ij (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h) in r
  ... | iso f+ f- f-+ f+- = ext lfp (f-+ x )
  ji : (y : LFP g) → i (j y) ≡ y
  ji (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h) in r
  ... | iso f+ f- f-+ f+- = ext lfp (f+- x )

LFPiso : ∀ (F : Set → Set) → F (LFP F) ≃ (LFP F)
LFPiso F = iso (f+ ) f- f-+ f+- where
  f+ : F (LFP F) → LFP F
  f+ x = lfp x
  f- : LFP F → F (LFP F)
  f- (lfp x) = x
  f-+ : (x : F (LFP F)) → x ≡ x
  f-+ x = refl x
  f+- : (y : LFP F) → f+ (f- y) ≡ y
  f+- (lfp x) = refl (lfp x)

lemmaμ1 : ∀ {n : ℕ} {X Y : Set} {ρ σ : Env n} → X ≃ Y → Env≃ ρ σ → Env≃ (extEnv X ρ) (extEnv Y σ)
lemmaμ1 {.zero} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (here zero) = xy
lemmaμ1 {.(succ n)} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (here (succ n)) = xy
lemmaμ1 {succ n} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (down x) = ρσ x

lemmaμ1gen : ∀ {n : ℕ} {X Y : Set} {ρ σ : Env n} (fn : Fin (succ n)) → X ≃ Y → Env≃ ρ σ → Env≃ (extEnvGen fn X ρ) (extEnvGen fn Y σ)
lemmaμ1gen {n} {X} {Y} {ρ} {σ} (here .n) XY ρ≃σ (here .n) = XY
lemmaμ1gen {n} {X} {Y} {ρ} {σ} (here .n) XY ρ≃σ (down x) = ρ≃σ x
lemmaμ1gen {.(succ n)} {X} {Y} {ρ} {σ} (down fn) XY ρ≃σ (here (succ n)) = ρ≃σ (here n)
lemmaμ1gen {succ n} {X} {Y} {ρ} {σ} (down fn) XY ρ≃σ (down x) = lemmaμ1gen {ρ = ρ ∘ down } {σ = σ ∘ down } fn XY (λ x₁ → ρ≃σ (down x₁) ) x

⟦_⟧≃_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : Env n} → Env≃ ρ σ → ⟦ e ⟧ ρ ≃ ⟦ e ⟧ σ
⟦ 𝕍 x ⟧≃ ρ≃σ = ρ≃σ x
⟦ 𝟎 ⟧≃ ρ≃σ = iso (λ x → x ) (λ x → x ) refl refl
⟦ 𝟏 ⟧≃ ρ≃σ = iso (λ z → z) (λ z → z) refl refl
⟦ e × e₁ ⟧≃ ρ≃σ = iso∧ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦ e ⊔ e₁ ⟧≃ ρ≃σ = iso∨ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦_⟧≃_ (μ e) {ρ = ρ} {σ = σ} ρ≃σ = LFP≃ (λ z → ⟦ e ⟧ extEnv z ρ) (λ z → ⟦ e ⟧ extEnv z σ) f where
  f : (x y : Set) → x ≃ y → (⟦ e ⟧ extEnv x ρ) ≃ (⟦ e ⟧ extEnv y σ)
  f x y xy with lemmaμ1 xy ρ≃σ
  ... | μ1 = ⟦ e ⟧≃ μ1

skip : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
skip (here _) x = down x
skip (down y) (here n) = here (succ n)
skip (down y) (down x) = down (skip y x )

wk : ∀ {n} → Fin (succ n) → ADT (n) → ADT (succ n)
wk {n} f (𝕍 x) = 𝕍 (skip f x )
wk {n} f 𝟎 = 𝟎
wk {n} f 𝟏 = 𝟏
wk {n} f (e × e₁) = wk f e × wk f e₁
wk {n} f (e ⊔ e₁) = wk f e ⊔ wk f e₁
wk {n} f (μ e) = μ (wk (down f) e)


subst-level : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → Fin (succ n) → ADT n
subst-level {n} (𝕍 x) e' f = coskip 𝕍 f e' x
subst-level 𝟎 e' f = 𝟎
subst-level 𝟏 e' f = 𝟏
subst-level (e × e₁) e' f = subst-level e e' f × subst-level e₁ e' f
subst-level (e ⊔ e₁) e' f = subst-level e e' f ⊔ subst-level e₁ e' f
subst-level {n} (μ e) e' f = μ (subst-level e (wk (here _) e' ) (down f))

subst : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → ADT n
subst e e' = subst-level e e' (here _)

substlemmaNoADT : ∀ {n} {l1} {l2} {A : Set l1} {B : Set l2} (f : A → B) → (ρ : Fin n → A) → (y : Fin (succ n)) → (a : A) → (x : Fin (succ n)) → f (coskip ρ y a x) ≡ coskip (f ∘ ρ) y (f a) x
substlemmaNoADT f ρ (here _) a (here _) = refl (f a)
substlemmaNoADT {.(succ n)} f ρ (down y) a (here (succ n)) = refl (f (ρ (here n)))
substlemmaNoADT f ρ (here _) a (down x) = refl (f (ρ x))
substlemmaNoADT {succ n} f ρ (down y) a (down x) = substlemmaNoADT f ((ρ ∘ down)) y a x



-- ↓n : ∀ {n} → Fin (succ n) → Fin n
-- ↓n {.zero} (here zero) = {!   !}
-- ↓n {.(succ n)} (here (succ n)) = here n
-- ↓n {succ n} (down f) = down (↓n f )


skip2 : ∀ {n} → (x : Fin (succ n)) (y : Fin (succ (succ n))) → Fin (succ n)
skip2 {n} (here _) (here .(succ _)) = here _
skip2 (here _) (down y) = y
skip2 (down x) (here .(succ _)) = here _
skip2 {succ n} (down x) (down y) = down (skip2 x y )

skip2lemma1 : ∀ {n} (x : Fin (succ n)) → skip2 x (here (succ n)) ≡ here n
skip2lemma1 {n} (here _) = refl (here n)
skip2lemma1 {n} (down x) = refl (here n)

unskip : ∀ {n} → (x : Fin (succ n)) (y : Fin (succ (succ n))) → Fin (succ (succ n))
unskip {n} (here .n) (here .(succ n)) = down (here n)
unskip {n} (here .n) (down y) = here (succ n)
unskip {n} (down x) (here .(succ n)) = down (down x )
unskip {succ n} (down x) (down y) = down (unskip x y )

unskiplemma1 : ∀ {n} → (x : Fin (succ n)) → unskip x (here (succ n)) ≡ down x
unskiplemma1 {n} (here .n) = refl (down (here n))
unskiplemma1 {n} (down x) = refl (down (down x))

enveqlemma1 : ∀ {n} (A A' : Set) (x : Fin (succ n)) (y : Fin (succ (succ n))) (ρ : Env n) → Env≃ (coskip (coskip ρ x A ) y A') (coskip (coskip ρ (skip2 x y ) A') (unskip x y ) A)
enveqlemma1 {n} A A' (here _) (here _) ρ (here .(succ n)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (here _) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (down y) ρ (here .(succ n)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (down y) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 A A' (down x) (here _) ρ (here .(succ _)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 A A' (down x) (here _) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {succ n} A A' (down x) (down y) ρ (here .(succ (succ n))) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {succ n} A A' (down x) (down y) ρ (down g) = enveqlemma1 A A' x y (ρ ∘ down) g

_≡∧≡_ : ∀ {A B C D : Set₁} → A ≡ B → C ≡ D → (A ∧ C) ≡ (B ∧ D)
refl A ≡∧≡ refl C = refl (A ∧ C)

_≡∨≡_ : ∀ {A B C D : Set₁} → A ≡ B → C ≡ D → (A ∨ C) ≡ (B ∨ D)
refl A ≡∨≡ refl C = refl (A ∨ C)


{-
weakeninglemma : ∀ {n} (x : Fin (succ n)) (A : ADT n) {A' : Set} (ρ : Env n) → ⟦ wk x A ⟧ (coskip ρ x A') ≡ ⟦ A ⟧ ρ
weakeninglemma (here _) (𝕍 x₁) {A'} ρ = refl (ρ x₁)
weakeninglemma (down x) (𝕍 (here n)) {A'} ρ = refl (ρ (here n))
weakeninglemma (down x) (𝕍 (down x₁)) {A'} ρ = weakeninglemma x (𝕍 x₁) (ρ ∘ down)
weakeninglemma x 𝟎 {A'} ρ = refl ⊥
weakeninglemma x 𝟏 {A'} ρ = refl ⊤
weakeninglemma x (A × A₁) {A'} ρ = weakeninglemma x A ρ ≡∧≡ weakeninglemma x A₁ ρ
weakeninglemma x (A ⊔ A₁) {A'} ρ = weakeninglemma x A ρ ≡∨≡ weakeninglemma x A₁ ρ
weakeninglemma {n} x (μ A) {A'} ρ with weakeninglemma (down x ) A {A'} (coskip ρ x A')
... | r = {!   !}
-}

skipcoskip : ∀ {n} (ρ : Env n) x v A → coskip ρ x A (skip x v) ≡ ρ v
skipcoskip {n} ρ (here .n) v A = refl (ρ v)
skipcoskip {.(succ n)} ρ (down x) (here n) A = refl (ρ (here n))
skipcoskip {.(succ _)} ρ (down x) (down v) A = skipcoskip (λ x₁ → ρ (down x₁)) (x ) v A

coskipLemma : ∀ {n} (x : Fin (succ n)) (y : Fin (succ (succ n))) (ρ : Env n) {A B : Set}
  → coskip (coskip ρ x A) (here (succ n)) B y ≡ coskip (coskip ρ (here n) B) (down x) A y
coskipLemma {n} (here .n) (here .(succ n)) ρ {A} {B} = refl B
coskipLemma {n} (here .n) (down y) ρ {A} {B} = refl _
coskipLemma {n} (down x) (here .(succ n)) ρ {A} {B} = refl B
coskipLemma {n} (down x) (down y) ρ {A} {B} = refl _

coskip≃lemma : ∀ {n : ℕ} {S1 S2 : Set} (ρ : Env n) (x : Fin (succ n)) → (S1 ≃ S2) → Env≃ (coskip ρ x S1) (coskip ρ x S2)
coskip≃lemma {n} {S1} {S2} ρ x s1≃s2 y = lemmaμ1gen x s1≃s2 (reflEnv ρ ) y

coskipEnv≃ : ∀ {n : ℕ} {ρ σ : Env n} (x : Fin (succ n)) → (A : Set) → (Env≃ ρ σ ) → Env≃ (coskip ρ x A) (coskip σ x A)
coskipEnv≃ {n} {ρ} {σ} (here .n) A ρ≃σ (here .n) = iso (λ z → z) (λ z → z) refl refl
coskipEnv≃ {n} {ρ} {σ} (here .n) A ρ≃σ (down f) = ρ≃σ f
coskipEnv≃ {.(succ n)} {ρ} {σ} (down x) A ρ≃σ (here (succ n)) = ρ≃σ (here n)
coskipEnv≃ {succ n} {ρ} {σ} (down x) A ρ≃σ (down f) = coskipEnv≃ x  A (λ x₁ → ρ≃σ (down x₁) ) f

-- iso {!   !} {!   !} {!   !} {!   !} where
--   f+ : (fn : Fin (succ n)) →  → coskip ρ fn S1 y → coskip ρ fn S2 y
--   f+ (here .n) cs = {!   !}
--   f+ (down fn) cs = {!   !}

refl2iso : ∀ {A B} → A ≡ B → A ≃ B
refl2iso (refl A) = id≃ A

transpRewrite : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) → B a1 → B a2
transpRewrite B (a12) ba1 rewrite a12 = ba1

transp-+ : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) (b : B a1)
           → transpRewrite B (~ e) (transpRewrite B e b) ≡ b
transp-+ B (refl a1) b = refl b

rewriteRoot : ∀ {A B : Set} → (E : A ≡ B) → A → B
rewriteRoot (refl _) a = a

rewriteRoot-+ : ∀ {A B : Set} → (E : A ≡ B) → (a : A) → rewriteRoot (~ E) (rewriteRoot E a) ≡ a
rewriteRoot-+ (refl _) a = refl a

rewriteRoot+- : ∀ {A B : Set} → (E : A ≡ B) → (b : B) → rewriteRoot E (rewriteRoot (~ E) b) ≡ b
rewriteRoot+-  (refl _) b = refl b

weakeningLemma≃ : ∀ {n} (x : Fin (succ n)) (A : ADT n) {A' : Set} (ρ : Env n) → ⟦ wk x A ⟧ (coskip ρ x A') ≃ ⟦ A ⟧ ρ
weakeningLemma≃ {n} x A {A'} ρ = iso (wkl+ A) (wkl- A) (wkl-+ A) (wkl+- A) where
  wkl+ : (e : ADT n) → ⟦ wk x e ⟧ coskip ρ x A' → ⟦ e ⟧ ρ
  wkl+ (𝕍 v) y = rewriteRoot (skipcoskip ρ x v A' ) y
  wkl+ 𝟏 y = tt
  wkl+ (e1 × e2) (y1 , y2) = (wkl+ e1 y1 , wkl+ e2 y2)
  wkl+ (e1 ⊔ e2) (in1 y1) = in1 (wkl+ e1 y1)
  wkl+ (e1 ⊔ e2) (in2 y2) = in2 (wkl+ e2 y2)
  wkl+ (μ e) y = _≃_.f+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ lemmaμ1 X≃Y (reflEnv ρ)) )) y
  wkl- : (e : ADT n) → ⟦ e ⟧ ρ → ⟦ wk x e ⟧ coskip ρ x A'
  wkl- (𝕍 v) y = rewriteRoot (~ (skipcoskip ρ x v A' ) ) y
  wkl- 𝟏 y = tt
  wkl- (e × e₁) (y , z) = wkl- e y , wkl- e₁ z
  wkl- (e ⊔ e₁) (in1 x) = in1 (wkl- e x )
  wkl- (e ⊔ e₁) (in2 x) = in2 (wkl- e₁ x )
  wkl- (μ e) y = _≃_.f- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ lemmaμ1 X≃Y (reflEnv ρ)) )) y
  wkl-+ : (e : ADT n) → ∀ z → wkl- e (wkl+ e z) ≡ z
  wkl-+ (𝕍 v) z = rewriteRoot-+ (skipcoskip ρ x v A' ) z
  wkl-+ 𝟏 tt = refl tt
  wkl-+ (e × e₁) (x , x₁) = (wkl-+ e x ) ≡,≡ wkl-+ e₁ x₁
  wkl-+ (e ⊔ e₁) (in1 x) = ext in1 (wkl-+ e x )
  wkl-+ (e ⊔ e₁) (in2 x) = ext in2 (wkl-+ e₁ x )
  wkl-+ (μ e) y = _≃_.f-+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ lemmaμ1 X≃Y (reflEnv ρ)) )) y
  wkl+- : (e : ADT n) → ∀ z → wkl+ e (wkl- e z) ≡ z
  wkl+- (𝕍 v) z = rewriteRoot+- (skipcoskip ρ x v A' ) z
  wkl+- 𝟏 tt = refl tt
  wkl+- (e × e₁) (x , x₁) = wkl+- e x ≡,≡ wkl+- e₁ x₁
  wkl+- (e ⊔ e₁) (in1 x) = ext in1 (wkl+- e x )
  wkl+- (e ⊔ e₁) (in2 x) = ext in2 (wkl+- e₁ x )
  wkl+- (μ e) y = _≃_.f+- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ lemmaμ1 X≃Y (reflEnv ρ)) )) y

-- substlemmavarcase : ∀ {n : ℕ} → (fn x : Fin (succ n)) → ∀ (A : ADT n) → (ρ : Env n) → ⟦ coskip 𝕍 fn A x ⟧ ρ → coskip ρ fn (⟦ A ⟧ ρ) x
-- substlemmavarcase (here _) (here _) A ρ si = si
-- substlemmavarcase {.(succ n)} (down fn) (here (succ n)) A ρ si = si
-- substlemmavarcase (here _) (down x) A ρ si = si
-- substlemmavarcase {succ n} (down fn) (down x) A ρ si rewrite substlemmaNoADT (λ e → ⟦ e ⟧ ρ) (𝕍 ) (down fn) A (down x) = si
--
--
-- substlemma+gen : ∀ {n : ℕ} → (x : Fin (succ n)) → (a : ADT (succ n)) → (a' : ADT n) → (ρ : Env n) → ⟦ subst-level a a' x ⟧ ρ → ⟦ a ⟧ (extEnvGen x (⟦ a' ⟧ ρ) ρ)
-- substlemma+gen {n} fn (𝕍 x) a' ρ si = substlemmavarcase fn x a' ρ si
-- substlemma+gen fn 𝟏 a' ρ si = tt
-- substlemma+gen fn (a × a₁) a' ρ (x , x₁) = (substlemma+gen fn a a' ρ x) , (substlemma+gen fn a₁ a' ρ x₁)
-- substlemma+gen fn (a ⊔ a₁) a' ρ (in1 x) = in1 (substlemma+gen fn a a' ρ x)
-- substlemma+gen fn (a ⊔ a₁) a' ρ (in2 x) = in2 (substlemma+gen fn a₁ a' ρ x)
-- substlemma+gen {n} fn (μ a) a' ρ (lfp si) with substlemma+gen (down fn ) a (wk ((here _)) a' )
--   (extEnv (LFP (λ z → ⟦ subst-level a (wk (here n) a') (down fn) ⟧ extEnv z ρ)) ρ ) si | enveqlemma1 ((⟦ a' ⟧ ρ)) ((LFP (λ X → ⟦ a ⟧ coskip (coskip ρ fn (⟦ a' ⟧ ρ)) (here (succ n)) X))) fn ((here (succ n))) ρ
-- ... | r | enveq with ⟦_⟧≃_ a (λ x → enveq x iso∘ {!   !} )
-- ...    | i = lfp (_≃_.f- i r )
--
-- substlemma+ : {n : ℕ} → (a : ADT (succ n)) → (a' : ADT n) → (ρ : Env n) → ⟦ subst a a' ⟧ ρ → ⟦ a ⟧ (extEnv (⟦ a' ⟧ ρ) ρ)
-- substlemma+ e e' ρ si = substlemma+gen (here _) e e' ρ si
--
-- substlemma-gen : ∀ {n : ℕ} → (x : Fin (succ n)) → (a : ADT (succ n)) → (a' : ADT n) → (ρ : Env n) → ⟦ a ⟧ (extEnvGen x (⟦ a' ⟧ ρ) ρ) → ⟦ subst-level a a' x ⟧ ρ
-- substlemma-gen {n} fn (𝕍 x) a' ρ ix with substlemmaNoADT (λ x₁ → ⟦ x₁ ⟧ ρ ) 𝕍 fn a' x
-- ... | slm rewrite ~ slm = ix
-- substlemma-gen {n} fn 𝟏 a' ρ ix = tt
-- substlemma-gen {n} fn (a × a₁) a' ρ (x , x₁) = substlemma-gen fn a a' ρ x , substlemma-gen fn a₁ a' ρ x₁
-- substlemma-gen {n} fn (a ⊔ a₁) a' ρ (in1 x) = in1 (substlemma-gen fn a a' ρ x)
-- substlemma-gen {n} fn (a ⊔ a₁) a' ρ (in2 x) = in2 (substlemma-gen fn a₁ a' ρ x)
-- substlemma-gen {n} fn (μ a) a' ρ (lfp ix) with enveqlemma1 (⟦ a' ⟧ ρ) ((LFP (λ X → ⟦ a ⟧ (λ y₁ → coskip (λ y₂ → coskip ρ fn (⟦ a' ⟧ ρ) y₂) (here (succ n)) X y₁)))) fn (here (succ n)) ρ
-- ... | enveq rewrite skip2lemma1 fn rewrite unskiplemma1 fn with ⟦ a ⟧≃ (enveq enviso∘ {!   !} )
-- ...   | iso1@(iso f+ f- f-+ f+-) with substlemma-gen (down fn) a ((wk (here n) a')) (coskip ρ (here n)  (LFP  (λ X →  ⟦ subst-level a (wk (here n) a') (down fn) ⟧ coskip ρ (here n) X))) (f+ ix )
-- ...     | r = lfp r
--
-- -- with ⟦ a ⟧≃ enveqlemma1 (⟦ μ a ⟧ λ x → coskip ρ fn (⟦ a' ⟧ ρ) x ) (⟦ a' ⟧ ρ ) (here _) (down fn ) ρ
-- -- ... | iso f+ f- f-+ f+- with substlemma-gen (down fn) a (wk (here _) a' ) (extEnv ((LFP (λ X → ⟦ subst-level a (wk (here n) a') (down fn) ⟧ coskip ρ (here n) X))) ρ ) ({!   !}  )
-- -- ...   | r = lfp r
--
-- substlemma- : {n : ℕ} → (a : ADT (succ n)) → (a' : ADT n) → (ρ : Env n) → ⟦ a ⟧ (extEnv (⟦ a' ⟧ ρ) ρ) → ⟦ subst a a' ⟧ ρ
-- substlemma- e e' ρ ix = substlemma-gen (here _) e e' ρ ix

substlemmagen : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → (ρ : Env n) → (x : Fin (succ n)) → ⟦ subst-level e e' x ⟧ ρ ≃ ⟦ e ⟧ (coskip ρ x (⟦ e' ⟧ ρ))
substlemmagen {n} (𝕍 v) e' ρ x = refl2iso (substlemmaNoADT (λ e → ⟦ e ⟧ ρ) (𝕍) x e' v)
substlemmagen {n} 𝟎 e' ρ x = iso (λ z → z) (λ z → z) refl refl
substlemmagen {n} 𝟏 e' ρ x = iso (λ z → z) (λ z → z) refl refl
substlemmagen {n} (e × e₁) e' ρ x = iso∧ (substlemmagen e e' ρ x ) (substlemmagen e₁ e' ρ x )
substlemmagen {n} (e ⊔ e₁) e' ρ x = iso∨ (substlemmagen e e' ρ x) (substlemmagen e₁ e' ρ x)
substlemmagen {n} (μ e) e' ρ x = LFP≃ ((λ X → ⟦ subst-level e (wk (here n) e') (down x) ⟧ coskip ρ (here n) X)) ((λ X → ⟦ e ⟧ coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) X)) (isom ) where
        cosk : (A B : Set) → A ≃ B → Env≃
          (coskip (coskip ρ (here n) A) (down x)
          (⟦ wk (here n) e' ⟧ coskip ρ (here n) A))
          (coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) B)
        cosk A B A≃B y rewrite (~ (coskipLemma x y ρ {⟦ e' ⟧ ρ} {B})) rewrite (~ (coskipLemma x y  ρ {⟦ wk (here n) e' ⟧ coskip ρ (here n) A} {A})) with coskip≃lemma {S1 = A} {S2 = B} (coskip ρ x (⟦ wk (here n) e' ⟧ coskip ρ (here n) A)) (here _) A≃B y
        ... | csl = csl iso∘ coskipEnv≃ (here _) B (coskip≃lemma ρ x (weakeningLemma≃ (here _) e' ρ ) ) y
        isom : (A B : Set) → A ≃ B → (⟦ subst-level e (wk (here n) e') (down x) ⟧ coskip ρ (here n) A) ≃ (⟦ e ⟧ coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) B)
        isom A B AB with substlemmagen e (wk (here n) e' ) (coskip ρ (here n) A ) (down x)
        ... | r = r iso∘ (⟦ e ⟧≃ cosk A B AB )

data Iso {n} : ADT n → ADT n → Set where
  -- Equivalence relation
  refl≃ : ∀ e → Iso e e
  symm≃ : ∀ {a b} → Iso a b → Iso b a
  tran≃ : ∀ {a b c} → Iso a b → Iso b c → Iso a c
  -- Congruence rules
  ∧≃ : ∀ {A1 A2 B1 B2 : ADT n} → Iso A1 A2 → Iso B1 B2 → Iso (A1 × B1) (A2 × B2)
  ∨≃ : ∀ {A1 A2 B1 B2 : ADT n} → Iso A1 A2 → Iso B1 B2 → Iso (A1 ⊔ B1) (A2 ⊔ B2)
  μ≃ : ∀ {A B : ADT (succ n)} → Iso A B → Iso (μ A) (μ B)
  -- Semiring axioms
  assoc×≃ : ∀ a b c → Iso (a × (b × c)) ((a × b) × c)
  assoc⊔≃ : ∀ a b c → Iso (a ⊔ (b ⊔ c)) ((a ⊔ b) ⊔ c)
  comm⊔≃ : ∀ a b → Iso (a ⊔ b) (b ⊔ a)
  comm×≃ : ∀ a b → Iso (a × b) (b × a)
  id⊔≃ : ∀ a → Iso a (𝟎 ⊔ a)
  id×≃ : ∀ a → Iso a (𝟏 × a)
  distrL≃ : ∀ {A B C} → Iso (A × (B ⊔ C)) ((A × B) ⊔ (A × C))
  distrR≃ : ∀ {A B C} → Iso ((A ⊔ B) × C) ((A × C) ⊔ (B × C))
  annih×≃ : ∀ a → Iso (a × 𝟎) 𝟎
  -- Mu reduction rules
  fix≃ : ∀ (e : ADT (succ n)) → Iso (μ e) (subst e (μ e))
  subst≃ : ∀ {e1 e2 : ADT (succ n)} {d1 d2 : ADT n} → Iso e1 e2 → Iso d1 d2 → Iso (subst e1 d1) (subst e2 d2)

1+ : ∀ {n} → ADT n → ADT n
1+ a = 𝟏 ⊔ a

_² : ∀ {n} → ADT n → ADT n
_² a = a × a

_³ : ∀ {n} → ADT n → ADT n
_³ a = a × a ²

infix 50 _²
infix 50 _³

Num : ∀ {n} → ℕ → ADT n
Num zero = 𝟎
Num (succ n) = 1+ (Num n)

𝕧₀ : ∀ {n} → ADT (succ n)
𝕧₀ = 𝕍 (here _)

-- Groupoid operations
!! : ∀ {n} {a : ADT n}   → Iso a a
!! = refl≃ _
~~ : ∀ {n} {a b : ADT n} → Iso a b → Iso b a
~~ = symm≃
_=!=_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso b c → Iso a c
ab =!= bc = tran≃ ab bc
_~!~_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso c b → Iso a c
ba ~!~ cb = (~~ ba) =!= (~~ cb)
_~!=_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso b c → Iso a c
ba ~!= bc = ~~ ba =!= bc
-- _~!=_ = _=!=_ ∘ ~~
_=!~_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso c b → Iso a c
ab =!~ cb = ab =!= (~~ cb)
-- _=!~_ = _~!~_ ∘ ~~

--- Congruence laws
cong+ :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a ⊔ c) (b ⊔ d)
cong+ ab cd = ∨≃ ab cd
cong× :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a × c) (b × d)
cong× ab cd = ∧≃ ab cd

cong+= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b ⊔ d) e → Iso (a ⊔ c) e
cong+= ab cd bde = cong+ ab cd =!= bde
cong×= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b × d) e → Iso (a × c) e
cong×= ab cd bde = cong× ab cd =!= bde

!+ :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
!+ i = cong+ !! i
+! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
+! i = cong+ i !!
!× :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a × b) (a × c)
!× i = cong× !! i
×! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b × a) (c × a)
×! i = cong× i !!

!+= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a ⊔ c) d → Iso (a ⊔ b) d
!+= bc acd = !+ bc =!= acd
+!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c ⊔ a) d → Iso (b ⊔ a) d
+!= bc cad = +! bc =!= cad
×!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a × c) d → Iso (a × b) d
×!= bc acd = !× bc =!= acd
!×= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c × a) d → Iso (b × a) d
!×= bc cad = ×! bc =!= cad

-- Semiring Axioms
-- Associativity, commutativity, and identity
a× : ∀ {n} {a b c : ADT n} → Iso ((a × b) × c) (a × (b × c))
a× {n} {a} {b} {c} = ~~ (assoc×≃ a b c)
a+ : ∀ {n} {a b c : ADT n} → Iso ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))
a+ {n} {a} {b} {c} = ~~ (assoc⊔≃ a b c)
c× : ∀ {n} {a b : ADT n} → Iso (a × b) (b × a)
c× {n} {a} {b} = comm×≃ a b
c+ : ∀ {n} {a b : ADT n} → Iso (a ⊔ b) (b ⊔ a)
c+ {n} {a} {b} = comm⊔≃ a b
i+l : ∀ {n} {a : ADT n} → Iso (𝟎 ⊔ a) a
i+l = ~~ (id⊔≃ _)
i+r : ∀ {n} {a : ADT n} → Iso (a ⊔ 𝟎) a
i+r = c+ =!~ id⊔≃ _
i×l : ∀ {n} {a : ADT n} → Iso (𝟏 × a) a
i×l {n} {a} = ~~ (id×≃ a)
i×r : ∀ {n} {a : ADT n} → Iso (a × 𝟏) a
i×r {n} {a} = c× =!~ id×≃ a
-- distributivity and annihilation
dl : ∀ {n} {a b c : ADT n} → Iso (a × (b ⊔ c)) (a × b ⊔ a × c)
dl {n} {a} {b} {c} = distrL≃
dr : ∀ {n} {a b c : ADT n} → Iso((a ⊔ b) × c)  (a × c ⊔ b × c)
dr {n} {a} {b} {c} = distrR≃
ar : ∀ {n} {a : ADT n} → Iso (a × 𝟎) 𝟎
ar {n} {a} = annih×≃ a
al : ∀ {n} {a : ADT n} → Iso (𝟎 × a) 𝟎
al {n} {a} = c× =!= (annih×≃ a)

a×= : ∀ {n} {a b c d : ADT n} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
a×= {n} {a} {b} {c} {d} i = assoc×≃ a b c ~!= i
a+= : ∀ {n} {a b c d : ADT n} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
a+= {n} {a} {b} {c} {d} i = assoc⊔≃ a b c ~!= i
c×= : ∀ {n} {a b c : ADT n} → Iso (b × a) c → Iso (a × b) c
c×= {n} {a} {b} {c} i = comm×≃ b a ~!= i
c+= : ∀ {n} {a b c : ADT n} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
c+= {n} {a} {b} {c} i = comm⊔≃ b a ~!= i
i+l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟎 ⊔ a) b
i+l= {n} {a} {b} i = i+l =!= i
i+r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a ⊔ 𝟎) b
i+r= {n} {a} {b} i = i+r =!= i
i×l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟏 × a) b
i×l= {n} {a} {b} i = i×l =!= i
i×r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a × 𝟏) b
i×r= {n} {a} {b} i = i×r =!= i

dl= : ∀ {n} {a b c d : ADT n} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
dl= {n} {a} {b} {c} {d} i = distrL≃ =!= i
dr= : ∀ {n} {a b c d : ADT n} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
dr= {n} {a} {b} {c} {d} i = distrR≃ =!= i
ar= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (a × 𝟎) b
ar= {n} {a} {b} i = annih×≃ a =!= i
al= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (𝟎 × a) b
al= {n} {a} {b} i = c×= (annih×≃ a =!= i)

-- END RULES LIST


+1× : ∀ {n} (c : ℕ) (A B : ADT n) → Iso ((Num c × A) ⊔ A) B → Iso (Num (succ c) × A) B
+1× c A B toB = tran≃ e1 toB where
  e1 = tran≃ distrR≃ (tran≃ (comm⊔≃ _ _ ) (∨≃ (refl≃ _) (symm≃ (id×≃ _ ) ) ) )



r= : ∀ {n} {e : ADT n} → Iso e e
r= {n} {e} = refl≃ e
s= : ∀ {n} {a b : ADT n} → Iso a b → Iso b a
s= {n} {a} {b} i = symm≃ i
t= : ∀ {n} {a b c : ADT n} → Iso a b → Iso b c → Iso a c
t= = tran≃
_t~_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso c b → Iso a c
_t~_ {n} {a} {b} {c} i1 i2 = t= i1 (s= i2)
_~t_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso b c → Iso a c
_~t_ {n} {a} {b} {c} i1 i2 = t= (s= i1) i2

+= :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
+= = !+
=+ :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
=+ = +!
×= :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a × b) (a × c)
×= = !×
=× :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b × a) (c × a)
=× = ×!

-- a×= : ∀ {n} {a b c d : ADT n} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
-- a+= : ∀ {n} {a b c d : ADT n} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
-- c+= : ∀ {n} {a b c : ADT n} → Iso (b × a) c → Iso (a × b) c
-- c×= : ∀ {n} {a b c : ADT n} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
-- 0L= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟎 ⊔ a) b
-- 0R= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a ⊔ 𝟎) b
-- 1×L= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟏 × a) b
-- 1×R= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a × 𝟏) b
-- dL= : ∀ {n} {a b c d : ADT n} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
-- dR= : ∀ {n} {a b c d : ADT n} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
-- dR= {n} {a} {b} {c} {d} i = tran≃ (symm≃ distrR≃ ) i
-- ah : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (a × 𝟎) b
-- ah {n} {a} {b} i = (annih×≃ a) ~t i

dist3 : ∀ {n} {A B C D : ADT n} → Iso (A × (B ⊔ C ⊔ D)) (A × B ⊔ A × C ⊔ A × D)
dist3 = dl= (!+ dl)

cycle+ : ∀ {n} {A B C : ADT n} → Iso (A ⊔ B ⊔ C) (B ⊔ C ⊔ A)
cycle+ = c+= (a+= !! )

-- μiso : ∀ {n} (e : ADT (succ n)) → Iso (μ e) (subst e (μ e))
μiso : ∀ {n} (e : ADT (succ n)) (ρ : Env n) → ⟦ μ e ⟧ ρ ≃ ⟦ subst e (μ e) ⟧ ρ
μiso {n} e ρ with iso~ (LFPiso (λ x → ⟦ e ⟧ extEnv (x  ) ρ )) | substlemmagen e (μ e) ρ (here _)
... | li | sl = li iso∘ iso~ sl

⟦_⟧iso : ∀ {n} {A B : ADT n} → Iso A B → ( ρ : Env n) → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ
⟦_⟧j : ∀ {n} {A B : ADT n} → Iso A B → {ρ ρ' : Env n} → Env≃ ρ ρ' → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ'

⟦ refl≃ e ⟧iso ρ = ⟦ e ⟧≃ reflEnv ρ
⟦ symm≃ e ⟧iso ρ with ⟦ e ⟧iso ρ
... | r = iso~ r
⟦ tran≃ e1 e2 ⟧iso ρ with ⟦ e1 ⟧iso ρ | ⟦ e2 ⟧iso ρ
... | r | r2 = r iso∘ r2
⟦ ∧≃ e e₁ ⟧iso ρ = iso∧ (⟦ e ⟧iso ρ ) (⟦ e₁ ⟧iso ρ)
⟦ ∨≃ e e₁ ⟧iso ρ = iso∨ (⟦ e ⟧iso ρ) (⟦ e₁ ⟧iso ρ)
⟦ μ≃ {e1} {e2} e12 ⟧iso ρ = LFP≃ (λ X → ⟦ e1 ⟧ (extEnv X ρ)) ((λ X → ⟦ e2 ⟧ (extEnv X ρ)))
                          λ X Y XY → ⟦ e12 ⟧j (lemmaμ1 XY (reflEnv ρ ) )
-- ⟦ ×≃ A x ⟧iso ρ = iso∧ (⟦ refl≃ A ⟧iso ρ ) (⟦ x ⟧iso ρ)
-- ⟦ ⊔≃ A x ⟧iso ρ = iso∨ (⟦ refl≃ A ⟧iso ρ) (⟦ x ⟧iso ρ)
⟦ distrL≃ ⟧iso ρ = isodistrL
⟦ distrR≃ ⟧iso ρ = isodistrR
⟦ fix≃ e ⟧iso ρ = μiso e ρ
⟦_⟧iso {n} (subst≃ {e1} {e2} {d1} {d2} j1 j2) ρ with substlemmagen e1 d1 ρ (here _) | substlemmagen e2 d2 ρ (here _)
... | sl1 | sl2 = sl1 iso∘ iso~ (sl2 iso∘ iso~ (⟦ j1 ⟧j (coskip≃lemma ρ (here _) (⟦ j2 ⟧iso ρ)) ) )
⟦ assoc×≃ a b c ⟧iso ρ = assoc∧
⟦ assoc⊔≃ a b c ⟧iso ρ = assoc∨
⟦ comm⊔≃ a b ⟧iso ρ = comm∨
⟦ comm×≃ a b ⟧iso ρ = comm∧
⟦ id⊔≃ _ ⟧iso ρ = id∨
⟦ id×≃ _ ⟧iso ρ = id∧
⟦ annih×≃ a ⟧iso ρ = annih∧

⟦_⟧j {A = A} {B = B} e {ρ} {ρ'} ρρ' = ⟦ e ⟧iso ρ iso∘ (⟦ B ⟧≃ ρρ')

module G=1+2G+G²+G³ where

  g : ADT 1
  g = 𝟏 ⊔ (Num 2 × (𝕍 (here 0))) ⊔ (𝕍 (here 0)) ² ⊔ (𝕍 (here 0)) ³

  G : ADT 0
  G = μ g

  GG : Set
  GG = ⟦ G ⟧ EmptyEnv

  Gleaf : GG
  Gleaf = lfp (in1 tt )
  Gunode1 : GG → GG
  Gunode1 g = lfp (in2 (in1 (in1 tt , g ) ) )
  Gunode2 : GG → GG
  Gunode2 g = lfp (in2 (in1 (in2 (in1 tt) , g ) ) )
  Gbnode : GG ∧ GG → GG
  Gbnode g12 = lfp (in2 (in2 (in1 g12 ) ) )
  Gtnode : GG ∧ (GG ∧ GG) → GG
  Gtnode g123 = lfp (in2 (in2 (in2 g123)))

  allG : ℕ → List GG
  allG zero = [] -- Gleaf ∷ []
  allG (succ n) = let
      un1 = List→ Gunode1 (allG n)
      un2 = List→ Gunode2 (allG n)
      allG² : List (GG ∧ GG)
      allG² = lazyProd (allG n) (allG n)
      allG³ : List (GG ∧ (GG ∧ GG))
      allG³ = lazyProd (allG n) allG²
      bn  = List→ Gbnode allG²
      tn =  List→ Gtnode allG³
    in Gleaf ∷ merge (merge un1 un2) (merge bn tn)

  ==G : GG → GG → 𝔹
  ==G (lfp (in1 _)) (lfp (in1 _)) = true
  ==G (lfp (in2 (in1 (in1 _ , g1)))) (lfp (in2 (in1 (in1 _ , g2)))) = ==G g1 g2
  ==G (lfp (in2 (in1 (in2 (in1 _) , g1)))) (lfp (in2 (in1 (in2 (in1 _) , g2)))) = ==G g1 g2
  ==G (lfp (in2 (in2 (in1 (g1 , g2))))) (lfp (in2 (in2 (in1 (g1' , g2'))))) = and (==G g1 g2) (==G g1' g2')
  ==G (lfp (in2 (in2 (in2 (g1 , (g2 , g3)))))) (lfp (in2 (in2 (in2 (g1' , (g2' , g3')))))) =
    and (==G g3 g3') (and (==G g1 g2) (==G g1' g2'))
  ==G _ _ = false

module M=1+M+M² where

  m : ADT 1
  m = 𝟏 ⊔ (𝕍 (here 0)) ⊔ (𝕍 (here 0)) ²

  M : ADT 0
  M = μ m

  MM : Set
  MM = ⟦ M ⟧ EmptyEnv

  Mleaf : MM
  Mleaf = lfp (in1 tt)
  Munode : MM → MM
  Munode m = lfp (in2 (in1 m) )
  Mbnode : MM → MM → MM
  Mbnode m1 m2 = lfp (in2 (in2 ((m1 , m2 )) ) )


  allM : ℕ → List MM
  allM n = {!   !}

  ==M : MM → MM → 𝔹
  ==M (lfp (in1 _)) (lfp (in1 _)) = true
  ==M (lfp (in2 (in1 m1))) (lfp (in2 (in1 m2))) = ==M m1 m2
  ==M (lfp (in2 (in2 (m1 , m2)))) (lfp (in2 (in2 (m1' , m2')))) = and (==M m1 m1') (==M m2 m2')
  ==M _ _ = false

  open G=1+2G+G²+G³

  gM : ADT 0
  gM = subst g M

  gM=M : Iso gM M
  -- gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r ) !! )) =!= a+= (+= e ) ) ) )
  gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= !! ar i+r) !! )) =!= a+= (+= e ) ) ) )
    where  e = dist3 ~!= ×= (~~ (fix≃ m ) )

  G→M : ⟦ G ⟧ EmptyEnv  → ⟦ M ⟧ EmptyEnv
  G→M = foldADT g (λ ()) (⟦ M ⟧ EmptyEnv) ((_≃_.f+ (⟦ gM=M ⟧iso EmptyEnv )))

  findm? : MM → ℕ → 𝔹
  findm? m n = elem ==M m (List→ G→M (allG n))

  allGlength : ℕ → ℕ
  allGlength = length ∘ allG

  [1-4] : List ℕ
  [1-4] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

  [1-10] : List ℕ
  [1-10] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []

  cn : ∀ {A : Set} → ℕ → (A → A) → A → A
  cn {A} zero f x = x
  cn {A} (succ n) f x = f (cn n f x)

  bigM : MM
  bigM = cn 7 (Mbnode Mleaf) Mleaf

  check : Set
  check = {! findm? bigM 5  !}
  -- check = {! findm? (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) Mleaf))) 4   !}
  -- check = {! ==M  (G→M (Gleaf)) Mleaf   !}

  20ms : List MM
  20ms = take 20 (allM 4)

  filter : ∀ {A} → (A → 𝔹) → List A → List A
  filter = {!   !}

  pass1 : List MM
  pass1 = filter (λ x → not (findm? x 3)) 20ms

  pass2 : List MM
  pass2 = filter (λ x → findm? x 4) 20ms


  -- T→B : ⟦ T ⟧ EmptyEnv  → ⟦ B ⟧ EmptyEnv
  -- T→B = foldADT t (λ ()) (⟦ B ⟧ EmptyEnv) ((_≃_.f+ (⟦ tB=B ⟧iso EmptyEnv )))

  h : ⟦ G ⟧ ρ₀ → ⟦ M ⟧ ρ₀
  h x = fold {λ X → ⟦ g ⟧ (extEnv X ρ₀)} (λ j →  ⟦ g ⟧→ (λ tt → j)) (_≃_.f+ (⟦ gM=M ⟧iso ρ₀ ) ) x

  M²=M+M²+M³ : Iso (M ²) (M ⊔ M ² ⊔ M ³)
  M²=M+M²+M³ = t= (t= (×= (fix≃ m)) (dist3) ) (∨≃ (c×= (i×l= r= ) ) r=  )  -- (s= {! dist3   !} )
  --
  M²=M³+M²+M : Iso (M ²) (M ³ ⊔ M ² ⊔ M)
  M²=M³+M²+M = t= M²=M+M²+M³ (c+= (t= (=+ (c+= r= )) (a+= r=) ) )
  --
  -- -- M²=1+2M+2M²+2M³ : Iso (M ²) (𝟏 ⊔ M ⊔ M ⊔ M ² ⊔ M ² ⊔ M ³ ⊔ M ³)
  M²=1+2M+2M²+2M³ : Iso (M ²) (M ³ ⊔ M ³ ⊔ M ² ⊔ M ² ⊔ M ⊔ M ⊔ 𝟏)
  M²=1+2M+2M²+2M³  = t= M²=M³+M²+M (+= (t= (=+ M²=M³+M²+M ) (a+= (+= (a+= (+= e ) ) ) ) ) )
    where e = t= (+= (fix≃ m ) ) (s= (t= cycle+ (+= (t= (=+ (c+= r= ) ) (a+= r=) ) ) ) )

  e3 : Iso (M ²) ((M ³ ⊔ M ³) ⊔ ( M ² ⊔ M ²) ⊔ (M ⊔ M) ⊔ 𝟏)
  e3 = t= M²=1+2M+2M²+2M³ (s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) ) )

  X+X=2X : ∀ {n} (X : ADT n) → Iso (X ⊔ X) (Num 2 × X)
  X+X=2X A = ~~ (dr= (cong+ i×l (dr= (+! i×l =!= (!+ al =!= i+r) ) ) ) )
  -- X+X=2X A = s= (dl= (∨≃ (i×l r=) (dl= (t= (∨≃ (i×l r=) (c× (ar= r= ) ) ) (c+ (i+ r= ) ) ) ) ) )

  M²=2M²+1 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
  -- M²=2M²+1 = t= e3 (s= {! t=   !} ) -- (s= (t= (=+ (t= (×= M²=M³+M²+M ) {!   !} )  ) {!   !} ) )
  M²=2M²+1 = t= e3 (s= (t= (=+ (t= (×= M²=M³+M²+M ) (s= (X+X=2X _ ) ) )  )
    (t= (a+= (a+= (+= (c+= (a+= (a+= (+= (a+= (+= (c+= (a+= (c+= (a+= (a+= (+= r= ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) e) ) )
    where e = s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) )
  -- M²=2M²+1 = t= e3 (s= (t= (=+ (s= (X+X=2X (M ²) ) ) ) {!    !} ) )


module 1+X²=1+X+X³ where
  -- The explicitly defined version
  data BT : Set where
    BTleaf : BT
    BTnode : BT → BT → BT

  data TT : Set where
    TTleaf : TT
    TUnode : TT → TT
    TTnode : TT → TT → TT → TT

  BT→TT : BT → TT
  BT→TT BTleaf = TTleaf
  BT→TT (BTnode bt1 BTleaf) = TUnode (BT→TT bt1)
  BT→TT (BTnode bt1 (BTnode bt2 bt3)) = TTnode (BT→TT bt1) (BT→TT bt2) (BT→TT bt3)

  TT→BT : TT → BT
  TT→BT TTleaf = BTleaf
  TT→BT (TUnode t) = BTnode (TT→BT t) BTleaf
  TT→BT (TTnode t1 t2 t3) = BTnode (TT→BT t1) (BTnode (TT→BT t2) (TT→BT t3) )

  cong : ∀ {A B : Set} (f : A → B) {a1 a2 : A} → a1 ≡ a2 → f a1 ≡ f a2
  cong f (refl _) = refl _

  cong2 : ∀ {A B C : Set} (f : A → B → C)
           {a1 a2 : A} → a1 ≡ a2 → {b1 b2 : B} → b1 ≡ b2 → f a1 b1 ≡ f a2 b2
  cong2 f (refl _) (refl _) = (refl _)

  cong3 : ∀ {A B C D : Set} (f : A → B → C → D) {a1 a2 b1 b2 c1 c2}
            → a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → f a1 b1 c1 ≡ f a2 b2 c2
  cong3 f (refl _) (refl _) (refl _) = refl _

  BT→TT→BT : ∀ b → TT→BT (BT→TT b) ≡ b
  BT→TT→BT BTleaf = refl BTleaf
  BT→TT→BT (BTnode b1 BTleaf) = cong (λ x → BTnode x BTleaf) (BT→TT→BT b1)
  BT→TT→BT (BTnode b1 (BTnode b2 b3)) = cong3 (λ x y z → BTnode x (BTnode y z)) (BT→TT→BT b1) (BT→TT→BT b2) (BT→TT→BT b3)

  TT→BT→TT : ∀ t → BT→TT (TT→BT t) ≡ t
  TT→BT→TT TTleaf = refl TTleaf
  TT→BT→TT (TUnode t) = cong TUnode (TT→BT→TT t)
  TT→BT→TT (TTnode t1 t2 t3) = cong3 TTnode (TT→BT→TT t1) (TT→BT→TT t2) (TT→BT→TT t3)

  -- Using the calculus of isomorphisms

  b : ADT 1
  b = 1+ (𝕧₀ ²)

  t : ADT 1
  t = 1+ (𝕧₀ ⊔ (𝕧₀ ³))

  t-func : Set → Set
  t-func X = ⟦ t ⟧ (λ _ → X )

  -- t-functor : Functor t-func
  -- t-functor f = ⟦ t ⟧→ emap where
  --   emap = {!   !}

  B : ADT 0
  B = μ b

  T : ADT 0
  T = μ t

  tB=B : Iso (subst t B) B
  tB=B = ~~ (fix≃ b =!= += (×= (fix≃ b) =!= dl= (=+ i×r ) ) )

  foldT : ∀ (X : Set) → (t-func X → X) → ⟦ T ⟧ EmptyEnv → X
  foldT X Xalg (lfp (in1 tt)) = Xalg (in1 tt)
  foldT X Xalg (lfp (in2 (in1 x))) = Xalg (in2 (in1 (foldT X Xalg x ) ) )
  foldT X Xalg (lfp (in2 (in2 (x1 , (x2 , x3)))))
    = Xalg (in2 (in2 ((fT x1) , ((fT x2) , fT x3 ) ) ) ) where fT = foldT X Xalg
  -- foldT X = fold {F = t-func} λ {A} {B} f → ⟦ t ⟧→ {!   !}

  T→B : ⟦ T ⟧ EmptyEnv  → ⟦ B ⟧ EmptyEnv
  T→B = foldADT t (λ ()) (⟦ B ⟧ EmptyEnv) ((_≃_.f+ (⟦ tB=B ⟧iso EmptyEnv )))
  -- foldT (⟦ B ⟧ EmptyEnv) (_≃_.f+ (⟦ tB=B ⟧iso EmptyEnv ) )


-- Iso ((𝟏 ⊔ 𝟎) × A × B ⊔ A × B) ((𝟏 ⊔ 𝟏 ⊔ 𝟎) × A × B)
-- Iso (1+ (1+ 𝟎) × A × B) (1+ 𝟎 × A × B ⊔ A × B)
foil : ∀ {n} {A B : ADT n} → Iso ((A ⊔ B) ²) (A ² ⊔ (Num 2 × A × B) ⊔ B ²)
foil {n} {A} {B} = tran≃ distrR≃ (tran≃ (∨≃ distrL≃ distrL≃)
                    (tran≃ (symm≃ (assoc⊔≃ _ _ _) ) (∨≃ (refl≃ _) e )) ) where
                      e3 = symm≃ (+1× 1 (A × B) _ (refl≃ _))
                      -- e3 =  +1× 1 (A × B) _ (refl≃ _)
                      e2 = tran≃ ((∨≃ (tran≃ (id×≃ _) (tran≃ (∧≃ (id⊔≃ 𝟏 ) (refl≃ _ ) ) (∧≃ (comm⊔≃ _ _ ) (refl≃ _ ) ) ) ) (refl≃ _))) e3
                      e = tran≃ (assoc⊔≃ _ _ _) (∨≃ (tran≃ (∨≃ (refl≃ _) (comm×≃ _ _)) e2) (refl≃ _))

-- ×≃ : ∀ A {B C} → Iso B C → Iso (A × B) (A × C)
-- ⊔≃ : ∀ A {B C} → Iso B C → Iso (A ⊔ B) (A ⊔ C)
-- euclid≃ : ∀ {e1 e2 e3} → Iso e1 e2 → Iso e3 e2 → Iso e1 e3



𝔹≃𝔹₁ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₁ = !!
𝔹≃𝔹₂ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₂ = a+ ~!= i+r= (c+= (!+ (~~ i+r) ) )
-- 𝔹≃𝔹₂ = c+= (cong+ i+r (~~ i+r) )
-- 𝔹≃𝔹₂ = c+= (a+= (!+ c+ ) )

iso≠lemma : ∀ {A B : Set} (i1 i2 : A ≃ B) → ∀ (a : A) → ¬ (_≃_.f+ i1 a ≡ _≃_.f+ i2 a) → ¬ (i1 ≡ i2)
iso≠lemma i1 .i1 a neq (refl .i1) = neq (refl (_≃_.f+ i1 a) )

𝔹1≠𝔹2 : ¬ (⟦ 𝔹≃𝔹₁ ⟧iso EmptyEnv ≡ ⟦ 𝔹≃𝔹₂ ⟧iso EmptyEnv)
𝔹1≠𝔹2 i1=i2 = iso≠lemma (⟦ 𝔹≃𝔹₁ ⟧iso EmptyEnv) (⟦ 𝔹≃𝔹₂ ⟧iso EmptyEnv) (in1 tt) (λ {()} ) i1=i2


-- 1 + X + X^3
FADT : ADT 1
FADT = 𝟏 ⊔ (𝕍 (here 0) ⊔ (𝕍 (here 0) × (𝕍 (here 0) × 𝕍 (here 0) ) ) )

-- 1 + X^2
GADT : ADT 1
GADT = 𝟏 ⊔ (𝕍 (here 0) × 𝕍 (here 0) )

Iso1 : Iso FADT GADT
Iso1 = {! fold   !}

module X=X^4 where

  ∛1 : ADT 0
  ∛1 = μ ((1+ (𝕍 (here 0))) ²)

  X : ADT 0
  X = ∛1

  skel : ADT 1
  skel = (1+ ((wk (here 0) X) × (𝕍 (here 0)))) ²

  -- 1+X^2=1+X[1+X^2] : Iso (1+ (X ²)) (1+ (X × (1+ (X ²))))
  -- 1+X^2=1+X[1+X^2] = subst≃ {0} {skel} {skel} {X} {1+ (X ²)} (refl≃ skel) (fix≃ ((1+ (𝕍 (here 0))) ²))

  1+X²≃1+X[1+X²] : Iso (1+ (X ²)) (1+ (X × (1+ X ²)))
  1+X²≃1+X[1+X²] = {!   !} -- subst≃ {0} {skel} {skel} {X} {1+ X ²} (refl≃ skel) (fix≃ ((1+ (𝕍 (here 0))) ²) )

  X=1+X+X^2 : Iso X (1+ (X ⊔ (X ²)))
  X=1+X+X^2 = fix≃ ((1+ (𝕍 (here 0))) ²) =!= {!   !}

exsub : ADT 1
exsub = μ (𝟏 ⊔ (𝕍 (here 1) × 𝕍 (down (here 0 ) ) )) ⊔ (𝕍 (here 0))

ex2sub : ADT 1
ex2sub = (𝟏 ⊔ 𝕍 (here 0))
