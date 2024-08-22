module Environment where

open import BasicLogic
open import BasicDatatypes
open import Functions
open import Isomorphisms


skip : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
skip (here _) x = down x
skip (down y) (here n) = here (succ n)
skip (down y) (down x) = down (skip y x )

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

decExtEnv : ∀ {n : ℕ} (ρ : Env n) (A : Set) → decEnv ρ → dec≡ A → decEnv (extEnv A ρ)
decExtEnv ρ A de da (here _) = da
decExtEnv ρ A de da (down x) = de x

Env→ : ∀ {n : ℕ} → Env n → Env n → Set
Env→ ρ σ = ∀ x → ρ x → σ x

ConsEnv→ : ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : Env n} (e12 : Env→ e1 e2)
             → Env→ (extEnv X e1) (extEnv Y e2)
ConsEnv→ f e12 (here _) = f
ConsEnv→ f e12 (down x) = e12 x

reflEnv→ : ∀ {n} (e : Env n) → Env→ e e
reflEnv→ e x = I

Env≃ : ∀ {n : ℕ} → Env n → Env n → Set
Env≃ ρ σ = ∀ x → ρ x ≃ σ x

_enviso∘_ : ∀ {n : ℕ} {ρ σ ψ : Env n} → Env≃ ρ σ → Env≃ σ ψ → Env≃ ρ ψ
_enviso∘_ {n} {ρ} {σ} {ψ} e1 e2 x with e1 x | e2 x
... | e1x | e2x = e1x iso∘ e2x

reflEnv : ∀ {n} (ρ : Env n)  → Env≃ ρ ρ
reflEnv ρ x = id≃ (ρ x)

lemmaμ1 : ∀ {n : ℕ} {X Y : Set} {ρ σ : Env n} → X ≃ Y → Env≃ ρ σ → Env≃ (extEnv X ρ) (extEnv Y σ)
lemmaμ1 {.zero} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (here zero) = xy
lemmaμ1 {.(succ n)} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (here (succ n)) = xy
lemmaμ1 {succ n} {X = X} {Y = Y} {ρ = ρ} {σ = σ} xy ρσ (down x) = ρσ x

lemmaμ1gen : ∀ {n : ℕ} {X Y : Set} {ρ σ : Env n} (fn : Fin (succ n)) → X ≃ Y → Env≃ ρ σ → Env≃ (extEnvGen fn X ρ) (extEnvGen fn Y σ)
lemmaμ1gen {n} {X} {Y} {ρ} {σ} (here .n) XY ρ≃σ (here .n) = XY
lemmaμ1gen {n} {X} {Y} {ρ} {σ} (here .n) XY ρ≃σ (down x) = ρ≃σ x
lemmaμ1gen {.(succ n)} {X} {Y} {ρ} {σ} (down fn) XY ρ≃σ (here (succ n)) = ρ≃σ (here n)
lemmaμ1gen {succ n} {X} {Y} {ρ} {σ} (down fn) XY ρ≃σ (down x) = lemmaμ1gen {ρ = (λ z → ρ (down z)) } {σ = (λ z → σ (down z)) } fn XY (λ x₁ → ρ≃σ (down x₁) ) x

substlemmaNoADT : ∀ {n} {l1} {l2} {A : Set l1} {B : Set l2} (f : A → B) → (ρ : Fin n → A) → (y : Fin (succ n)) → (a : A) → (x : Fin (succ n)) → f (coskip ρ y a x) ≡ coskip (λ z → f (ρ z)) y (f a) x
substlemmaNoADT f ρ (here _) a (here _) = refl (f a)
substlemmaNoADT {.(succ n)} f ρ (down y) a (here (succ n)) = refl (f (ρ (here n)))
substlemmaNoADT f ρ (here _) a (down x) = refl (f (ρ x))
substlemmaNoADT {succ n} f ρ (down y) a (down x) = substlemmaNoADT f (λ z → ρ (down z)) y a x

enveqlemma1 : ∀ {n} (A A' : Set) (x : Fin (succ n)) (y : Fin (succ (succ n))) (ρ : Env n) → Env≃ (coskip (coskip ρ x A ) y A') (coskip (coskip ρ (skip2 x y ) A') (unskip x y ) A)
enveqlemma1 {n} A A' (here _) (here _) ρ (here .(succ n)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (here _) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (down y) ρ (here .(succ n)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {n} A A' (here _) (down y) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 A A' (down x) (here _) ρ (here .(succ _)) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 A A' (down x) (here _) ρ (down g) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {succ n} A A' (down x) (down y) ρ (here .(succ (succ n))) = iso (λ z → z) (λ z → z) refl refl
enveqlemma1 {succ n} A A' (down x) (down y) ρ (down g) = enveqlemma1 A A' x y (λ z → ρ (down z)) g

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