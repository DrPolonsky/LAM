-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --allow-unsolved-meta #-}
module Environment where
-- module QADT.Environment where

open import Agda.Primitive using (lsuc)
open import Logic
open import Lifting
open import Predicates using (𝓟)
open import QADT.Functions

skip : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
skip o x = i x
skip {succ n} (i y) o = o
skip {succ n} (i y) (i x) = i (skip y x )

Env : ∀ {l} (A : Set l) → ℕ → Set l
Env {l} A n = Fin n → A

SetEnv : ℕ → Set₁
SetEnv = Env Set

Γ₀ : SetEnv 0
Γ₀ ()

_⅋_:=_ : ∀ {l} {n} {A} (Γ : Env {l} A n) (x : Fin (succ n)) (a : A) → Env A (succ n)
_⅋_:=_ Γ o a o = a
_⅋_:=_ Γ o a (i y) = Γ y
_⅋_:=_ {n = succ n} Γ (i x) a o = Γ o
_⅋_:=_ {n = succ n} Γ (i x) a (i y) = _⅋_:=_ (λ z → Γ (i z)) x a y

_⅋o:=_ : ∀ {l} {n} {A} (Γ : Env {l} A n) (a : A) → Env A (succ n)
_⅋o:=_ Γ A = _⅋_:=_ Γ o A

Env≡ : ∀ {l} {A : Set l} {n} → Env A n → Env A n → Set l
Env≡ Γ Δ = ∀ x → Γ x ≡ Δ x

reflEnv≡ : ∀ {l} {A : Set l} {n} (Γ : Env A n) → Env≡ Γ Γ
reflEnv≡ Γ x = refl

EnvConsLemma : ∀ {n} (Γ : Fin n → Set) (x : Fin (succ n)) (A : Set) (B : Set)
                     → Env≡ ((Γ ⅋ x := A) ⅋ o := B) ((Γ ⅋ o := B) ⅋ (i x) := A)
EnvConsLemma Γ (i x) A B (i y) = refl
EnvConsLemma Γ (i x) A B o = refl
EnvConsLemma Γ o A B (i x) = refl
EnvConsLemma Γ o A B o = refl

skipCons : ∀ {n} (Γ : SetEnv n) x (A : Set) → Env≡ ((Γ ⅋ x := A) ∘ (skip x)) Γ
skipCons {succ n} Γ (i x) A (i y) = skipCons (λ v → Γ (i v)) x A y
skipCons {succ n} Γ (i x) A o     = refl
skipCons Γ o v A = refl

EnvSubstLemma : ∀ {l} {n} {A B : Set l} (Γ : Env {l} A n) (f : A → B) (a : A) (x : Fin (succ n))
                  → Env≡ (f ∘ (Γ ⅋ x := a)) ((f ∘ Γ) ⅋ x := f a)
EnvSubstLemma {n = succ n} Γ f a (i x) (i y) = EnvSubstLemma (λ z → Γ (i z)) f a x y
EnvSubstLemma {n = succ n} Γ f a (i x) o = refl
EnvSubstLemma Γ f a o (i x) = refl
EnvSubstLemma Γ f a o o = refl

-- -- f ((ρ ⅋ y := a) x) ≡ ((f ∘ ρ) ⅋ y := (f a)) x
-- substlemmaNoADT : ∀ {n} {A : Set} (f : A → Set) → (ρ : Env {l} A n) →
--                     (y : Fin (succ n)) → (a : A) → (x : Fin (succ n)) → f ((ρ ⅋ y := a) x) ≡ ((f ∘ ρ) ⅋ y := (f a)) x
--                     -- f (coskip ρ y a x) ≡ coskip (f ∘ ρ) y (f a) x
-- substlemmaNoADT f ρ y a x = EnvSubstLemma ρ f a y x
-- substlemmaNoADT f ρ (here _) a (here _) = refl (f a)
-- substlemmaNoADT {.(succ n)} f ρ (down y) a (here (succ n)) = refl (f (ρ (here n)))
-- substlemmaNoADT f ρ (here _) a (down x) = refl (f (ρ x))
-- substlemmaNoADT {succ n} f ρ (down y) a (down x) = substlemmaNoADT f ((ρ ∘ down)) y a x

-- Morphisms  between environments
-- Given ρ,σ : SetEnv n, Env→ ρ σ is an environment for the SetEnv ρ→σ = λ x → (ρ x → σ x)
SetEnv→ : ∀ {n : ℕ} → SetEnv n → SetEnv n → Set
SetEnv→ ρ σ = ∀ x → ρ x → σ x

reflSetEnv→ : ∀ {n} (e : SetEnv n) → SetEnv→ e e
reflSetEnv→ e x = I

ConsSetEnv→ : ∀ {n} {e1 e2 : SetEnv n} (e12 : SetEnv→ e1 e2) {X Y : Set} (f : X → Y) (x : Fin (succ n))
             → SetEnv→ (e1 ⅋ x := X) (e2 ⅋ x := Y)
ConsSetEnv→ e12 f o o = f
ConsSetEnv→ e12 f o (i y) = e12 y
ConsSetEnv→ {succ n} e12 f (i x) o = e12 o
ConsSetEnv→ {succ n} e12 f (i x) (i y) = ConsSetEnv→ (λ z → e12 (i z)) f x y

-- Decidability properties
-- open import BasicDatatypes


decSetEnv : ∀ {n} → SetEnv n → Set
decSetEnv ρ = ∀ x → dec≡ (ρ x)

decExtEnv : ∀ {n : ℕ} (ρ : SetEnv n) (A : Set) → decSetEnv ρ → dec≡ A → decSetEnv (ρ ⅋ o := A)
decExtEnv ρ A de da o = da
decExtEnv ρ A de da (i x) = de x

-- Injectivity properties
SetEnv→Inj : ∀ {n} {ρ σ : SetEnv n} → 𝓟 (SetEnv→ ρ σ)
SetEnv→Inj ρ→σ = ∀ x → inj (ρ→σ x)

reflSetEnv→Inj : ∀ {n} (e : SetEnv n) → SetEnv→Inj (reflSetEnv→ e)
reflSetEnv→Inj e = λ x → λ z → z

ConsSetEnv→Inj :  ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : SetEnv n} (e12 : SetEnv→ e1 e2)
                 → inj f → SetEnv→Inj e12 → SetEnv→Inj (ConsSetEnv→ e12 f o)
ConsSetEnv→Inj f e12 injf inje12 o = injf
ConsSetEnv→Inj f e12 injf inje12 (i x) = inje12 x
