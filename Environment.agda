-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --allow-unsolved-meta #-}
module Environment where
-- module QADT.Environment where

open import Agda.Primitive using (lsuc)
open import Logic
open import Lifting
open import Datatypes
open import Predicates using (𝓟)
open import QADT.Functions

skip : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
skip o x = i x
skip {succ n} (i y) o = o
skip {succ n} (i y) (i x) = i (skip y x )

Env : ∀ {l} (A : Set l) → Set → Set l
Env {l} A V = V → A

SetEnv : Set → Set₁
SetEnv = Env Set

TypeEnv : Set → Set₁
TypeEnv V = V → Set

Γ₀ : SetEnv ⊥
Γ₀ ()

-- _⅋_:=_ : ∀ {l} {V} {A} (Γ : Env {l} A V) (x : (↑ V)) (a : A) → Env A (↑ V)
-- _⅋_:=_ Γ x a y = {!   !}

infixl 19 _⅋o:=_

_⅋o:=_ : ∀ {l} {V : Set} {A} (Γ : Env {l} A V) (a : A) → Env A (↑ V)
(Γ ⅋o:= a) (i x) = Γ x
(Γ ⅋o:= a) o = a
-- Γ ⅋o:= a = io Γ a needs io to be universe-polymorphic


Env≡ : ∀ {l} {A : Set l} {V} → Env A V → Env A V → Set l
Env≡ Γ Δ = ∀ x → Γ x ≡ Δ x


reflEnv≡ : ∀ {l} {A : Set l} {V} (Γ : Env A V) → Env≡ Γ Γ
reflEnv≡ Γ x = refl

{-
EnvConsLemma : ∀ {n} (Γ : Fin n → Set) (x : Fin (succ n)) (A : Set) (B : Set)
                     → Env≡ ((Γ ⅋o:= A) ⅋o:= B) ((Γ ⅋o:= B) ⅋ (i x) := A)
EnvConsLemma Γ (i x) A B (i y) = refl
EnvConsLemma Γ (i x) A B o = refl
EnvConsLemma Γ o A B (i x) = refl
EnvConsLemma Γ o A B o = refl

skipCons : ∀ {n} (Γ : SetEnv n) x (A : Set) → Env≡ ((Γ ⅋ x := A) ∘ (skip x)) Γ
skipCons {succ n} Γ (i x) A (i y) = skipCons (λ v → Γ (i v)) x A y
skipCons {succ n} Γ (i x) A o     = refl
skipCons Γ o v A = refl
-}

EnvSubstLemma : ∀ {l} {m} {V} {A : Set l} {B : Set m} (Γ : Env A V) (f : A → B) (a : A)
                  → Env≡ (f ∘ (Γ ⅋o:= a)) ((f ∘ Γ) ⅋o:= f a)
EnvSubstLemma Γ f a (i x) = refl
EnvSubstLemma Γ f a o = refl
{-
-- -- f ((ρ ⅋ y := a) x) ≡ ((f ∘ ρ) ⅋ y := (f a)) x
-- substlemmaNoADT : ∀ {n} {A : Set} (f : A → Set) → (ρ : Env {l} A n) →
--                     (y : Fin (succ n)) → (a : A) → (x : Fin (succ n)) → f ((ρ ⅋ y := a) x) ≡ ((f ∘ ρ) ⅋ y := (f a)) x
--                     -- f (coskip ρ y a x) ≡ coskip (f ∘ ρ) y (f a) x
-- substlemmaNoADT f ρ y a x = EnvSubstLemma ρ f a y x
-- substlemmaNoADT f ρ (here _) a (here _) = refl (f a)
-- substlemmaNoADT {.(succ n)} f ρ (down y) a (here (succ n)) = refl (f (ρ (here n)))
-- substlemmaNoADT f ρ (here _) a (down x) = refl (f (ρ x))
-- substlemmaNoADT {succ n} f ρ (down y) a (down x) = substlemmaNoADT f ((ρ ∘ down)) y a x
-}
-- Morphisms  between environments
-- Given ρ,σ : SetEnv n, Env→ ρ σ is an environment for the SetEnv ρ→σ = λ x → (ρ x → σ x)
SetEnv→ : ∀ {V : Set} → SetEnv V → SetEnv V → Set
SetEnv→ ρ σ = ∀ x → ρ x → σ x


reflSetEnv→ : ∀ {n} (e : SetEnv n) → SetEnv→ e e
reflSetEnv→ e x = I

ConsSetEnv→ : ∀ {V} {e1 e2 : SetEnv V} (e12 : SetEnv→ e1 e2) {X Y : Set} (f : X → Y)
             → SetEnv→ (e1 ⅋o:= X) (e2 ⅋o:= Y)
ConsSetEnv→ e12 f (i x) = e12 x
ConsSetEnv→ e12 f o = f

-- Decidability properties
-- open import BasicDatatypes


decSetEnv : ∀ {V} → SetEnv V → Set
decSetEnv ρ = ∀ x → dec≡ (ρ x)

decExtEnv : ∀ {V : Set} (ρ : SetEnv V) (A : Set) → decSetEnv ρ → dec≡ A → decSetEnv (ρ ⅋o:= A)
decExtEnv ρ A de da o = da
decExtEnv ρ A de da (i x) = de x

-- Injectivity properties
SetEnv→Inj : ∀ {V} {ρ σ : SetEnv V} → 𝓟 (SetEnv→ ρ σ)
SetEnv→Inj ρ→σ = ∀ x → inj (ρ→σ x)

reflSetEnv→Inj : ∀ {n} (e : SetEnv n) → SetEnv→Inj (reflSetEnv→ e)
reflSetEnv→Inj e = λ x → λ z → z

ConsSetEnv→Inj :  ∀ {V} {X Y : Set} (f : X → Y) → {e1 e2 : SetEnv V} (e12 : SetEnv→ e1 e2)
                 → inj f → SetEnv→Inj e12 → SetEnv→Inj (ConsSetEnv→ e12 f)
ConsSetEnv→Inj f e12 injf inje12 o = injf
ConsSetEnv→Inj f e12 injf inje12 (i x) = inje12 x
