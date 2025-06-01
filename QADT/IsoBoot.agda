{-# OPTIONS --type-in-type #-}

open import Logic
open import Lifting
open import Datatypes
open import Predicates using (𝓟)
open import Relations.Core using (Rel)

-- Bootstrapping isomorphisms
module QADT.IsoBoot where

data 𝕌 (V : Set) : Set where
  𝕍∙ : V → 𝕌 V
  ⊥∙ : 𝕌 V
  ⊤∙ : 𝕌 V
  ×∙ : 𝕌 V → 𝕌 V → 𝕌 V
  ⊔∙ : 𝕌 V → 𝕌 V → 𝕌 V
  μ∙ : 𝕌 (↑ V) → 𝕌 V
  ≃∙ : 𝕌 V → 𝕌 V → 𝕌 V

𝕌→ : ∀ {V W : Set} → (V → W) → 𝕌 V → 𝕌 W
𝕌→ f (𝕍∙ v) = 𝕍∙ (f v)
𝕌→ f ⊥∙ = ⊥∙
𝕌→ f ⊤∙ = ⊤∙
𝕌→ f (×∙ A B) = ×∙ (𝕌→ f A) (𝕌→ f B)
𝕌→ f (⊔∙ A B) = ⊔∙ (𝕌→ f A) (𝕌→ f B)
𝕌→ f (μ∙ F) = μ∙ (𝕌→ (↑→ f) F )
𝕌→ f (≃∙ A B) = ≃∙ (𝕌→ f A) (𝕌→ f B)

Sub : Set → Set → Set
Sub V W = V → 𝕌 W

Sub↑ : ∀ {V W} → Sub V W → Sub (↑ V) (↑ W)
Sub↑ f = io (𝕌→ i ∘ f) (𝕍∙ o)

_[_] : ∀ {V W : Set} → 𝕌 V → Sub V W → 𝕌 W
𝕍∙ x [ σ ] = σ x
⊥∙ [ σ ] = ⊥∙
⊤∙ [ σ ] = ⊤∙
×∙ A B [ σ ] = ×∙ (A [ σ ]) (B [ σ ])
⊔∙ A B [ σ ] = ⊔∙ (A [ σ ]) (B [ σ ])
μ∙ F [ σ ]   = μ∙ (F [ Sub↑ σ ])
≃∙ A B [ σ ] = ≃∙ (A [ σ ]) (B [ σ ])

data 𝕌* {V : Set} : 𝕌 V → 𝕌 V → Set where
  𝕍* : ∀ v → 𝕌* (𝕍∙ v) (𝕍∙ v)
  ⊥* : 𝕌* ⊥∙ ⊥∙
  ⊤* : 𝕌* ⊤∙ ⊤∙
  ×* : ∀ {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1) → 𝕌* (×∙ A0 B0) (×∙ A1 B1)
  ⊔* : ∀ {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1) → 𝕌* (⊔∙ A0 B0) (⊔∙ A1 B1)
  ≃* : ∀ {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1) → 𝕌* (≃∙ A0 B0) (≃∙ A1 B1)
  μ* : ∀ {F0 F1 : 𝕌 (↑ V)} → 𝕌* F0 F1 → 𝕌* (μ∙ F0) (μ∙ F1) -- ??

𝕌*→ : ∀ {V W : Set} (f : V → W) {A B : 𝕌 V} → 𝕌* A B → 𝕌* (𝕌→ f A) (𝕌→ f B)
𝕌*→ f (𝕍* v) = 𝕍* (f v)
𝕌*→ f ⊥* = ⊥*
𝕌*→ f ⊤* = ⊤*
𝕌*→ f (×* AB AB₁) = ×* (𝕌*→ f AB) (𝕌*→ f AB₁)
𝕌*→ f (⊔* AB AB₁) = ⊔* (𝕌*→ f AB) (𝕌*→ f AB₁)
𝕌*→ f (≃* AB AB₁) = ≃* (𝕌*→ f AB) (𝕌*→ f AB₁)
𝕌*→ f (μ* AB) = μ* (𝕌*→ (↑→ f) AB)

Sub* : ∀ {V W : Set} → Rel (Sub V W) (Sub V W)
Sub* σ τ = ∀ v → 𝕌* (σ v) (τ v)

Sub↑* : ∀ {V W : Set} {σ τ : Sub V W} → Sub* σ τ → Sub* (Sub↑ σ) (Sub↑ τ)
Sub↑* στ (i x) = 𝕌*→ i (στ x)
Sub↑* στ o = 𝕍* o

_[_]* : ∀ {V W : Set} → (A : 𝕌 V) → {σ τ : Sub V W} → (στ : Sub* σ τ) → 𝕌* (A [ σ ]) (A [ τ ])
𝕍∙ x [ στ ]* = στ x
⊥∙ [ στ ]* = ⊥*
⊤∙ [ στ ]* = ⊤*
×∙ A B [ στ ]* = ×* (A [ στ ]*) (B [ στ ]*)
⊔∙ A B [ στ ]* = ⊔* (A [ στ ]*) (B [ στ ]*)
≃∙ A B [ στ ]* = ≃* (A [ στ ]*) (B [ στ ]*)
μ∙ F [ στ ]* = μ* (F [ Sub↑* στ ]*)

refl𝕌* : ∀ {V : Set} (A : 𝕌 V) → 𝕌* A A
refl𝕌* (𝕍∙ x) = 𝕍* x
refl𝕌* ⊥∙ = ⊥*
refl𝕌* ⊤∙ = ⊤*
refl𝕌* (×∙ A B) = ×* (refl𝕌* A) (refl𝕌* B)
refl𝕌* (⊔∙ A B) = ⊔* (refl𝕌* A) (refl𝕌* B)
refl𝕌* (≃∙ A B) = ≃* (refl𝕌* A) (refl𝕌* B)
refl𝕌* (μ∙ F) = μ* (refl𝕌* F)

𝕌*[] : ∀ {V W : Set} (A B : 𝕌 V) (σ : Sub V W) → 𝕌* A B → 𝕌* (A [ σ ]) (B [ σ ])
𝕌*[] (𝕍∙ v) (𝕍∙ v) σ (𝕍* v) = refl𝕌* (σ v)
𝕌*[] ⊥∙ ⊥∙ σ ⊥* = ⊥*
𝕌*[] ⊤∙ ⊤∙ σ ⊤* = ⊤*
𝕌*[] (×∙ A1 A2) (×∙ B1 B2) σ (×* e1 e2) = ×* (𝕌*[] A1 B1 σ e1) (𝕌*[] A2 B2 σ e2)
𝕌*[] (⊔∙ A1 A2) (⊔∙ B1 B2) σ (⊔* e1 e2) = ⊔* (𝕌*[] A1 B1 σ e1) (𝕌*[] A2 B2 σ e2)
𝕌*[] (≃∙ A1 A2) (≃∙ B1 B2) σ (≃* e1 e2) = ≃* (𝕌*[] A1 B1 σ e1) (𝕌*[] A2 B2 σ e2)
𝕌*[] (μ∙ F1) (μ∙ F2) σ (μ* e) = μ* (𝕌*[] F1 F2 (Sub↑ σ) e)

idSub : ∀ {V W : Set} (σ : Sub V W) → Sub* σ σ
idSub σ x = refl𝕌* (σ x)

record Cell (V : Set) : Set where
  constructor cell
  field
    src : 𝕌 V
    tgt : 𝕌 V
    eq : 𝕌* src tgt

Cell→ : ∀ {V W} → (V → W) → Cell V → Cell W
Cell→ f (cell src tgt eq) = cell (𝕌→ f src) (𝕌→ f tgt) (𝕌*→ f eq)

open Cell

EqSub : Set → Set → Set
EqSub V W = V → Cell W

EqSub↑ : ∀ {V W : Set} → EqSub V W → EqSub (↑ V) (↑ W)
EqSub↑ eqsub o = record { src = 𝕍∙ o ; tgt = 𝕍∙ o ; eq = 𝕍* o }
EqSub↑ eqsub (i x) = Cell→ i (eqsub x)

_[_]Eq : ∀ {V W : Set} → (A : 𝕌 V) (σ* : EqSub V W) → 𝕌* (A [ src ∘ σ* ]) (A [ tgt ∘ σ* ])
𝕍∙ x [ σ* ]Eq = eq (σ* x)
⊥∙ [ σ* ]Eq = ⊥*
⊤∙ [ σ* ]Eq = ⊤*
×∙ A B [ σ* ]Eq = ×* (A [ σ* ]Eq) (B [ σ* ]Eq)
⊔∙ A B [ σ* ]Eq = ⊔* (A [ σ* ]Eq) (B [ σ* ]Eq)
μ∙ A [ σ* ]Eq = μ* {! (A [ EqSub↑ σ* ]Eq)  !}
≃∙ A B [ σ* ]Eq = {!   !}

{-

SetEnv : Set → Set
SetEnv V = V → Set

⟦_⟧ : ∀ {V} → 𝕌 V → SetEnv V → Set
⟦ 𝕍∙ x ⟧ ρ = ρ x
⟦ ⊥∙ ⟧ ρ = ⊥
⟦ ⊤∙ ⟧ ρ = ⊤
⟦ ×∙ A B ⟧ ρ = ⟦ A ⟧ ρ × ⟦ B ⟧ ρ
⟦ ⊔∙ A B ⟧ ρ = ⟦ A ⟧ ρ ⊔ ⟦ B ⟧ ρ
⟦ ≃∙ A B ⟧ ρ = 𝕌* A B
⟦ μ∙ F ⟧ ρ = {!   !}

RelEnv : ∀ {V : Set} → Rel (SetEnv V) (SetEnv V)
RelEnv {V} ρ0 ρ1 = ∀ v → Rel (ρ0 v) (ρ1 v)

⟦_⟧* : ∀ {V} {A B : 𝕌 V} → 𝕌* A B → {ρ0 ρ1 : SetEnv V} (ρ* : RelEnv ρ0 ρ1)
           → Rel (⟦ A ⟧ ρ0) (⟦ B ⟧ ρ1)
⟦ 𝕍* v ⟧* ρ* = ρ* v
⟦ ⊥* ⟧* ρ* ()
⟦ ⊤* ⟧* ρ* _ _ = ⊤
⟦ ×* A* B* ⟧* ρ* (a0 , b0) (a1 , b1) = ⟦ A* ⟧* ρ* a0 a1 × ⟦ B* ⟧* ρ* b0 b1
⟦ ⊔* A* B* ⟧* ρ* (in1 a0) (in1 a1) = ⟦ A* ⟧* ρ* a0 a1
⟦ ⊔* A* B* ⟧* ρ* (in1 _) (in2 _) = ⊥
⟦ ⊔* A* B* ⟧* ρ* (in2 _) (in1 _) = ⊥
⟦ ⊔* A* B* ⟧* ρ* (in2 b0) (in2 b1) = ⟦ B* ⟧* ρ* b0 b1
⟦ ≃* A* B* ⟧* ρ* i0 i1 = ∀ {x0} {y0} (xy0 : i0 x0 y0) {x1} {y1} (xy1 : i1 x1 y1)
                           → Rel (⟦ A* ⟧* ρ* x0 x1) (⟦ B* ⟧* ρ* y0 y1)

-}

-- ⟦_⟧Rel : ∀ {V} (A : 𝕌 V) {ρ0 ρ1 : SetEnv V}
--           → RelEnv ρ0 ρ1 → Rel (⟦ A ⟧Set ρ0) (⟦ A ⟧Set ρ1)
-- ⟦ 𝕍∙ x ⟧Rel ρ* = ρ* x
-- ⟦ ⊥∙ ⟧Rel ρ* ()
-- ⟦ ⊤∙ ⟧Rel ρ* _ _ = ⊤
-- ⟦ ×∙ A B ⟧Rel ρ* (a0 , b0) (a1 , b1) = ⟦ A ⟧Rel ρ* a0 a1 × ⟦ B ⟧Rel ρ* b0 b1
-- ⟦ ⊔∙ A B ⟧Rel ρ* (in1 a0) (in1 a1) = ⟦ A ⟧Rel ρ* a0 a1
-- ⟦ ⊔∙ A B ⟧Rel ρ* (in1 _) (in2 _) = ⊥
-- ⟦ ⊔∙ A B ⟧Rel ρ* (in2 _) (in1 _) = ⊥
-- ⟦ ⊔∙ A B ⟧Rel ρ* (in2 b0) (in2 b1) = ⟦ B ⟧Rel ρ* b0 b1
-- ⟦ ≃∙ A B ⟧Rel ρ* i0 i1 =
--   ∀ {x0} {y0} (xy0 : i0 x0 y0) {x1} {y1} (xy1 : i1 x1 y1)
--     → Rel (⟦ A ⟧Rel ρ* x0 x1) (⟦ B ⟧Rel ρ* y0 y1)

{-
⟦_⟧*Set₀ : ∀ {V} {A B : 𝕌 V} → 𝕌* A B → (ρ : SetEnv V) → Rel (⟦ A ⟧Set ρ) (⟦ B ⟧Set ρ)
⟦ 𝕍* v ⟧*Set₀ ρ = {!   !}
⟦ ⊥* ⟧*Set₀ ρ = {!   !}
⟦ ⊤* ⟧*Set₀ ρ = {!   !}
⟦ ×* A A₁ ⟧*Set₀ ρ = {!   !}
⟦ ⊔* A A₁ ⟧*Set₀ ρ = {!   !}



⟦_⟧*Sub : ∀ {V W : Set} {A B : 𝕌 V} → 𝕌* A B → {ρ0 ρ1 : Sub V W} (ρ* : Sub* ρ0 ρ1) (σ : SetEnv W)
           → Rel (⟦ A [ ρ0 ] ⟧Set σ) (⟦ B [ ρ1 ] ⟧Set σ)
⟦ AB ⟧*Sub ρ* σ = {! AB [ ]  !}

eq : ∀ {V : Set} (A : 𝕌 V) {σ : SetEnv V} → Rel (⟦ A ⟧Set σ) (⟦ A ⟧Set σ)
eq A {σ} = let
    A𝕍∙ = A [ 𝕍∙ ]
    A[𝕍*] = A [ idSub 𝕍∙ ]*
    reflA = refl𝕌* A
    reflA* = ⟦ refl A ⟧*Set (idSub 𝕍̇∙)
  in ?


-- ⟦_⟧*Rel : ∀ {V} {A B : 𝕌 V} (R : 𝕌* A B) → {ρ0 ρ1 : SetEnv V} (ρ* : RelEnv ρ0 ρ1)
--            → (e0 : SetEnvElem ρ0) (e1 : SetEnvElem ρ1)
--            → RelEnvProof ρ* e0 e1 → ⟦ R ⟧*Set ρ* e0 e1

-- ⟦_⟧*Rel : ∀ {V} {A0 A1 : 𝕌 V} (A* : 𝕌* A0 A1) → {B0 B1 : 𝕌 V} (B* : 𝕌* B0 B1)
--             →  𝕌* A B → (ρ : SetEnv V) → Rel (⟦ A ⟧Set ρ) (⟦ B ⟧Set ρ)

SetEnv𝕌 : ∀ V → SetEnv V
SetEnv𝕌 V = λ v → 𝕌 V

RelEnv𝕌* : ∀ V → RelEnv (SetEnv𝕌 V) (SetEnv𝕌 V)
RelEnv𝕌* V = λ v → 𝕌*

T𝕌⁰ : ∀ (A : 𝕌 ⊥) → Rel (⟦ A ⟧Set ∅) (⟦ A ⟧Set ∅)
T𝕌⁰ A = ⟦ A ⟧Rel λ ()

T𝕌 : ∀ {V} (A : 𝕌 V) (ρ : SetEnv V) → Rel (⟦ A ⟧Set ρ) (⟦ A ⟧Set ρ)
T𝕌 A ρ = {!   !}

-- Id𝕌 ρ = 𝕌*
--
--
-- Eq𝕌 : ∀ {V} → Rel (𝕌 V) (𝕌 V)
-- Eq𝕌 {V} = {!   !}

-- SetEnvElem : ∀ {V} → SetEnv V → Set
-- SetEnvElem {V} ρ = ∀ v → ρ v
--
-- RelEnvProof : ∀ {V} {ρ0 ρ1 : SetEnv V} → RelEnv ρ0 ρ1 → SetEnvElem ρ0 → SetEnvElem ρ1 → Set
-- RelEnvProof {V} {ρ0} {ρ1} ρ* e0 e1 = ∀ (v : V) → ρ* v (e0 v) (e1 v)






-- the end

-- ⟦_⟧*Set : ∀ {V} {A B : 𝕌 V} → 𝕌* A B → (ρ : SetEnv V) (idρ : RelEnv ρ ρ) → Rel (⟦ A ⟧Set ρ) (⟦ B ⟧Set ρ)
-- ⟦ 𝕍* v ⟧*Set ρ a b = {!   !}
-- ⟦ ⊤* ⟧*Set ρ a b = {!   !}
-- ⟦ ×* A* A*₁ ⟧*Set ρ a b = {!   !}
-- ⟦ ⊔* A* A*₁ ⟧*Set ρ a b = {!   !}

-}
