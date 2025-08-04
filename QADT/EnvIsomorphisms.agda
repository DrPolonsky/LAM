open import Logic
open import Lifting
open import Datatypes
open import Environment
open import QADT.Isomorphisms

module QADT.EnvIsomorphisms where

SetEnv≃ : ∀ {V : Set} → SetEnv V → SetEnv V → Set
SetEnv≃ ρ σ = ∀ x → ρ x ≃ σ x

_enviso∘_ : ∀ {V : Set} {ρ σ ψ : SetEnv V} → SetEnv≃ ρ σ → SetEnv≃ σ ψ → SetEnv≃ ρ ψ
_enviso∘_ {n} {ρ} {σ} {ψ} e1 e2 x with e1 x | e2 x
... | e1x | e2x = e1x iso∘ e2x

reflSetEnv≃ : ∀ {V} (ρ : SetEnv V)  → SetEnv≃ ρ ρ
reflSetEnv≃ ρ x = id≃ (ρ x)

coskipSet≃ : ∀ {V : Set} {S1 S2 : Set} (ρ : SetEnv V) → (S1 ≃ S2) → SetEnv≃ (ρ ⅋o:= S1) (ρ ⅋o:= S2)
coskipSet≃ {n} {S1} {S2} ρ s1≃s2 o = s1≃s2
coskipSet≃ {n} {S1} {S2} ρ s1≃s2 (i y) = refl2iso refl

coskipSetEnv≃ : ∀ {V : Set} {ρ σ : SetEnv V} → (A : Set) → (SetEnv≃ ρ σ) → SetEnv≃ (ρ ⅋o:= A) (σ ⅋o:= A)
coskipSetEnv≃ {n} {ρ} {σ} A ρ≃σ (o) = id≃ A
coskipSetEnv≃ {n} {ρ} {σ} A ρ≃σ (i (f)) = ρ≃σ f

coskipSetEnv≃Set≃ : ∀ {V : Set} {X Y : Set} {ρ σ : SetEnv V} → X ≃ Y → SetEnv≃ ρ σ → SetEnv≃ (ρ ⅋o:= X) (σ ⅋o:= Y)
coskipSetEnv≃Set≃ {Y = Y} {ρ = ρ} xy ρσ x = coskipSet≃ ρ xy x iso∘ coskipSetEnv≃ Y ρσ x
