open import Logic
open import Lifting
open import Datatypes
open import Environment
open import QADT.Isomorphisms

module QADT.EnvIsomorphisms where

SetEnv≃ : ∀ {n : ℕ} → SetEnv n → SetEnv n → Set
SetEnv≃ ρ σ = ∀ x → ρ x ≃ σ x

_enviso∘_ : ∀ {n : ℕ} {ρ σ ψ : SetEnv n} → SetEnv≃ ρ σ → SetEnv≃ σ ψ → SetEnv≃ ρ ψ
_enviso∘_ {n} {ρ} {σ} {ψ} e1 e2 x with e1 x | e2 x
... | e1x | e2x = e1x iso∘ e2x

reflSetEnv≃ : ∀ {n} (ρ : SetEnv n)  → SetEnv≃ ρ ρ
reflSetEnv≃ ρ x = id≃ (ρ x)

coskipSet≃ : ∀ {n : ℕ} {S1 S2 : Set} (ρ : SetEnv n) (x : Fin (succ n)) → (S1 ≃ S2) → SetEnv≃ (ρ ⅋ x := S1) (ρ ⅋ x := S2)
coskipSet≃ {n} {S1} {S2} ρ (o) s1≃s2 (o) = s1≃s2
coskipSet≃ {n} {S1} {S2} ρ (o) s1≃s2 (i (y)) = refl2iso refl
coskipSet≃ {succ n} {S1} {S2} ρ (i (x)) s1≃s2 (o) = refl2iso refl
coskipSet≃ {succ n} {S1} {S2} ρ (i (x)) s1≃s2 (i (y)) = coskipSet≃ (λ z → ρ (i (z)) ) x s1≃s2 y

coskipSetEnv≃ : ∀ {n : ℕ} {ρ σ : SetEnv n} (x : Fin (succ n)) → (A : Set) → (SetEnv≃ ρ σ ) → SetEnv≃ (ρ ⅋ x := A) (σ ⅋ x := A)
coskipSetEnv≃ {n} {ρ} {σ} (o) A ρ≃σ (o) = id≃ A
coskipSetEnv≃ {n} {ρ} {σ} (o) A ρ≃σ (i (f)) = ρ≃σ f
coskipSetEnv≃ {succ n} {ρ} {σ} (i (x)) A ρ≃σ (o) = ρ≃σ (o)
coskipSetEnv≃ {succ n} {ρ} {σ} (i (x)) A ρ≃σ (i (f)) = coskipSetEnv≃ x  A (λ x₁ → ρ≃σ (i (x₁)) ) f

coskipSetEnv≃Set≃ : ∀ {n : ℕ} {X Y : Set} {ρ σ : SetEnv n} → X ≃ Y → SetEnv≃ ρ σ → SetEnv≃ (ρ ⅋o:= X) (σ ⅋o:= Y)
coskipSetEnv≃Set≃ {Y = Y} {ρ = ρ} xy ρσ = λ x → coskipSet≃ ρ (o) xy x iso∘ coskipSetEnv≃ (o) Y ρσ x
