open import Logic
open import Lifting
open import Environment
open import QADT.Isomorphisms

module QADT.EnvIsomorphisms where

Env≃ : ∀ {n : ℕ} → Env n → Env n → Set
Env≃ ρ σ = ∀ x → ρ x ≃ σ x

_enviso∘_ : ∀ {n : ℕ} {ρ σ ψ : Env n} → Env≃ ρ σ → Env≃ σ ψ → Env≃ ρ ψ
_enviso∘_ {n} {ρ} {σ} {ψ} e1 e2 x with e1 x | e2 x
... | e1x | e2x = e1x iso∘ e2x

reflEnv≃ : ∀ {n} (ρ : Env n)  → Env≃ ρ ρ
reflEnv≃ ρ x = id≃ (ρ x)

coskipSet≃ : ∀ {n : ℕ} {S1 S2 : Set} (ρ : Env n) (x : Fin (succ n)) → (S1 ≃ S2) → Env≃ (coskip ρ x S1) (coskip ρ x S2)
coskipSet≃ {n} {S1} {S2} ρ (here .n) s1≃s2 (here .n) = s1≃s2
coskipSet≃ {n} {S1} {S2} ρ (here .n) s1≃s2 (down y) = refl2iso (refl (ρ y))
coskipSet≃ {.(succ n)} {S1} {S2} ρ (down x) s1≃s2 (here (succ n)) = refl2iso (refl (ρ (here _)))
coskipSet≃ {succ n} {S1} {S2} ρ (down x) s1≃s2 (down y) = coskipSet≃ (λ z → ρ (down z) ) x s1≃s2 y

coskipEnv≃ : ∀ {n : ℕ} {ρ σ : Env n} (x : Fin (succ n)) → (A : Set) → (Env≃ ρ σ ) → Env≃ (coskip ρ x A) (coskip σ x A)
coskipEnv≃ {n} {ρ} {σ} (here .n) A ρ≃σ (here .n) = iso (λ z → z) (λ z → z) refl refl
coskipEnv≃ {n} {ρ} {σ} (here .n) A ρ≃σ (down f) = ρ≃σ f
coskipEnv≃ {.(succ n)} {ρ} {σ} (down x) A ρ≃σ (here (succ n)) = ρ≃σ (here n)
coskipEnv≃ {succ n} {ρ} {σ} (down x) A ρ≃σ (down f) = coskipEnv≃ x  A (λ x₁ → ρ≃σ (down x₁) ) f

coskipEnv≃Set≃ : ∀ {n : ℕ} {X Y : Set} {ρ σ : Env n} → X ≃ Y → Env≃ ρ σ → Env≃ (extEnv X ρ) (extEnv Y σ)
coskipEnv≃Set≃ {Y = Y} {ρ = ρ} xy ρσ = λ x → coskipSet≃ ρ (here _) xy x iso∘ coskipEnv≃ (here _) Y ρσ x
