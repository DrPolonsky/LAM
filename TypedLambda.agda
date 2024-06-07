module TypedLambda (𝔸 : Set) where

open import Logic
open import Lifting
open import Lambda

-- term2 = "λxλy.y(λz.z(λa.ax)y)x"
term2 : Λ₀
term2 = abs (abs (app (app (var o ) (abs (app (app (var o)
  (abs (app (var o) (var (i (i (i o))))))) (var (i o))))) (var (i o))))

data 𝕋 : Set where
  atom : 𝔸 → 𝕋
  _⇒_  : 𝕋 → 𝕋 → 𝕋

module Curry where

{- In order to be able to express a (hypothetical) type judgment Γ ⊢ t : A,
   we need to instantiate the type Λ of t at a particular set of variables V.
Hence, such a type judgment must be parametrized by the set V of free variables.

Moreover, the variables in V should all be provided a type by the context Γ.
So, "Γ : Cxt V" should mean:
  1. dom(Γ) = V, and
  2. for each x : V, Γ provides a type A=Γ(x) : 𝕋
-}
  Cxt : Set → Set
  Cxt V = V → 𝕋

  -- ⊢ is \|- or \vdash, ∶ is \:
  data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
    Var : ∀ {Γ x A}      →  Γ x ≡ A                      → Γ ⊢ var x ∶ A
    App : ∀ {Γ A B M N}  →  Γ ⊢ M ∶ (A ⇒ B) → Γ ⊢ N ∶ A  → Γ ⊢ app M N ∶ B
    Abs : ∀ {Γ M A B}    →  io Γ A ⊢ M ∶ B               → Γ ⊢ abs M ∶ (A ⇒ B)

  -- data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
  --   Var : ∀ {Γ : Cxt V} {x : V} {A : 𝕋} → Γ x ≡ A → Γ ⊢ var x ∶ A
  --   App : ∀ {Γ : Cxt V} {M N : Λ V} {A B : 𝕋}
  --           → Γ ⊢ M ∶ (A ⇒ B)  →  Γ ⊢ N ∶ A  →  Γ ⊢ app M N ∶ B
  --   Abs : ∀ {Γ : Cxt V} {M : Λ (↑ V)} {A B : 𝕋}
  --           → io Γ A ⊢ M ∶ B  →  Γ ⊢ abs M ∶ (A ⇒ B)

module Church where

  -- 𝑽ᵀ : Set
  -- 𝑽ᵀ = 𝑽 ∧ 𝕋

  -- data ΛCh : 𝕋 → Set where
  --   var : ∀ {A : 𝕋} → 𝑽 → Λ A
  --   app : ∀ {A B : 𝕋} → Λ (A ⇒ B) → Λ A → Λ B
  --   abs : ∀ {A B : 𝕋} → 𝑽 → Λ (B) → Λ (A ⇒ B)
