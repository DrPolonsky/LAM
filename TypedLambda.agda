module TypedLambda (𝔸 : Set) where

open import Logic
open import Lifting
open import Lambda
open import Predicates

-- term2 = "λxλy.y(λz.z(λa.ax)y)x"
term2 : Λ₀
term2 = abs (abs (app (app (var o ) (abs (app (app (var o)
  (abs (app (var o) (var (i (i (i o))))))) (var (i o))))) (var (i o))))

data 𝕋 : Set where
  atom : 𝔸 → 𝕋
  _⇒_  : 𝕋 → 𝕋 → 𝕋

Cxt : Set → Set
Cxt V = V → 𝕋

module Curry where

{- In order to be able to express a (hypothetical) type judgment Γ ⊢ t : A,
   we need to instantiate the type Λ of t at a particular set of variables V.
Hence, such a type judgment must be parametrized by the set V of free variables.

Moreover, the variables in V should all be provided a type by the context Γ.
So, "Γ : Cxt V" should mean:
  1. dom(Γ) = V, and
  2. for each x : V, Γ provides a type A=Γ(x) : 𝕋
-}
  -- ⊢ is \|- or \vdash, ∶ is \:
  data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
    Var : ∀ {Γ A} x      →  Γ x ≡ A                      → Γ ⊢ var x ∶ A
    App : ∀ {Γ A B M N}  →  Γ ⊢ M ∶ (A ⇒ B) → Γ ⊢ N ∶ A  → Γ ⊢ app M N ∶ B
    Abs : ∀ {Γ M A B}    →  io Γ A ⊢ M ∶ B               → Γ ⊢ abs M ∶ (A ⇒ B)

  _≅⊢_ : ∀ {V} {Γ Δ : Cxt V} → Γ ≅ Δ → ∀ {M} {A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A
  ΓΔ ≅⊢ (Var x d)   = Var x (ΓΔ x ~! d)
  ΓΔ ≅⊢ (App d1 d2) = App (ΓΔ ≅⊢ d1) (ΓΔ ≅⊢ d2)
  ΓΔ ≅⊢ (Abs d0)    = Abs (io≅ ΓΔ refl ≅⊢ d0)

  ≅⊢⇔ : ∀ {V} {Γ Δ : Cxt V} → Γ ≅ Δ → ∀ {M} {A} → Γ ⊢ M ∶ A ↔ Δ ⊢ M ∶ A
  ≅⊢⇔ Γ≅Δ = (_≅⊢_ Γ≅Δ) , (_≅⊢_ (~≅ Γ≅Δ) )

  -- make B explicit!!
  weak⊢ : ∀ {V W} {Δ : Cxt W} {N : Λ V} {A : 𝕋} (f : V → W) → (Δ ∘ f) ⊢ N ∶ A → Δ ⊢ Λ→ f N ∶ A
  weak⊢ f (Var x d)   = Var (f x) d
  weak⊢ f (App d1 d2) = App (weak⊢ f d1)  (weak⊢ f d2)
  weak⊢ f (Abs d0)    = Abs (weak⊢ (↑→ f) (io-nat _ f _ ≅⊢ d0))

  lift⊢ : ∀ {V W : Set} {Γ : Cxt V} {Δ : Cxt W} {Ns : V → Λ W} {B : 𝕋}
          → (∀ v → Δ ⊢ Ns v ∶ Γ v) → ∀ (v : ↑ V) → io Δ B ⊢ lift Ns v ∶ io Γ B v
  lift⊢ ν (i x) = weak⊢ i (ν x)
  lift⊢ ν o     = Var o refl

  SubLemma⊢Var : ∀ {V : Set} {Γ : Cxt V} {y : V} {B : 𝕋}
                   {W : Set} {Δ : Cxt W} {Ns : V → Λ W}
                    → Γ y ≡ B  →  (∀ v → Δ ⊢ Ns v ∶ Γ v) →  Δ ⊢ Ns y ∶ B
  SubLemma⊢Var Γy=B ν = transp (λ T → _ ⊢ _ ∶ T) Γy=B (ν _)

  SubLemma⊢ : ∀ {V : Set} {Γ : Cxt V} {M : Λ V} {B : 𝕋}
                {W : Set} {Δ : Cxt W} {Ns : V → Λ W}
                → Γ ⊢ M ∶ B  →  (∀ v → Δ ⊢ Ns v ∶ Γ v) →  Δ ⊢ M [ Ns ] ∶ B
  SubLemma⊢ (Var y Γy=B) ν = SubLemma⊢Var Γy=B ν
  SubLemma⊢ (App μ1 μ2)  ν = App (SubLemma⊢ μ1 ν) (SubLemma⊢ μ2 ν)
  SubLemma⊢ (Abs μ0)     ν = Abs (SubLemma⊢ μ0 (lift⊢ ν))

  -- Prop 1B.5 in [BDS 2010]
  SubLemma⊢ₒ : ∀ {V : Set} {Γ : Cxt V} {M : Λ (↑ V)} {N : Λ V} {A B : 𝕋}
              → io Γ A ⊢ M ∶ B  →  Γ ⊢ N ∶ A  →  Γ ⊢ M [ N ]ₒ ∶ B
  SubLemma⊢ₒ μ ν = SubLemma⊢ μ (io𝓟 _ (λ x → Var x refl) ν)


open Curry

{-
module DeBruijn where

  data ΛdB (V : Set) : Set where
    vardB : V → ΛdB V
    appdB : ΛdB V → ΛdB V → ΛdB V
    absdB : 𝕋 → ΛdB (↑ V) → ΛdB V

  -- λx:a→b. λy:a. xy
  exdB : 𝔸 → 𝔸 → ΛdB ⊥
  exdB α β = absdB (atom α ⇒ atom β) (absdB (atom α) (appdB (vardB (o)) (vardB (i o ))))

  -- λx. λy.xy
  exPure : 𝔸 → 𝔸 → Λ ⊥
  exPure α β = abs (abs (app (var (i o)) (var o) ) )

  data _⊢dB_∶_ {V : Set} : Cxt V → ΛdB V → 𝕋 → Set where
    VardB : ∀ {Γ A} {x}    →  Γ x ≡ A                          → Γ ⊢dB vardB x ∶ A
    AppdB : ∀ {Γ A B M N}  →  Γ ⊢dB M ∶ (A ⇒ B) → Γ ⊢dB N ∶ A  → Γ ⊢dB appdB M N ∶ B
    AbsdB : ∀ {Γ M A B}    →  io Γ A ⊢dB M ∶ B                 → Γ ⊢dB absdB A M ∶ (A ⇒ B)

open DeBruijn

module Church where
  data ΛCh {V : Set} : (Cxt V) → 𝕋 → Set where
    varCh : ∀ {Γ} {A} x   → Γ x ≡ A                 → ΛCh Γ A
    appCh : ∀ {Γ} {A B}   → ΛCh Γ (A ⇒ B) → ΛCh Γ A → ΛCh Γ B
    absCh : ∀ {Γ} {A B}   → ΛCh (io Γ A) (B)        → ΛCh Γ (A ⇒ B)

  erase1 : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → ΛdB V
  erase1 t = {!   !}
  erase2 : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛdB V → Λ V
  erase2 t = {!   !}

  erase : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → Λ V
  -- erase = erase2 ∘ erase1
  erase (varCh x e)   = var x
  erase (appCh M1 M2) = app (erase M1) (erase M2)
  erase (absCh M0)    = abs (erase M0)

  prop1B19i : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛCh Γ A) → Γ ⊢ erase M ∶ A
  prop1B19i (varCh x Γx≡A) = Var Γx≡A
  prop1B19i (appCh M1 M2)  = App (prop1B19i M1) (prop1B19i M2)
  prop1B19i (absCh M0)     = Abs (prop1B19i M0)

  embellish : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛCh Γ A
  embellish (var x)     (Var Γx≡A)  = varCh x Γx≡A
  embellish (app M1 M2) (App d1 d2) = appCh (embellish M1 d1) (embellish M2 d2)
  embellish (abs M0)    (Abs d)     = absCh (embellish M0 d)

  embellishdB→Ch : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛdB V) → Γ ⊢dB M ∶ A → ΛCh Γ A
  embellishdB→Ch M d = {!   !}
  embellishCu→dB : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛdB V
  embellishCu→dB M d = {!   !}
  embellishCu→dB⊢ : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
                    → Γ ⊢dB embellishCu→dB M d ∶ A
  embellishCu→dB⊢ M d = {!   !}

  prop1B19ii : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
               → erase (embellish M d) ≡ M
  prop1B19ii (var x)     (Var _)     = refl
  prop1B19ii (app M1 M2) (App d1 d2) = cong2 app (prop1B19ii M1 d1) (prop1B19ii M2 d2)
  prop1B19ii (abs M0)    (Abs d0)    = cong abs (prop1B19ii M0 d0)

  ΛCh≃ : ∀ {V : Set} {Γ Δ : Cxt V} {A : 𝕋} → Γ ≅ Δ → ΛCh Γ A → ΛCh Δ A
  ΛCh≃ g=d (varCh x e) = varCh x (g=d x ~! e)
  ΛCh≃ g=d (appCh t1 t2) = appCh (ΛCh≃ g=d  t1) (ΛCh≃ g=d t2)
  ΛCh≃ g=d (absCh t0) = absCh (ΛCh≃ (io≅ g=d refl) t0)

  ΛCh→≅ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) (Δ : Cxt V)
            → Δ ≅ Γ ∘ f → ΛCh Δ A → ΛCh Γ A
  ΛCh→≅ f Δ Δ=Γf (varCh x e) = varCh (f x) (Δ=Γf x ~! e )
  ΛCh→≅ f Δ Δ=Γf (appCh d1 d2) = appCh (ΛCh→≅ f Δ Δ=Γf d1) (ΛCh→≅ f Δ Δ=Γf d2)
  ΛCh→≅ f Δ Δ=Γf (absCh d0) = absCh (ΛCh→≅ (↑→ f) (io Δ _) cxt≅ d0) where
    cxt≅ : _
    cxt≅ (i x) = Δ=Γf  x
    cxt≅ o = refl

  -- ΛCh→ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) → ΛCh Γ A → ΛCh (Γ ∘ f) A
  ΛCh→ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) → ΛCh (Γ ∘ f) A → ΛCh Γ A
  ΛCh→ {Γ = Γ} f M = ΛCh→≅ f (Γ ∘ f) !≅! M

  _[_]Ch : ∀ {V W : Set} {Γ : Cxt V} {Δ : Cxt W} {A} → ΛCh Γ A → (N : ∀ (x : V) → ΛCh Δ (Γ x))
            → ΛCh Δ A
  varCh x e [ N ]Ch = transp (ΛCh _) e (N x)
  appCh M1 M2     [ N ]Ch = appCh (M1 [ N ]Ch) (M2 [ N ]Ch)
  absCh M0        [ N ]Ch = absCh (M0 [ N' ]Ch) where
    N' : _ -- ∀ (x : ↑ V) → ΛCh (io Δ A) (io Γ A x)
    N' (i x) = ΛCh→ i (N x)
    N' o     = varCh o refl


  -- data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
  --   Var : ∀ {Γ : Cxt V} {x : V} {A : 𝕋} → Γ x ≡ A → Γ ⊢ var x ∶ A
  --   App : ∀ {Γ : Cxt V} {M N : Λ V} {A B : 𝕋}
  --           → Γ ⊢ M ∶ (A ⇒ B)  →  Γ ⊢ N ∶ A  →  Γ ⊢ app M N ∶ B
  --   Abs : ∀ {Γ : Cxt V} {M : Λ (↑ V)} {A B : 𝕋}
  --           → io Γ A ⊢ M ∶ B  →  Γ ⊢ abs M ∶ (A ⇒ B)
-}
