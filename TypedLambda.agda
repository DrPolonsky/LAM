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
    Var : ∀ {Γ A} {x}    →  Γ x ≡ A                      → Γ ⊢ var x ∶ A
    App : ∀ {Γ A B M N}  →  Γ ⊢ M ∶ (A ⇒ B) → Γ ⊢ N ∶ A  → Γ ⊢ app M N ∶ B
    Abs : ∀ {Γ M A B}    →  io Γ A ⊢ M ∶ B               → Γ ⊢ abs M ∶ (A ⇒ B)

  _≅⊢_∶_ : ∀ {V} {Γ Δ : Cxt V} → Γ ≅ Δ → ∀ {M} {A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A
  _≅⊢_∶_ ΓΔ (Var {x = x} d) = Var (ΓΔ x ~! d)
  _≅⊢_∶_ ΓΔ (App der1 der2) = App (_≅⊢_∶_ ΓΔ der1) (_≅⊢_∶_ ΓΔ der2)
  _≅⊢_∶_ ΓΔ (Abs der0) = Abs (_≅⊢_∶_ (io≅ ΓΔ refl ) der0)

  ioNat : ∀ {A B C : Set} (f : B → C) (g : A → B) (c : C) → io (f ∘ g) c ≅ io f c ∘ ↑→ g
  ioNat f g d (i x) = refl
  ioNat f g d o = refl

  -- make B explicit!!
  weak⊢ : ∀ {V W} {Δ : Cxt W} {N : Λ V} {A B : 𝕋} (f : V → W) → (Δ ∘ f) ⊢ N ∶ A → Δ ⊢ Λ→ f N ∶ A
  weak⊢ f (Var d) = Var d
  weak⊢ f (App {A = A} {B} d1 d2) = App (weak⊢ {B = A ⇒ B} f d1) (weak⊢ {B = A} f d2)
  weak⊢ {Δ = Δ} f (Abs {A = A} {B} d0) = Abs (weak⊢ {B = A} (↑→ f) (_≅⊢_∶_ (ioNat Δ f A ) d0 ) )

  lift⊢ : ∀ {V W : Set} {Γ : Cxt V} {Δ : Cxt W} {Ns : V → Λ W} {B : 𝕋}
          → (∀ v → Δ ⊢ Ns v ∶ Γ v) → ∀ (v : ↑ V) → io Δ B ⊢ lift Ns v ∶ io Γ B v
  lift⊢ {V} {W} {Γ} {Δ} {Ns} {B} ν (i x) = weak⊢ {B = B} i (ν x)
    -- _≅⊢_∶_ {!   !} (weak⊢ i (ν x) ) -- weak⊢ (ν x)
  -- ν x has type       Δ ⊢ Ns x ∶ Γ x
  -- Goal is       io Δ B ⊢ Λ→ i (Ns x) ∶ Γ x
  lift⊢ {V} {W} {Γ} {Δ} {Ns} {B} ν o = Var refl

  SubLemma⊢Var : ∀ {V : Set} {Γ : Cxt V} {y : V} {B : 𝕋}
                   {W : Set} {Δ : Cxt W} {Ns : V → Λ W}
                    → Γ y ≡ B  →  (∀ v → Δ ⊢ Ns v ∶ Γ v) →  Δ ⊢ Ns y ∶ B
  SubLemma⊢Var {V} {Γ} {y} {B} {W} {Δ} {Ns} Γy=B ν
      = transp {A = 𝕋} (λ T → Δ ⊢ Ns y ∶ T) Γy=B (ν y)

  SubLemma⊢ : ∀ {V : Set} {Γ : Cxt V} {M : Λ V} {B : 𝕋}
                {W : Set} {Δ : Cxt W} {Ns : V → Λ W}
                → Γ ⊢ M ∶ B  →  (∀ v → Δ ⊢ Ns v ∶ Γ v) →  Δ ⊢ M [ Ns ] ∶ B
  SubLemma⊢ {V} {Γ} {(var y)} {B} {W} {Δ} {Ns} (Var Γy=B) ν
             = SubLemma⊢Var {Γ = Γ} {y = y} {Ns = Ns} Γy=B ν
  SubLemma⊢ {V} {Γ} {(app M1 M2)} {B} {W} {Δ} {Ns} (App μ1 μ2) ν
             = App (SubLemma⊢ μ1 ν) (SubLemma⊢ μ2 ν)
  SubLemma⊢ {V} {Γ} {(abs M0)} {(B1 ⇒ B2)} {W} {Δ} {Ns} (Abs μ0) ν
             = Abs (SubLemma⊢ μ0 (lift⊢ ν ) )

  -- SubLemma⊢ₒ (Var {x = x} Γx=A) n = SubLemma⊢ₒVar x Γx=A n
  -- SubLemma⊢ₒ (App m1 m2) n = App (SubLemma⊢ₒ m1 n) (SubLemma⊢ₒ m2 n)
  -- SubLemma⊢ₒ (Abs m0) n =
  --   let rc = SubLemma⊢ₒ m0 {!   !}
  --    in Abs {!   !} -- Recursive call is BROKEN, lemma needs to be generalized


  -- Prop 1B.5 in [BDS 2010]
  SubLemma⊢ₒ : ∀ {V : Set} {Γ : Cxt V} {M : Λ (↑ V)} {N : Λ V} {A B : 𝕋}
              → io Γ A ⊢ M ∶ B  →  Γ ⊢ N ∶ A  →  Γ ⊢ M [ N ]ₒ ∶ B
  SubLemma⊢ₒ {V} {Γ} {M} {N} {A} {B} μ ν
    = SubLemma⊢ {↑ V} {io Γ A} {M} {B} {V} {Γ} {io var N} μ νs where
      νs : (v : ↑ V) → Γ ⊢ io var N v ∶ io Γ A v
      νs (i x) = Var refl
      νs o = ν

open Curry

module Church where
  data ΛCh {V : Set} : (Cxt V) → 𝕋 → Set where
    varCh : ∀ {Γ} x {A} → Γ x ≡ A → ΛCh Γ A
    appCh : ∀ {Γ} {A B}   → ΛCh Γ (A ⇒ B) → ΛCh Γ A → ΛCh Γ B
    absCh : ∀ {Γ} {A B}   → ΛCh (io Γ A) (B)        → ΛCh Γ (A ⇒ B)

  erase : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → Λ V
  erase (varCh x e) = var x
  erase (appCh M1 M2) = app (erase M1) (erase M2)
  erase (absCh M0) = abs (erase M0)

  prop1B19i : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛCh Γ A) → Γ ⊢ erase M ∶ A
  prop1B19i (varCh x Γx≡A) = Var Γx≡A
  prop1B19i (appCh M1 M2) = App (prop1B19i M1) (prop1B19i M2)
  prop1B19i (absCh M0) = Abs (prop1B19i M0)

  embellish : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛCh Γ A
  embellish (var x) (Var Γx≡A) = varCh x Γx≡A
  embellish (app M1 M2) (App d1 d2) = appCh (embellish M1 d1) (embellish M2 d2)
  embellish (abs M0) (Abs d) = absCh (embellish M0 d)

  prop1B19ii : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
               → erase (embellish M d) ≡ M
  prop1B19ii M d = {!   !}

  ΛCh≃ : ∀ {V : Set} {Γ Δ : Cxt V} {A : 𝕋} → Γ ≅ Δ → ΛCh Γ A → ΛCh Δ A
  ΛCh≃ g=d (varCh x e) = varCh x (g=d x ~! e)
  ΛCh≃ g=d (appCh t1 t2) = appCh (ΛCh≃ g=d  t1) (ΛCh≃ g=d t2)
  ΛCh≃ g=d (absCh t0) = absCh (ΛCh≃ (io≅ g=d refl) t0)

  -- ΛCh→ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) → ΛCh Γ A → ΛCh (Γ ∘ f) A
  ΛCh→ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) → ΛCh (Γ ∘ f) A → ΛCh Γ A
  ΛCh→ f (varCh x e) = varCh (f x) e
  ΛCh→ f (appCh M1 M2) = appCh (ΛCh→ f M1) (ΛCh→ f M2)
  ΛCh→ f (absCh M0) = absCh (ΛCh→ (↑→ f) (ΛCh≃ (λ {  (i x) → refl ; o → refl }) M0 ) )

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
