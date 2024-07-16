-- {-# OPTIONS --cubical-compatible #-}
-- {-# OPTIONS --without-K  #-}

module TypedLambda (𝔸 : Set) where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Reduction
open import ClosureOperators

-- term2 = "λxλy.y(λz.z(λa.ax)y)x"
term2 : Λ⁰
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
              → io Γ A ⊢ M ∶ B  →  Γ ⊢ N ∶ A  →  Γ ⊢ M [ N ]ᵒ ∶ B
  SubLemma⊢ₒ μ ν = SubLemma⊢ μ (io𝓟 _ (λ x → Var x refl) ν)

  SubReduction⊢₁ : ∀ {V : Set} {Γ : Cxt V} {M N : Λ V} {A : 𝕋}
                    → Γ ⊢ M ∶ A → M ⟶β N → Γ ⊢ N ∶ A
  -- SubReduction⊢ {V} {Γ} {M} {N} {A} (App {A = B} {N = P} d1 d2) (redexβ {s = G} refl)
  SubReduction⊢₁ (App (Abs d1) d2) (redexβ refl) = SubLemma⊢ₒ d1 d2
  SubReduction⊢₁ (App d1 d2) (appLβ re) = App (SubReduction⊢₁ d1 re) d2
  SubReduction⊢₁ (App d1 d2) (appRβ re) = App d1 (SubReduction⊢₁ d2 re)
  SubReduction⊢₁ (Abs d0) (absβ re) = Abs (SubReduction⊢₁ d0 re)


  SubReduction⊢ : ∀ {V : Set} {Γ : Cxt V} {M N : Λ V} {A : 𝕋} → Γ ⊢ M ∶ A → M ⟶⋆β N → Γ ⊢ N ∶ A
  SubReduction⊢ d (ax⋆ M→N) = SubReduction⊢₁ d M→N
  SubReduction⊢ d ε⋆ = d
  SubReduction⊢ d (M→y ,⋆ y→⋆N) = SubReduction⊢ (SubReduction⊢₁ d M→y) y→⋆N

open Curry

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

  Λ→dB : ∀ {A B : Set} (f : A → B) → ΛdB A → ΛdB B
  Λ→dB f (vardB x) = vardB (f x)
  Λ→dB f (appdB M1 M2) = appdB (Λ→dB f M1) (Λ→dB f M2)
  Λ→dB f (absdB x M0) = absdB x (Λ→dB (↑→ f) M0)

  _≅⊢dB_ : ∀ {V} {Γ Δ : Cxt V} → Γ ≅ Δ → ∀ {M : ΛdB V} {A} → Γ ⊢dB M ∶ A → Δ ⊢dB M ∶ A
  Γ≅Δ ≅⊢dB VardB e = VardB (Γ≅Δ _ ~! e )
  Γ≅Δ ≅⊢dB AppdB d1 d2 = AppdB (Γ≅Δ ≅⊢dB d1) (Γ≅Δ ≅⊢dB d2)
  Γ≅Δ ≅⊢dB AbsdB d0 = AbsdB (io≅ Γ≅Δ refl ≅⊢dB d0)

  -- weak⊢ : ∀ {V W} {Δ : Cxt W} {N : Λ V} {A : 𝕋} (f : V → W) → (Δ ∘ f) ⊢ N ∶ A → Δ ⊢ Λ→ f N ∶ A
  weak⊢dB : ∀ {V W} {Δ : Cxt W} {N : ΛdB V} {A : 𝕋} (f : V → W) → (Δ ∘ f) ⊢dB N ∶ A → Δ ⊢dB (Λ→dB f N) ∶ A
  weak⊢dB f (VardB p) = VardB p
  weak⊢dB f (AppdB d1 d2) = AppdB (weak⊢dB f d1) (weak⊢dB f d2)
  weak⊢dB f (AbsdB d0) = AbsdB (weak⊢dB (↑→ f) (io-nat _ f _ ≅⊢dB d0))


open DeBruijn

module Church where
  data ΛCh {V : Set} : (Cxt V) → 𝕋 → Set where
    varCh : ∀ {Γ} {A} x   → Γ x ≡ A                 → ΛCh Γ A
    appCh : ∀ {Γ} {A B}   → ΛCh Γ (A ⇒ B) → ΛCh Γ A → ΛCh Γ B
    absCh : ∀ {Γ} {A B}   → ΛCh (io Γ A) (B)        → ΛCh Γ (A ⇒ B)

  erase1 : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → ΛdB V
  erase1         (varCh x Γx≡A) = vardB x
  erase1         (appCh M1 M2)  = appdB (erase1 M1) (erase1 M2)
  erase1 {A = A} (absCh M0)     = absdB A (erase1 M0)

  erase2 : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛdB V → Λ V
  erase2 {V} {Γ} {A} (vardB x)     = var x
  erase2 {V} {Γ} {A} (appdB M1 M2) = app (erase2 {V} {Γ} {A} M1) (erase2 {V} {Γ} {A} M2)
  erase2 {V} {Γ} {A} (absdB x M0)  = abs (erase2 {↑ V} {λ Γ → x} {A} M0)

  erase : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → Λ V
  erase {V} {Γ} {A} = erase2 {V} {Γ} {A} ∘ erase1
  -- erase (varCh x e)   = var x
  -- erase (appCh M1 M2) = app (erase M1) (erase M2)
  -- erase (absCh M0)    = abs (erase M0)
  
  prop1B19i : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛCh Γ A) → Γ ⊢ erase M ∶ A
  prop1B19i (varCh x Γx≡A) = Var x Γx≡A
  prop1B19i (appCh M1 M2)  = App (prop1B19i M1) (prop1B19i M2)
  prop1B19i (absCh M0)     = Abs (prop1B19i M0)

  embellish : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛCh Γ A
  embellish (var x)     (Var _ Γx≡A) = varCh x Γx≡A
  embellish (app M1 M2) (App d1 d2)  = appCh (embellish M1 d1) (embellish M2 d2)
  embellish (abs M0)    (Abs d)      = absCh (embellish M0 d)

  embellishCu→dB : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛdB V
  embellishCu→dB (var x) d               = vardB x
  embellishCu→dB (app M1 M2) (App d1 d2) = appdB (embellishCu→dB M1 d1) (embellishCu→dB M2 d2)
  embellishCu→dB (abs M0) (Abs {A = A} d0)       = absdB A (embellishCu→dB M0 d0)

  embellishCu→dB⊢ : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
                    → Γ ⊢dB embellishCu→dB M d ∶ A
  embellishCu→dB⊢ (var _) (Var _ Γx≡A) = VardB Γx≡A
  embellishCu→dB⊢ (app M1 M2) (App d1 d2) = AppdB (embellishCu→dB⊢ M1 d1) (embellishCu→dB⊢ M2 d2)
  embellishCu→dB⊢ (abs M0) (Abs d0) = AbsdB (embellishCu→dB⊢ M0 d0)

  embellishdB→Ch : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛdB V) → Γ ⊢dB M ∶ A → ΛCh Γ A
  embellishdB→Ch (vardB x)     (VardB Γx≡A)  = varCh x Γx≡A
  embellishdB→Ch (appdB M1 M2) (AppdB d1 d2) = appCh (embellishdB→Ch M1 d1) (embellishdB→Ch M2 d2)
  embellishdB→Ch (absdB x M0)  (AbsdB d0)    = absCh (embellishdB→Ch M0 d0)

  -- embellishCu→Ch : ∀ {V} {Γ : Cxt V} {A : 𝕋} {M : Λ V} → Γ ⊢ M ∶ A →

  prop1B19ii : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
               → erase (embellish M d) ≡ M
  prop1B19ii (var x)     (Var _ _)   = refl
  prop1B19ii (app M1 M2) (App d1 d2) = cong2 app (prop1B19ii M1 d1) (prop1B19ii M2 d2)
  prop1B19ii (abs M0)    (Abs d0)    = cong abs  (prop1B19ii M0 d0)

  ΛCh≃ : ∀ {V : Set} {Γ Δ : Cxt V} {A : 𝕋} → Γ ≅ Δ → ΛCh Γ A → ΛCh Δ A
  ΛCh≃ g=d (varCh x e)   = varCh x (g=d x ~! e)
  ΛCh≃ g=d (appCh t1 t2) = appCh (ΛCh≃ g=d  t1) (ΛCh≃ g=d t2)
  ΛCh≃ g=d (absCh t0)    = absCh (ΛCh≃ (io≅ g=d refl) t0)

  ΛCh→≅ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) (Δ : Cxt V)
            → Δ ≅ Γ ∘ f → ΛCh Δ A → ΛCh Γ A
  ΛCh→≅ f Δ Δ=Γf (varCh x e)   = varCh (f x) (Δ=Γf x ~! e )
  ΛCh→≅ f Δ Δ=Γf (appCh d1 d2) = appCh (ΛCh→≅ f Δ Δ=Γf d1) (ΛCh→≅ f Δ Δ=Γf d2)
  ΛCh→≅ f Δ Δ=Γf (absCh d0)    = absCh (ΛCh→≅ (↑→ f) (io Δ _) cxt≅ d0) where
    cxt≅ : _
    cxt≅ (i x) = Δ=Γf  x
    cxt≅ o     = refl

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

  NF : ∀ {X} → 𝓟 (Λ X)
  NF M = ∀ N → ¬ (M ⟶β N)
  
  NFCh : ∀ (V : Set) (Γ : Cxt V) (A : 𝕋) → 𝓟 (ΛCh Γ A)
  NFCh V Γ A M = ∀ N → ¬ (erase M ⟶β erase {V} {Γ} {A} N)

  CxtEqIrrel : ∀ {V} (Γ : Cxt V) (x : V) (A : 𝕋) (p1 p2 : Γ x ≡ A) → p1 ≡ p2
  CxtEqIrrel Γ x .(Γ x) refl refl = refl

  absChInv : ∀ {V} {Γ : Cxt V} {A B : 𝕋} (N1 N2 : ΛCh (io Γ A) B) → absCh N1 ≡ absCh N2 → N1 ≡ N2
  absChInv N1 .N1 refl = refl

  absInv : ∀ {V} {N1 N2 : Λ (↑ V)} → abs N1 ≡ abs N2 → N1 ≡ N2
  absInv refl = refl

  Prop1B24 : ∀ {V : Set} {Γ : Cxt V} (A : 𝕋) (M : Λ V) → M ∈ NF
                → (d : Γ ⊢ M ∶ A) → ∀ (N : ΛCh Γ A) → erase N ≡ M → N ≡ embellish M d
  Prop1B24 {V} {Γ} A (var x) M∈NF (Var .x Γx=A) (varCh .x Γy=A) refl
    = cong (varCh x) (CxtEqIrrel Γ x A Γy=A Γx=A )
  Prop1B24 A (app M1 M2) M∈NF d N eN=M = {! M∈NF   !}
  Prop1B24 (A ⇒ B) (abs M0) M∈NF (Abs d) (absCh N) eN=M = cong absCh c where
    b = λ M' M0→M' → M∈NF (abs M') (absβ M0→M')
    c = Prop1B24 B M0 b d N (absInv eN=M)

  -- should probably change NF to NFCh here (not working with ∈)
  Prop1B25 : ∀ {V : Set} {Γ : Cxt V} (A : 𝕋) (M : ΛCh Γ A)
              → erase M ∈ NF → (Γ ⊢ erase M ∶ A)
  Prop1B25 A (varCh x Γx=A) nf = Var x Γx=A
  Prop1B25 A (appCh M1 M2) nf = {!   !}
  Prop1B25 (A ⇒ B) (absCh M) nf = {!   !}
  
  -- data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
  --   Var : ∀ {Γ : Cxt V} {x : V} {A : 𝕋} → Γ x ≡ A → Γ ⊢ var x ∶ A
  --   App : ∀ {Γ : Cxt V} {M N : Λ V} {A B : 𝕋}
  --           → Γ ⊢ M ∶ (A ⇒ B)  →  Γ ⊢ N ∶ A  →  Γ ⊢ app M N ∶ B
  --   Abs : ∀ {Γ : Cxt V} {M : Λ (↑ V)} {A B : 𝕋}
  --           → io Γ A ⊢ M ∶ B  →  Γ ⊢ abs M ∶ (A ⇒ B)
