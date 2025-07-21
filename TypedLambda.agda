-- {-# OPTIONS --cubical-compatible #-}
-- {-# OPTIONS --without-K  #-}
{-# OPTIONS --allow-unsolved-metas #-}

module TypedLambda (𝔸 : Set) where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Reduction
open import Relations.ClosureOperators

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

  SubReduction⊢₁ : ∀ {V : Set} {Γ : Cxt V} {M N : Λ V} {A : 𝕋}
                    → Γ ⊢ M ∶ A → M ⟶β N → Γ ⊢ N ∶ A
  -- SubReduction⊢ {V} {Γ} {M} {N} {A} (App {A = B} {N = P} d1 d2) (redexβ {s = G} refl)
  SubReduction⊢₁ (App (Abs d1) d2) (red⟶β (redex refl)) = SubLemma⊢ₒ d1 d2
  SubReduction⊢₁ (App d1 d2) (appL⟶β re) = App (SubReduction⊢₁ d1 re) d2
  SubReduction⊢₁ (App d1 d2) (appR⟶β re) = App d1 (SubReduction⊢₁ d2 re)
  SubReduction⊢₁ (Abs d0) (abs⟶β re) = Abs (SubReduction⊢₁ d0 re)

  SubReduction⊢ : ∀ {V : Set} {Γ : Cxt V} {M N : Λ V} {A : 𝕋} → Γ ⊢ M ∶ A → M ⟶β⋆ N → Γ ⊢ N ∶ A
  -- SubReduction⊢ d (ax⋆ M→N) = SubReduction⊢₁ d M→N
  SubReduction⊢ d ε⋆ = d
  SubReduction⊢ d (M→y ,⋆ y→⋆N) = SubReduction⊢ (SubReduction⊢₁ d M→y) y→⋆N

  CxtEqIrrel : ∀ {V} (Γ : Cxt V) (x : V) (A : 𝕋) (p1 p2 : Γ x ≡ A) → p1 ≡ p2
  CxtEqIrrel Γ x .(Γ x) refl refl = refl

  inv⇒L : ∀ {A1 A2 B1 B2 : 𝕋} → (A1 ⇒ A2) ≡ (B1 ⇒ B2) → A1 ≡ B1
  inv⇒L refl = refl

  inv⇒R : ∀ {A1 A2 B1 B2 : 𝕋} → (A1 ⇒ A2) ≡ (B1 ⇒ B2) → A2 ≡ B2
  inv⇒R refl = refl

  appNF⊢unique : ∀ {V} {Γ : Cxt V} (s t : Λ V) → app s t ∈ NF
                   → ∀ {A B : 𝕋} → Γ ⊢ app s t ∶ A → Γ ⊢ app s t ∶ B → A ≡ B
  appNF⊢unique (var x) t st∈NF (App (Var .x e1) T1) (App (Var .x e2) T2) = inv⇒R (e1 ~! e2)
  appNF⊢unique (app s1 s2) t st∈NF (App S1 S2) (App T1 T2)
    = inv⇒R (appNF⊢unique s1 s2 (appNFinvL st∈NF ) S1 T1)
  appNF⊢unique (abs s0)    t st∈NF S T = ∅ (st∈NF (s0 [ t ]ₒ) (red⟶β (redex refl) ) )

  unique⊢NF : ∀ {V} {Γ : Cxt V} {A : 𝕋} {M : Λ V} → M ∈ NF
                → ∀ (d1 d2 : Γ ⊢ M ∶ A) → d1 ≡ d2
  unique⊢NF {Γ = Γ} {A} {var x} M∈NF (Var .x g1) (Var .x g2) = cong (Var x) (CxtEqIrrel Γ x A g1 g2)
  unique⊢NF {A = A1 ⇒ A2} {abs M0} M∈NF (Abs d1) (Abs d2) = cong Abs (unique⊢NF (absNFinv M∈NF) d1 d2)
  unique⊢NF {V} {Γ} {A} {app (var x) M2} M∈NF (App (Var .x e1) d1) (App (Var .x e2) d2)
    with inv⇒L (e1 ~! e2)
  ... | e rewrite e = cong2 App (cong (Var x) (CxtEqIrrel Γ x _ e1 e2) )
                                (unique⊢NF (appNFinvR M∈NF) d1 d2)
  unique⊢NF {A = A} {app (app M1 M3) M2} M∈NF (App d1 d2) (App d3 d4)
    with inv⇒L (appNF⊢unique M1 M3 (appNFinvL M∈NF) d1 d3)
  ... | e rewrite e = cong2 App (unique⊢NF {M = app M1 M3} (appNFinvL M∈NF) d1 d3)
                                (unique⊢NF {M = M2}        (appNFinvR M∈NF) d2 d4)
  unique⊢NF {A = A} {app (abs M1) M2} M∈NF (App d1 d2) (App d3 d4)
    = ∅ (M∈NF (M1 [ M2 ]ₒ) (red⟶β (redex refl) ) )

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

  unique⊢dB : ∀ {V} {Γ : Cxt V} {A B : 𝕋} {M : ΛdB V} → Γ ⊢dB M ∶ A → Γ ⊢dB M ∶ B → A ≡ B
  unique⊢dB {V} {Γ} {A} {B} {vardB x} (VardB e1) (VardB e2) = e1 ~! e2
  unique⊢dB {V} {Γ} {A} {B} {appdB M1 M2} (AppdB d1 d2) (AppdB d3 d4) with unique⊢dB d1 d3
  ... | refl = refl
  unique⊢dB {V} {Γ} {(A1 ⇒ B1)} {(A2 ⇒ B2)} {absdB C M0} (AbsdB d1) (AbsdB d2)
    = cong (_⇒_ A1) (unique⊢dB d1 d2)

open DeBruijn

module Church where
  data ΛCh {V : Set} : (Cxt V) → 𝕋 → Set where
    varCh : ∀ {Γ} {A} x   → Γ x ≡ A                 → ΛCh Γ A
    appCh : ∀ {Γ} {A B}   → ΛCh Γ (A ⇒ B) → ΛCh Γ A → ΛCh Γ B
    absCh : ∀ {Γ} {A B}   → ΛCh (io Γ A) (B)        → ΛCh Γ (A ⇒ B)

  erase1 : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → ΛdB V
  erase1         (varCh x Γx≡A) = vardB x
  erase1         (appCh M1 M2)  = appdB (erase1 M1) (erase1 M2)
  erase1 {A = A ⇒ B} (absCh M0) = absdB A (erase1 M0)

  erase2 : ∀ {V : Set} → ΛdB V → Λ V
  erase2 {V} (vardB x)     = var x
  erase2 {V} (appdB M1 M2) = app (erase2 {V} M1) (erase2 {V} M2)
  erase2 {V} (absdB x M0)  = abs (erase2 {↑ V} M0)

  erase : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} → ΛCh Γ A → Λ V
  erase = erase2 ∘ erase1

  prop1B19i : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : ΛCh Γ A) → Γ ⊢ erase M ∶ A
  prop1B19i (varCh x Γx≡A) = Var x Γx≡A
  prop1B19i (appCh M1 M2)  = App (prop1B19i M1) (prop1B19i M2)
  prop1B19i (absCh M0)     = Abs (prop1B19i M0)

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

  embellish : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) → Γ ⊢ M ∶ A → ΛCh Γ A
  embellish M d = embellishdB→Ch (embellishCu→dB M d ) (embellishCu→dB⊢ M d)

  prop1B19ii : ∀ {V : Set} {Γ : Cxt V} {A : 𝕋} (M : Λ V) (d : Γ ⊢ M ∶ A)
               → erase (embellish M d) ≡ M
  prop1B19ii (var x)     (Var _ _)   = refl
  prop1B19ii (app M1 M2) (App d1 d2) = cong2 app (prop1B19ii M1 d1) (prop1B19ii M2 d2)
  prop1B19ii (abs M0)    (Abs d0)    = cong abs  (prop1B19ii M0 d0)

  ΛCh→≅ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) (Δ : Cxt V)
            → Δ ≅ Γ ∘ f → ΛCh Δ A → ΛCh Γ A
  ΛCh→≅ f Δ Δ=Γf (varCh x e)   = varCh (f x) (Δ=Γf x ~! e )
  ΛCh→≅ f Δ Δ=Γf (appCh d1 d2) = appCh (ΛCh→≅ f Δ Δ=Γf d1) (ΛCh→≅ f Δ Δ=Γf d2)
  ΛCh→≅ f Δ Δ=Γf (absCh d0)    = absCh (ΛCh→≅ (↑→ f) (io Δ _) cxt≅ d0) where
    cxt≅ : _
    cxt≅ (i x) = Δ=Γf  x
    cxt≅ o     = refl

  ΛCh≅ : ∀ {V : Set} {Γ Δ : Cxt V} {A : 𝕋} → Γ ≅ Δ → ΛCh Γ A → ΛCh Δ A
  ΛCh≅ {V} {Γ} {Δ} {A} g=d m = ΛCh→≅ {V} {V} {Δ} {A} I Γ (λ x → g=d x) m

  erase→≅ : ∀ {V W : Set} {Γ : Cxt W} {A : 𝕋} (f : V → W) (Δ : Cxt V)
            → (gd : Δ ≅ Γ ∘ f) (M : ΛCh Δ A) → Λ→ f (erase M) ≡ erase (ΛCh→≅ {Γ = Γ} f Δ gd M)
  erase→≅ f Δ gd (varCh x Γx=A) = refl
  erase→≅ f Δ gd (appCh M1 M2) = cong2 app (erase→≅ f Δ gd M1) (erase→≅ f Δ gd M2)
  erase→≅ {Γ = Γ} {A ⇒ B} f Δ gd (absCh M0) = cong abs (erase→≅ (↑→ f) (io Δ _ ) h M0) where
    h : io Δ A ≅ io Γ A ∘ ↑→ f
    h x = _ -- TypedLambda.Church.cxt≅ f Δ gd M0

  erase≅ : ∀ {V : Set} {Γ Δ : Cxt V} {A : 𝕋} (gd : Γ ≅ Δ)
              → ∀ (M : ΛCh Γ A) → erase M ≡ erase (ΛCh≅ gd M)
  erase≅ {Γ = Γ} gd M = Λ→≅I !≅! (erase M) ~! erase→≅ I Γ gd M

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

  NFCh : ∀ (V : Set) (Γ : Cxt V) (A : 𝕋) → 𝓟 (ΛCh Γ A)
  NFCh V Γ A M = ∀ N → ¬ (erase M ⟶β erase {V} {Γ} {A} N)

  absChInv : ∀ {V} {Γ : Cxt V} {A B : 𝕋} (N1 N2 : ΛCh (io Γ A) B) → absCh N1 ≡ absCh N2 → N1 ≡ N2
  absChInv N1 .N1 refl = refl

  erase1type : ∀ {V : Set} {Γ : Cxt V} (A : 𝕋) (M : ΛCh Γ A) → Γ ⊢dB erase1 M ∶ A
  erase1type A (varCh x x∶A) = VardB x∶A
  erase1type A (appCh {A = B} M1 M2) = AppdB (erase1type (B ⇒ A) M1 ) (erase1type B M2)
  erase1type (A1 ⇒ A2) (absCh M0) = AbsdB (erase1type A2 M0)

  erase2type : ∀ {V : Set} {Γ : Cxt V} {M : ΛdB V} {A : 𝕋} → Γ ⊢dB M ∶ A → Γ ⊢ erase2 M ∶ A
  erase2type (VardB x) = Var _ x
  erase2type (AppdB d1 d2) = App (erase2type d1) (erase2type d2)
  erase2type (AbsdB d0) = Abs (erase2type d0)

  -- -- Outside NFs, this is simply false
  -- erase2unique : ∀ {V : Set} {Γ : Cxt V} {M : ΛdB V} {A B : 𝕋} → Γ ⊢dB M ∶ A → Γ ⊢ erase2 M ∶ B → A ≡ B
  -- erase2unique {M = vardB x} {A} {B} (VardB e1) (Var .x e2) = e1 ~! e2
  -- erase2unique {M = absdB .A1 M} {A1 ⇒ B1} {A2 ⇒ B2} (AbsdB db) (Abs cu)
  --   = {!   !}
  -- erase2unique {M = appdB M1 M2} {A} {B} (AppdB db1 db2) (App cu1 cu2)
  --   = inv⇒R (erase2unique {M = M1} db1 cu1)

  Prop1B24-Lemma1 : ∀ {V : Set} {Γ : Cxt V} (M : ΛdB V)
        → ∀ (A : 𝕋) (d : Γ ⊢dB M ∶ A) → ∀ (N : ΛCh Γ A) → erase1 {V} N ≡ M → N ≡ embellishdB→Ch {V} {Γ} M d
  Prop1B24-Lemma1 {V} {Γ} (vardB x) A (VardB x∶A1) (varCh .x x∶A2) refl
    rewrite CxtEqIrrel Γ x A x∶A1 x∶A2 = refl
  Prop1B24-Lemma1 {V} {Γ} .(erase1 (absCh N)) (A1 ⇒ A2) (AbsdB d) (absCh N) refl
    = cong absCh (Prop1B24-Lemma1 (erase1 {↑ V} {io Γ A1} {A2} N) A2 d N refl)
  Prop1B24-Lemma1 {V} {Γ} .(erase1 (appCh N1 N2)) B (AppdB d1 d2) (appCh {A = A} N1 N2) refl
    with unique⊢dB d2 (erase1type A N2)
  ... | e rewrite e = cong2 appCh n1 n2 where
    n1 = Prop1B24-Lemma1 (erase1 N1) (A ⇒ B) d1 N1 refl
    n2 = Prop1B24-Lemma1 (erase1 N2)  A      d2 N2 refl

  Prop1B24 : ∀ {V : Set} {Γ : Cxt V} (A : 𝕋) (M : Λ V) → M ∈ NF
                → (d : Γ ⊢ M ∶ A) → ∀ (N : ΛCh Γ A) → erase N ≡ M → N ≡ embellish M d
  Prop1B24 {V} {Γ} A (var x) M∈NF (Var .x Γx=A) (varCh .x Γy=A) refl
    = cong (varCh x) (CxtEqIrrel Γ x A Γy=A Γx=A )
  Prop1B24 (A ⇒ B) (abs M0) M∈NF (Abs d) (absCh N) eN=M = cong absCh c where
    b = λ M' M0→M' → M∈NF (abs M') (abs⟶β M0→M')
    c = Prop1B24 B M0 b d N (absInv eN=M)
  Prop1B24 {V} {Γ} B (app .(erase N1) .(erase N2)) eN1N2∈NF (App {.Γ} {A1} {.B} d1 d2) (appCh {.Γ} {A2} {.B} N1 N2) refl
    with N1 | d1
  ... | appCh s1 s2 | d0 with inv⇒L (appNF⊢unique (erase s1) (erase s2) (appNFinvL eN1N2∈NF) d0
                                      (erase2type (erase1type (A2 ⇒ B) (appCh s1 s2))) )
  ... | e rewrite e = cong2 appCh ((Prop1B24 (A2 ⇒ B) (erase (appCh s1 s2)) (appNFinvL eN1N2∈NF)  d0 (appCh s1 s2) refl))
                                  (Prop1B24 A2  (erase N2) (appNFinvR eN1N2∈NF) d2 N2 refl )
  Prop1B24 {V} {Γ} B (app .(erase N1) .(erase N2)) eN1N2∈NF (App {.Γ} {A1} {.B} d1 d2) (appCh {.Γ} {A2} {.B} N1 N2) refl
    | absCh s0    | d0 = ∅ (eN1N2∈NF (erase2 (erase1 s0) [ io var (erase2 (erase1 N2)) ]) (red⟶β (redex refl) ) )
  Prop1B24 {V} {Γ} B (app .(erase N1) .(erase N2)) eN1N2∈NF (App {.Γ} {A1} {.B} d1 d2) (appCh {.Γ} {A2} {.B} N1 N2) refl
    | varCh x g | Var .x g2 with inv⇒L (g2 ~! g)
  ... | e rewrite e = cong2 appCh (cong (varCh x) (CxtEqIrrel Γ x (A2 ⇒ B) g g2) )
            (Prop1B24 A2 (erase2 (erase1 N2)) (λ N z → eN1N2∈NF (app (var x) N) (appR⟶β z)) d2 N2 refl )

  emptyLemma : ∀ {X : Set} (Γ : ⊥ → X) → Γ ≅ ∅
  emptyLemma Γ = λ x → ∅ x

  emptyCxtLemma : ∀ {Γ Δ : Cxt ⊥} → Γ ≅ Δ
  emptyCxtLemma {Γ} {Δ} = emptyLemma Γ ≅!~ emptyLemma Δ

  -- should probably change NF to NFCh here (not working with ∈)
  -- problem: M and N might have ``different'' contexts,
  -- even though we know they are the same (≅-equal)
  -- eraseM2∈NF : ∀ {V : Set} {Γ : Cxt V} (A) (M1 M2 : ΛCh Γ A) → erase (appCh _ M2) ∈ NF → erase M2 ∈ NF
  -- eraseM2∈NF = {!   !}

  Prop1B25 : ∀ {Γ : Cxt ⊥} (A : 𝕋) (M : ΛCh Γ A) (N : Λ ⊥)
                → erase M ∈ NF → (d : ∅ ⊢ N ∶ A) → erase M ≡ N
                → ΛCh≅ (emptyLemma Γ) M ≡ embellish N d
  Prop1B25 {Γ} A M N M∈NF d eM=N = Prop1B24 A N g1 d (ΛCh→≅ (λ z → z) Γ (λ x → ∅ x) M) g2
    where g1 = transp NF eM=N M∈NF
          g2 = ~ (erase≅ (λ x → ∅ x) M)  ! eM=N

  -- -- should probably change NF to NFCh here (not working with ∈)
  -- Prop1B25 : ∀ {V : Set} {Γ : Cxt V} (A : 𝕋) (M : ΛCh Γ A)
  --             → erase M ∈ NF → (Γ ⊢ erase M ∶ A)
  -- Prop1B25 A (varCh x Γx=A) nf = Var x Γx=A
  -- Prop1B25 A (appCh M1 M2) nf = App (Prop1B25 _ M1 eraseM1∈NF) (Prop1B25 _ M2 {!   !})
  --     where eraseM1∈NF = λ { X M2betaX → nf X {!   !} }
  --           -- eraseM2∈NF = {!   !}
  -- Prop1B25 (A ⇒ B) (absCh M0) nf = Abs (Prop1B25 B M0 eraseM0∈NF)
  --     where eraseM0∈NF = λ ↑X M0betaX → nf (abs ↑X) (absβ M0betaX)

  -- data _⊢_∶_ {V : Set} : Cxt V → Λ V → 𝕋 → Set where
  --   Var : ∀ {Γ : Cxt V} {x : V} {A : 𝕋} → Γ x ≡ A → Γ ⊢ var x ∶ A
  --   App : ∀ {Γ : Cxt V} {M N : Λ V} {A B : 𝕋}
  --           → Γ ⊢ M ∶ (A ⇒ B)  →  Γ ⊢ N ∶ A  →  Γ ⊢ app M N ∶ B
  --   Abs : ∀ {Γ : Cxt V} {M : Λ (↑ V)} {A B : 𝕋}
  --           → io Γ A ⊢ M ∶ B  →  Γ ⊢ abs M ∶ (A ⇒ B)
