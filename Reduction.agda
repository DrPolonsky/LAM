module Reduction where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import RelationsCore

-- Congruence Closure
data CC (R : ∀ {X : Set} → 𝓡 (Λ X)) {X : Set} : 𝓡 (Λ X) where
  axCC : ∀ {s t : Λ X} → R s t                            → CC R s t
  varCC : ∀ {x : X}                                       → CC R (var x) (var x)
  appCC : ∀ {s1 s2 t1 t2 : Λ X} → CC R s1 s2 → CC R t1 t2 → CC R (app s1 t1) (app s2 t2)
  absCC : ∀ {r1 r2 : Λ (↑ X)}   → CC R r1 r2              → CC R (abs r1) (abs r2)

data CxtC (R : ∀ {X : Set} → 𝓡 (Λ X)) {X : Set} : 𝓡 (Λ X) where
  axCxtC :  ∀ {s t : Λ X} → R s t       → CxtC R s t
  appLCxtC : ∀ {s1 s2 t} → CxtC R s1 s2 → CxtC R (app s1 t) (app s2 t)
  appRCxtC : ∀ {s t1 t2} → CxtC R t1 t2 → CxtC R (app s t1) (app s t2)
  absCxtC : ∀ {r1 r2}    → CxtC R r1 r2 → CxtC R (abs r1) (abs r2)

reflCC : ∀ (R : ∀ {X} → 𝓡 (Λ X)) {X : Set} → ∀ (t : Λ X) → CC R t t
reflCC R (var x) = varCC
reflCC R (app t1 t2) = appCC (reflCC R t1) (reflCC R t2)
reflCC R (abs t0) = absCC (reflCC R t0 )

data contrβ {X : Set} : Λ X → Λ X → Set where
  red : ∀ {r s t} → (s [ t ]ᵒ ≡ r) → contrβ (app (abs s) t) r

data _⇉_ {X : Set} : Λ X → Λ X → Set where
  red⇉ : ∀ {s1 s2 : Λ (↑ X)} {t1 t2 t3 : Λ X}
           → s1 ⇉ s2 → t1 ⇉ t2 → s2 [ t2 ]ᵒ ≡ t3 → (app (abs s1) t1) ⇉ t3
  CC⇉ : ∀ {s t : Λ X} → CC _⇉_ s t → s ⇉ t

IC : ∀ {X} → Λ X
IC = abs (var o )



II⇉I : ∀ {X} → app IC IC ⇉ IC {X}
II⇉I {X} = red⇉ {X} {var o} {var o} {IC} {IC} {IC} (CC⇉ varCC )
                (CC⇉ (reflCC _⇉_ (abs (var o)) ) )
                refl

src : Λ ⊥
src = app (abs (app (app (var o) (app IC IC)) (app IC (var o)) ) ) (app IC IC)
tgt : Λ ⊥
tgt = app (app IC IC) IC

src⇉tgt : src ⇉ tgt
src⇉tgt = red⇉ {s2 = app (app (var o) IC) (var o)} {t2 = IC}
            (CC⇉ (appCC {s1 = app (var o) (app IC IC)} {s2 = app (var o) IC}
                        {t1 = app IC (var o)} {t2 = var o}
                        (appCC varCC (axCC II⇉I ) ) (axCC (red⇉ (CC⇉ varCC) (CC⇉ varCC) refl) ) ) )
          II⇉I refl

oneStepBeta : ∀ {X : Set} → Λ X → Λ X → Set
oneStepBeta = CxtC contrβ

-- One-step reduction relation
data _⟶β_ {X : Set} : Λ X → Λ X → Set where
  redexβ : ∀ {r s t} → (s [ t ]ᵒ ≡ r) → app (abs s) t ⟶β r
  appLβ : ∀ {s1 s2 t} → s1 ⟶β s2 → app s1 t ⟶β app s2 t
  appRβ : ∀ {s t1 t2} → t1 ⟶β t2 → app s t1 ⟶β app s t2
  absβ : ∀ {r1 r2}    → r1 ⟶β r2 → abs r1   ⟶β abs r2


-- -- \*
-- data _⋆ {X : Set} (R : X → X → Set) : X → X → Set where
--   ε⋆ : ∀ {x} → (R ⋆) x x
--   _,⋆_ : ∀ {x y z} → R x y → (R ⋆) y z → (R ⋆) x z

_⟶⋆β_ : ∀ {X} → Λ X → Λ X → Set
_⟶⋆β_ = (_⟶β_) ⋆

-- IC : ∀ {X} → Λ X
-- IC = abs (var o )

II→I : ∀ {X} → app (IC {X}) IC ⟶β IC
II→I = redexβ refl

I[II]→⋆I : ∀ {X} → (_⟶β_ ⋆) (app (IC {X}) (app IC IC)) IC
I[II]→⋆I = (redexβ refl ) ,⋆ (II→I ,⋆ ε⋆ )
-- I[II]→⋆I = (appRβ II→I ) ,⋆ (II→I ,⋆ ε⋆ )

open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

FPT : ∀ {X} (F : Λ X) → Σ[ YF ∈ Λ X ] (YF ⟶⋆β app F YF)
FPT F =
  let W = abs (app (Λ→ i F) (app (var o) (var o)))
      WW→FWW : app W W ⟶⋆β app F (app W W)
      WW→FWW = (redexβ (cong2 app {!   !} refl ) ) ,⋆ ε⋆
   in (app W W ,, WW→FWW )








-- The end
