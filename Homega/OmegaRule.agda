{-# OPTIONS --guardedness #-}
module Homega.OmegaRule where

open import Logic
open import Lifting
open import Lambda
open import Reduction
-- open import Relations

open import Predicates
open import Relations.Core

open import Homega.Unsolvable
open import Homega.LambdaH

ωΛRel : ΛRel → ΛRel
ωΛRel R {X} s t = ∀ (ξ : X → Λ⁰) → R (s [ ξ ]) (t [ ξ ])

_⊆ΛRel_ : ΛRel → ΛRel → Set₁
R1 ⊆ΛRel R2 = ∀ {X} → R1 {X} ⊆ R2 {X}

module LambdaCongruences (R : ΛRel) where

  isΛEquivalence : Set₁
  isΛEquivalence = ∀ {X} → isEquivalence (R {X})

  record isΛCongruence : Set₁ where
    constructor ΛCong
    field
      varR : ∀ {X} (x : X) → R (var x) (var x)
      appR : ∀ {X} {s1 s2 t1 t2 : Λ X} → R s1 t1 → R s2 t2 → R (app s1 s2) (app t1 t2)
      absR : ∀ {X} {r1 r2 : Λ (↑ X)} → R r1 r2 → R (abs r1) (abs r2)

  isωCongruence : Set₁
  isωCongruence = ∀ {X} → ωΛRel R {X} ⊆ R {X}

  record isωTheory : Set₁ where
    field
      isΛEq   : isΛEquivalence
      isΛCong : isΛCongruence
      isωCong : isωCongruence

  data ωTh {X : Set} : Λ X → Λ X → Set where
    axω  : ∀ {s t : Λ X} → R s t → ωTh s t
    varω : ∀ {x : X} → ωTh (var x) (var x)
    appω : ∀ {s1 s2 t1 t2 : Λ X} → ωTh s1 s2 → ωTh t1 t2 → ωTh (app s1 t1) (app s2 t2)
    absω : ∀ {r1 r2 : Λ (↑ X)} → ωTh r1 r2 → ωTh (abs r1) (abs r2)
    _!ωTh_  : ∀ {s t u : Λ X} → ωTh s t → ωTh t u → ωTh s u
    _~!ωTh_ : ∀ {s t u : Λ X} → ωTh t s → ωTh t u → ωTh s u
    ω-rule  : ∀ {s t : Λ X}   → ωΛRel ωTh s t → ωTh s t

  reflωTh : ∀ {X} → reflR (ωTh {X})
  reflωTh (var x) = varω
  reflωTh (app s t) = appω (reflωTh s) (reflωTh t)
  reflωTh (abs r) = absω (reflωTh r)

  symmωTh : ∀ {X} → symmR (ωTh {X})
  symmωTh {X} {s} {t} (axω x) = axω x ~!ωTh reflωTh s
  symmωTh {X} {.(var _)} {.(var _)} varω = varω
  symmωTh {X} {.(app _ _)} {.(app _ _)} (appω st st₁) = appω (symmωTh st) (symmωTh st₁)
  symmωTh {X} {.(abs _)} {.(abs _)} (absω st) = absω (symmωTh st)
  symmωTh {X} {s} {t} (st !ωTh st₁) = symmωTh st₁ !ωTh symmωTh st
  symmωTh {X} {s} {t} (st ~!ωTh st₁) = symmωTh st₁ !ωTh st
  symmωTh {X} {s} {t} (ω-rule om) = ω-rule (λ ξ → symmωTh (om ξ ) )

  tranωTh : ∀ {X} → tranR (ωTh {X})
  tranωTh {X} r s t rs st = rs !ωTh st

open LambdaCongruences public

module UniversalProperty (R : ΛRel) where

  ωTh-isΛEquivalence : isΛEquivalence (ωTh R)
  ωTh-isΛEquivalence = record { isRefl = reflωTh R ; isSymm = symmωTh R ; isTran = tranωTh R }
  ωTh-isΛCongruence  : isΛCongruence  (ωTh R)
  ωTh-isΛCongruence  = record { varR = λ x → varω ; appR = appω ; absR = absω }
  ωTh-isωCongruence  : isωCongruence  (ωTh R)
  ωTh-isωCongruence s t s=ωt = ω-rule s=ωt

  ωTh-isωTheory : isωTheory (ωTh R)
  ωTh-isωTheory = record { isΛEq = ωTh-isΛEquivalence
                         ; isΛCong = ωTh-isΛCongruence
                         ; isωCong = ωTh-isωCongruence }

  -- For any Λ-relation R, ωTh(R) is the least Λ-theory containing R closed under the ω-rule
  ωThElim : ∀ (Q : ΛRel) → R ⊆ΛRel Q → isωTheory Q → ωTh R ⊆ΛRel Q
  ωThElim Q R⊆Q QTh@(record { isΛEq = isΛEq ; isΛCong = (ΛCong varR appR absR) ; isωCong = isωCong })
    {X} s t s=t with s=t
  ... | axω x = R⊆Q s t x
  ... | varω = varR _
  ... | appω c d = appR (ωThElim Q R⊆Q QTh _ _ c) (ωThElim Q R⊆Q QTh _ _ d)
  ... | absω c = absR (ωThElim Q R⊆Q QTh _ _ c)
  ... | c !ωTh  d = isTran (isΛEq) s _ t ((ωThElim Q R⊆Q QTh _ _ c)) ((ωThElim Q R⊆Q QTh _ _ d)) where open isEquivalence
  ... | c ~!ωTh  d = isTran (isΛEq) s _ t (isSymm isΛEq ((ωThElim Q R⊆Q QTh _ _ c)) )
                                          ((ωThElim Q R⊆Q QTh _ _ d)) where open isEquivalence
  ... | ω-rule om = isωCong s t (λ ξ → (ωThElim Q R⊆Q QTh _ _ (om ξ) ) )

open UniversalProperty public

-- -- First attempt
-- ωΛRel : ΛRel → ΛRel
-- ωΛRel R {X} s t = ∀ {φ1 φ2 : X → Λ ⊥} → (∀ x → R (φ1 x) (φ2 x)) → R (s [ φ1 ]) (t [ φ2 ])
--
-- -- The last rule is not monotone
-- data _=𝓗ω_ {X : Set} : Λ X → Λ X → Set where
--   =Ω⊆=𝓗ω : ∀ {s t : Λ X}   → s =Ω t              → s =𝓗ω t
--   sred𝓗ω : ∀ {s t u : Λ X} → s ⟶s t  → t =𝓗ω u → s =𝓗ω u
--   pred𝓗ω : ∀ {s t u : Λ X} → s =𝓗ω t → u ⇉ t    → s =𝓗ω u
--   om𝓗ω   : ∀ {s t : Λ X} → ωΛRel _=𝓗ω_ s t → s =𝓗ω t
