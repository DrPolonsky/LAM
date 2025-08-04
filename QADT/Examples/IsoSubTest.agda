open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

-- We want a convenient syntax for substituting isomorphisms inside of elements of Iso types

module QADT.Examples.IsoSubTest where

-- Q: Can we prove X = X² or is that not a rig iso?

∛1 : ADT ⊥
∛1 = μ ((1+ (𝕍 (o))) ²)

X : ADT ⊥
X = ∛1

skel : ADT (↑ ⊥)
skel = (1+ ((wk₀ X) × (𝕍 (o)))) ²

-- 1+X^2=1+X[1+X^2] : Iso (1+ (X ²)) (1+ (X × (1+ (X ²))))
-- 1+X^2=1+X[1+X^2] = subst≃ {0} {skel} {skel} {X} {1+ (X ²)} (refl≃ skel) (fix≃ ((1+ (𝕍 (o))) ²))

1+X²≃1+X[1+X²] : Iso (1+ (X ²)) (1+ (X × (1+ X ²)))
1+X²≃1+X[1+X²] = {!   !} -- subst≃ {0} {skel} {skel} {X} {1+ X ²} (refl≃ skel) (fix≃ ((1+ (𝕍 (o))) ²) )

X=1+X+X^2 : Iso X (1+ (X ⊔ (X ²)))
X=1+X+X^2 = fix≃ ((1+ (𝕍 (o))) ²) =!= {!   !}
