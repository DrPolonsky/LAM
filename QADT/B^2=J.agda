open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment

module QADT.B^2=J where

b : ADT 1
b = 1+ (𝕧₀ ²)

B : ADT 0
B = μ b

j : ADT 1
j = 𝟏 ⊔ (𝕍 o) ⊔ (𝕍 o) ⊔ (𝕍 o) ²

J : ADT 0
J = μ j

B² = B ²

B²=J : Iso (j [ B² ]) B²
B²=J = {!    !} 
