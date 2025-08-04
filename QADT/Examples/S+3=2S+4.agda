open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.S+3=2S+4 where

S+3=2S+4 : Iso (1+ 2+S) (2+S ⊔ 2+S)
S+3=2S+4 = += (+= (+= (fix≃ s) )) =!= ~~ (a+= (+= (a+= (+= (c+= (a+= (+= (c+= (a+ ~!= c+= e ) ) ) ) ) ) ) ) )
  where e = a+ ~!= =+ (~~ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r) !! ) ) )

3+S→ : ⟦ 1+ 2+S ⟧ Γ₀ → ⟦ 2+S ⊔ 2+S ⟧ Γ₀
3+S→ = _≃_.f+ (≃⟦ S+3=2S+4 ⟧ Γ₀)

some2+S : List (⟦ 1+ 2+S ⟧ Γ₀)
some2+S = in1 tt ∷ in2 (in1 tt) ∷ in2 (in2 (in1 tt)) ∷ List→ (in2 ∘ (in2 ∘ in2)) (allS 10)

find-the-y : List (⟦ 1+ 2+S ⟧ Γ₀)
find-the-y = filter p some2+S where
  p : ⟦ 1+ 2+S ⟧ Γ₀ → 𝔹
  p (in1 y) = false
  p (in2 y) = not (or (==2+S (3+S→ (in2 y)) (in1 y)) (==2+S (3+S→ (in2 y)) (in2 y)))

checky : Set
checky = {! find-the-y  !}
