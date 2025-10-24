open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

module QADT.Examples.S^3=S where

Sⁿlemma : ∀ (n : ℕ) → Iso (Pow S (succ (succ n))) (Pow S (succ (succ n)) ⊔ Pow S (succ n) ⊔ Pow S n)
Sⁿlemma n = =× (fix≃ s) =!= (distrR≃ =!= (+= (i×l= (=× (fix≃ s) =!= distrR≃)) =!= (+= (+= i×l ) =!= (a+ ~!= ~~ (a+ ~!= =+ (~~ (cong+= (=× (dr= (cong+= i×l {!   !} {!   !}) ) ) {!   !} {!   !}) ) ) ) ) ) )

s[S³]=S³ : Iso (subst s (S ³)) (S ³)
s[S³]=S³ = {!   !}
