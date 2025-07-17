
open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.ExampleADTs

module QADT.SimpleNonIsoFold where

M=2M : Iso M (subst 2m M)
M=2M = fix≃ m =!= += (=+ (fix≃ m) =!= a+= (~~ (a+= (+= (a+= (~~ (a+= (+= c+ ) ) ) ) ) ) ) )

M=M : Iso M (subst m M)
M=M = fix≃ m =!= += (=+ (fix≃ m) =!= (a+= (+= (a+= (+= c+ ) ) =!= ((a+ ~!= (a+ ~!= (=+ (a+=  (~~ (fix≃ m) ) )) ) ) ) ) ) )

2M→M : ⟦ 2M ⟧ Γ₀ → MM
2M→M = RigFold 2m M (~~ M=2M)

M→M : MM → MM
M→M = RigFold m M (~~ M=M)

findm : MM → ℕ → 𝔹
findm mm n = elem ==M mm (List→ 2M→M (all2M n))

findmm : MM → ℕ → 𝔹
findmm mm n = elem ==M mm (List→ M→M (allM n))

some_m : List MM
some_m = take 100 (allM 10)

passN : ℕ → List MM
passN zero = some_m
passN (succ n) = filter (λ x → findm x (succ n)) (passN n)

passNm : ℕ → List MM
passNm zero = some_m
passNm (succ n) = filter (λ x → findmm x (succ n)) (passNm n)

notPassm : ℕ → List MM
notPassm zero = some_m
notPassm (succ n) = filter (λ x → not (findmm x (succ n))) some_m


test : Set
test = {!   List→ M→𝕄 (passNm 4)  !}


-- reconcile the following -- is pattern matching not deep enough?
test2 : Set
test2 = {! M→𝕄 (M→M (𝕄→M (mu (mb ml ml)))) !}

test3 : Set
test3 = {! (_≃_.f+ (≃⟦ M=M ⟧ Γ₀) (𝕄→M (mu (mb ml ml))))  !}
