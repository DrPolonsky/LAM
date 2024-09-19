module Relations.Terese-1-3 where

open import Logic
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators
open import Relations.ARS

-- Hint: Use 1.1.10(v)
1-3-4 : ∀ {A : Set} {I : Set} {R : I → 𝓡 A} → (∀ α β → commute (R α) (R β)) → CR (⋃₂ R)
1-3-4 {A} {I} {R} commR peak@(a ,, ε⋆ , ⋃R*ac) = {!   !}
1-3-4 {A} {I} {R} commR peak@(a ,, (⋃Rab₀ ,⋆ ⋃R*b₀b) , ⋃R*ac) = Proposition-1-1-10.v→i (λ b c (a ,, Rab , R*ac) → f b c a Rab R*ac) peak  where
    f = {!   !}