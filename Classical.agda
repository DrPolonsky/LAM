module Classical where

open import Logic

-- Classical Principles
EM : Set → Set
EM A = A ⊔ ¬ A

WEM : Set → Set
WEM A = ¬ A ⊔ ¬¬ A

DNE : Set → Set
DNE A = ¬¬ A → A

EM→WEM×DNE : ∀ A → EM A → WEM A × DNE A
EM→WEM×DNE = {!   !}
WEM×DNE→EM : ∀ A → WEM A → DNE A → EM A
WEM×DNE→EM = {!   !}
