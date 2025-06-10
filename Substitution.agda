module Substitution where

open import Logic
open import Lifting
open import Lambda

-- lift≅ : ∀ {A B : Set} {f g : A → Λ B} → f ≅ g → lift f ≅ lift g
-- lift≅ f≅g (i x) = cong Λ→i (f≅g x)
-- lift≅ f≅g o = refl

-- bind≅ : ∀ {A B : Set} {f g : A → Λ B} → f ≅ g → ∀ t → t [ f ] ≡ t [ g ]
-- bind≅ f≅g (var x) = f≅g x
-- bind≅ f≅g (app t1 t2) = cong2 app (bind≅ f≅g t1) (bind≅ f≅g t2)
-- bind≅ f≅g (abs t) = cong abs (bind≅ (lift≅ f≅g ) t)

-- bind : ∀ {A B : Set} → (A → Λ B) → Λ A → Λ B
-- bind f t = t [ f ]

bindLaw≅ : ∀ {A B C : Set} {f : A → Λ B} {g : B → Λ C} {h : A → Λ C}
          → (bind g ∘ f) ≅ h → (bind g ∘ bind f) ≅ bind h
bindLaw≅ fgh (var x) = fgh x
bindLaw≅ fgh (app t1 t2) = cong2 app (bindLaw≅ fgh t1) (bindLaw≅ fgh t2)
bindLaw≅ {f = f} {g} {h} fgh (abs t0) = cong abs (bindLaw≅ aux t0)
  where aux : bind (lift g) ∘ lift f ≅ lift h
        aux (i x) = ~ {!   !}
        aux o = refl
