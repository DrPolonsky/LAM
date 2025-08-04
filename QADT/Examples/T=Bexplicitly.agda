open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.T=Bexplicitly where

-- The explicitly defined version
data BT : Set where
  BTleaf : BT
  BTnode : BT → BT → BT

data TT' : Set where
  TT'leaf : TT'
  TUnode : TT' → TT'
  TT'node : TT' → TT' → TT' → TT'

BT→TT' : BT → TT'
BT→TT' BTleaf = TT'leaf
BT→TT' (BTnode bt1 BTleaf) = TUnode (BT→TT' bt1)
BT→TT' (BTnode bt1 (BTnode bt2 bt3)) = TT'node (BT→TT' bt1) (BT→TT' bt2) (BT→TT' bt3)

TT'→BT : TT' → BT
TT'→BT TT'leaf = BTleaf
TT'→BT (TUnode t) = BTnode (TT'→BT t) BTleaf
TT'→BT (TT'node t1 t2 t3) = BTnode (TT'→BT t1) (BTnode (TT'→BT t2) (TT'→BT t3) )

BT→TT'→BT : ∀ b → TT'→BT (BT→TT' b) ≡ b
BT→TT'→BT BTleaf = refl
BT→TT'→BT (BTnode b1 BTleaf) = cong (λ x → BTnode x BTleaf) (BT→TT'→BT b1)
BT→TT'→BT (BTnode b1 (BTnode b2 b3)) = cong3 (λ x y z → BTnode x (BTnode y z)) (BT→TT'→BT b1) (BT→TT'→BT b2) (BT→TT'→BT b3)

TT'→BT→TT' : ∀ t → BT→TT' (TT'→BT t) ≡ t
TT'→BT→TT' TT'leaf = refl
TT'→BT→TT' (TUnode t) = cong TUnode (TT'→BT→TT' t)
TT'→BT→TT' (TT'node t1 t2 t3) = cong3 TT'node (TT'→BT→TT' t1) (TT'→BT→TT' t2) (TT'→BT→TT' t3)

-- Using the calculus of isomorphisms


t-func : Set → Set
t-func X = ⟦ t ⟧ (λ _ → X )

tB=B : Iso (subst t (B)) B
tB=B = ~~ (fix≃ b =!= += (×= (fix≃ b) =!= dl= (=+ i×r ) ) )

foldT : ∀ (X : Set) → (t-func X → X) → ⟦ T ⟧ Γ₀ → X
foldT X Xalg (lfp (in1 TT')) = Xalg (in1 TT')
foldT X Xalg (lfp (in2 (in1 x))) = Xalg (in2 (in1 (foldT X Xalg x ) ) )
foldT X Xalg (lfp (in2 (in2 (x1 , (x2 , x3)))))
  = Xalg (in2 (in2 ((fT x1) , ((fT x2) , fT x3 ) ) ) ) where fT = foldT X Xalg
-- foldT X = fold {F = t-func} λ {A} {B} f → ⟦ t ⟧→ {!   !}

T→B : ⟦ T ⟧ Γ₀  → ⟦ B ⟧ Γ₀
T→B = foldADT t (λ ()) (⟦ B ⟧ Γ₀) ((_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ )))
