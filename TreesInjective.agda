module TreesInjective where

open import Logic
open import Predicates

data T : Set where
  leaf : T
  node : T → T → T

foldT : ∀ {X : Set} → X → (X → X → X) → T → X
foldT l n leaf = l
foldT l n (node t1 t2) = n (foldT l n t1) (foldT l n t2)

nodeInj : ∀ {X : Set} → 𝓟 (X → X → X)
nodeInj n = ∀ {x1 x2 y1 y2} → n x1 y1 ≡ n x2 y2 → (x1 ≡ x2) × (y1 ≡ y2)

node≠leaf : ∀ {X : Set} → X → (X → X → X) → Set
node≠leaf l n = ∀ x1 x2 → ¬ (l ≡ n x1 x2)

foldInj : ∀ {X : Set} → X → (X → X → X) → Set
foldInj l n = ∀ t1 t2 → foldT l n t1 ≡ foldT l n t2 → t1 ≡ t2

nodeInj→foldInj : ∀ {X} (l : X) (n : X → X → X) → nodeInj n → node≠leaf l n → foldInj l n
nodeInj→foldInj l n nInj n≠l leaf leaf ft1=ft2 = refl
nodeInj→foldInj l n nInj n≠l leaf (node t2 t3) ft1=ft2 = ∅ (n≠l ((foldT l n t2)) ((foldT l n t3))  ft1=ft2)
nodeInj→foldInj l n nInj n≠l (node t1 t3) leaf ft1=ft2 = ∅ (n≠l ((foldT l n t1)) ((foldT l n t3)) (~ ft1=ft2 ) )
nodeInj→foldInj l n nInj n≠l (node t1 t3) (node t2 t4) ft1=ft2
  with nodeInj→foldInj l n nInj n≠l t1 t2 | nodeInj→foldInj l n nInj n≠l t3 t4
... | c1 | c2 with nInj ft1=ft2
... | d1 , d2 = cong2 node (c1 d1) (c2 d2) 
