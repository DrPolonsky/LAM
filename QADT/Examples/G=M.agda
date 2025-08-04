open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.G=M where

gM : ADT ⊥
gM = subst g (M)

gM=M : Iso gM M
-- gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r ) !! )) =!= a+= (+= e ) ) ) )
gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= !! ar i+r) !! )) =!= a+= (+= e ) ) ) )
  where  e = dist3 ~!= ×= (~~ (fix≃ m ) )

G→M : ⟦ G ⟧ Γ₀  → ⟦ M ⟧ Γ₀
G→M = RigFold g M gM=M

findm : MM → ℕ → 𝔹
findm m n = elem ==M m (List→ G→M (allG n))

cn : ∀ {A : Set} → ℕ → (A → A) → A → A
cn {A} zero f x = x
cn {A} (succ n) f x = f (cn n f x)

bigM : MM
bigM = cn 7 (Mbnode Mleaf) Mleaf

-- take 100 (allM 4) works
-- take 100 (allM 5) works
20ms : List MM
20ms = take 20 (allM 6)

passNm : ℕ → List MM
passNm zero = 20ms
passNm (succ n) = filter (λ x → findm x (succ n)) (passNm n)

-- why does it stop at a number? agda limitation? or the way allM is generated?
-- test = {! length (filter (λ {(x , y) → ==M x y})  (zip (take 1000000 (allM 5)) (take 1000000 (allM 6))))  !}

h : ⟦ G ⟧ Γ₀ → ⟦ M ⟧ Γ₀
h x = fold {λ X → ⟦ g ⟧ (Γ₀ ⅋o:= X)} (λ j →  ⟦ g ⟧→ (λ tt → j)) (_≃_.f+ (≃⟦ gM=M ⟧ Γ₀ ) ) x
