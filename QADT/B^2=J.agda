open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.ExampleADTs

module QADT.B^2=J where

j[c×B²] : Iso (subst j B²) (subst j B²)
j[c×B²] = substIso j c×

-- 1 + B² + B² + B⁴ = 1 + B² + (B² × 1) + B² × B² =
-- 1 + B² + B² × (1 + B²) = 1 + B² + B³ = B + B³ =
-- (B × 1) + (B × B²) = B × (1 + B²) = B²
--
jB²=B² : Iso (subst j B²) (B²)
jB²=B² = += (+= (=+ i×r ~!~ dl ) =!= (+= (×= (~~ (fix≃ b) ) ) =!= (+= a×) ) ) =!= (a+ ~!= (=+ (~~ (fix≃ b) =!~ i×r ) =!= (~~ dl =!= ×= (~~ (fix≃ b) ) )  ) )

-- 1 + B² + B² + B⁴ = 1 + B² + (B² × 1) + B² × B² =
-- 1 + B² + B² × (1 + B²) = 1 + B² + B³ = B + B³ =
-- (1 × B) + (B × B²) = (1 + B²) × B = B²
--
jB²=B²v2 : Iso (subst j B²) (B²)
jB²=B²v2 = a+ ~!= cong+= (~~ (fix≃ b) ) ((=+ (~~ i×r) =!~ dl) =!= ×= (~~ (fix≃ b) ) ) (=+ (~~ i×l) =!= ((dr ~!= =× (~~ (fix≃ b) ) ))  )

-- 1 + B² + B² + B⁴ ->  1 + c+(B² + B²) + B⁴ -> isov1
jB²=B²v3 : Iso (subst j B²) (B²)
jB²=B²v3 = += (a+ ~!= (=+ c+ =!= a+ )) =!= (+= (+= (=+ i×r ~!~ dl ) =!= (+= (×= (~~ (fix≃ b) ) ) =!= (+= a×) ) ) =!= (a+ ~!= (=+ (~~ (fix≃ b) =!~ i×r ) =!= (~~ dl =!= ×= (~~ (fix≃ b) ) )  ) ))

-- 1 + B² + B² + B⁴ ->  1 + c+(B² + B²) + B⁴ -> isov2
jB²=B²v4 : Iso (subst j B²) (B²)
jB²=B²v4 = += (a+ ~!= (=+ c+ =!= a+ )) =!= (a+ ~!= cong+= (~~ (fix≃ b) ) ((=+ (~~ i×r) =!~ dl) =!= ×= (~~ (fix≃ b) ) ) (=+ (~~ i×l) =!= ((dr ~!= =× (~~ (fix≃ b) ) ))  ))

J→B² : JJ → BB ∧ BB
J→B² = RigFold j B² jB²=B²

J→B²v2 : JJ → BB ∧ BB
J→B²v2 = RigFold j B² jB²=B²v2

J→B²v3 : JJ → BB ∧ BB
J→B²v3 = RigFold j B² jB²=B²v3

J→B²v4 : JJ → BB ∧ BB
J→B²v4 = RigFold j B² jB²=B²v4

==jB²=B² : Iso (subst j B²) (B²) → Iso (subst j B²) (B²) → ℕ → 𝔹
==jB²=B² i1 i2 n = all (λ {(b1 , b2) → ==ADT {B²} b1 b2 } ) (List→ (λ x → x , _≃_.f+ (≃⟦ i2 ⟧ Γ₀) (_≃_.f- (≃⟦ i1 ⟧ Γ₀) x) ) (allB² n))

J→B²isoList₀ : List (Iso (subst j B²) (B²))
J→B²isoList₀ = jB²=B² ∷ jB²=B²v2 ∷ jB²=B²v3 ∷ jB²=B²v4 ∷ []

J→B²isoList₁ : List (Iso (subst j B²) (B²))
J→B²isoList₁ = List→ (λ x → x =!= c× ) J→B²isoList₀

J→B²isoList₂ : List (Iso (subst j B²) (B²))
J→B²isoList₂ = List→ (λ x → j[c×B²] =!= x ) J→B²isoList₀

J→B²isoList₃ : List (Iso (subst j B²) (B²))
J→B²isoList₃ = List→ (λ x → j[c×B²] =!= x ) J→B²isoList₁

J→B²isoList : List (Iso (subst j B²) (B²))
J→B²isoList = (J→B²isoList₀ ++ J→B²isoList₁ ++ J→B²isoList₂ ++ J→B²isoList₃)

isoCheck : (Iso (subst j B²) (B²)) → List 𝔹
isoCheck i0 = List→ (λ i1 → ==jB²=B² i0 i1 3) J→B²isoList

what = {! List→ (λ l → length (filter I (isoCheck l))) J→B²isoList !}
-- what = {! length (allB² 3)  !}

J→B²funList : List (⟦ subst j B² ⟧ Γ₀ → ⟦ B² ⟧ Γ₀)
J→B²funList = List→ (λ f → _≃_.f+ (≃⟦ f ⟧ Γ₀)) J→B²isoList

testIso= : Set
testIso= = {! List→ (λ f → f (in2 (in1 (Bleaf , Bleaf) ) ) ) J→B²funList  !}
-- testIso= = List→ (λ f → f (in2 (in1 (Bleaf , Bleaf) ) ) ) J→B²funList


-- ------------------------------------------- Test α


testRig : Iso (subst j B²) (B²) → ℕ → 𝔹
testRig α n = all (λ { (x , y) → ==ADT { subst j B² } x y }) (List→ f (allB² n))
  where i1 = c× =!~ α
        i2 = α ~!= j[c×B²]
        f =  λ x → _≃_.f+ (≃⟦ i1 ⟧ Γ₀ ) x , _≃_.f+ (≃⟦ i2  ⟧ Γ₀ ) x

test' : Set
test' = {! testRig jB²=B²v4 2  !}

-- -------------------------------------------

findB² : ℕ → BB² → 𝔹
findB² n b² = elem (==ADT {B × B}) b² (List→ J→B² (allJ n) )

someB² : List (BB²)
someB² = take 40 (allB² 5)

pass : ℕ → List (BB²)
pass n = filter (findB² n) someB²

test : Set
test = {! pass 5 !}
