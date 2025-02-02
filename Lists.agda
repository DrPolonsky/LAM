open import Logic
open import Predicates
open import Datatypes

module Lists where

List∀ : ∀ {A : Set} → 𝓟 A → 𝓟 (List A)
List∀ P [] = ⊤
List∀ P (x ∷ xs) = P x × List∀ P xs

List∃ : ∀ {A : Set} → 𝓟 A → 𝓟 (List A)
List∃ P [] = ⊥
List∃ P (x ∷ xs) = P x ⊔ List∃ P xs

_∈List_ : ∀ {A : Set} → A → List A → Set
x ∈List ys = List∃ (λ y → x ≡ y) ys

List∃elim : ∀ {A : Set} (P : 𝓟 A) (xs : List A) → List∃ P xs →
              Σ[ y ∈ A ] (y ∈List xs × P y)
List∃elim P (x ∷ xs) (in1 px) = (x ,, (in1 refl) , px )
List∃elim P (x ∷ xs) (in2 lPxs) with List∃elim P xs lPxs
... | (y ,, y∈xs , Py) = (y ,, (in2 y∈xs ) , Py )

All∈List : ∀ {A : Set} (P : 𝓟 A) {x} {xs} → x ∈List xs → List∀ P xs → P x
All∈List P {x} {y ∷ xs} (in1 x=y)  (Py , allPxs) = transp P (~ x=y) Py
All∈List P {x} {y ∷ xs} (in2 x∈xs) (Py , allPxs) = All∈List P x∈xs allPxs



ListDNS : ∀ {A : Set} (P : 𝓟 A) → ∀ xs → List∀ (∁ (∁ P)) xs → ¬¬ (List∀ P xs)
ListDNS P [] all¬¬P ¬allP = ¬allP all¬¬P
ListDNS P (x ∷ xs) (¬¬Px , all¬¬Pxs) ¬allP
        = ¬¬Px (λ px → ListDNS P xs all¬¬Pxs (λ allPxs → ¬allP (px , allPxs)))
