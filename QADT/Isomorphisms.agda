open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import QADT.Functions

module QADT.Isomorphisms where

record _≃_ (A B : Set) : Set where
  constructor iso
  field
    f+ : A → B
    f- : B → A
    f-+ : ∀ x → f- (f+ x) ≡ x
    f+- : ∀ y → f+ (f- y) ≡ y

infix 19 _≃_

and≡ : ∀ {A B : Set} {w x : A} {y z : B} → w ≡ x → y ≡ z → (w , y) ≡ (x , z)
and≡ {A} {B} {w} {.w} {y} {.y} (refl ) (refl ) = refl

-- cong, : ...
-- cong, = cong2 _,_

iso∧ : ∀ {A1 A2 B1 B2} → (A1 ≃ A2) → (B1 ≃ B2) → (A1 ∧ B1) ≃ (A2 ∧ B2)
iso∧ {A1} {A2} {B1} {B2} (iso f+ f- f-+ f+-) (iso g+ g- g-+ g+-)
  = iso fg+ fg- fg-+ fg+- where
    fg+ : (A1 ∧ B1 → A2 ∧ B2)
    fg+ (x , x₁) = (f+ x ) , g+ x₁
    fg- : (A2 ∧ B2 → A1 ∧ B1)
    fg- (x , x₁) = f- x , g- x₁
    fg-+ : ∀ x → fg- (fg+ x) ≡ x
    fg-+ (x , x₁) = and≡ (f-+ x ) (g-+ x₁ )
    fg+- : ∀ x → fg+ (fg- x) ≡ x
    fg+- (x , x₁) = and≡ (f+- x ) (g+- x₁ )

iso∨ : ∀ {A1 A2 B1 B2} → (A1 ≃ A2) → (B1 ≃ B2) → (A1 ∨ B1) ≃ (A2 ∨ B2)
iso∨ {A1} {A2} {B1} {B2} (iso f+ f- f-+ f+-) (iso g+ g- g-+ g+-)
  = iso fg+ fg- fg-+ fg+- where
    fg+ : (A1 ∨ B1 → A2 ∨ B2)
    fg+ (in1 x) = in1 (f+ x)
    fg+ (in2 x) = in2 (g+ x)
    fg- : (A2 ∨ B2 → A1 ∨ B1)
    fg- (in1 x) = in1 (f- x)
    fg- (in2 x) = in2 (g- x)
    fg-+ : ∀ x → fg- (fg+ x) ≡ x
    fg-+ (in1 x) = cong in1 (f-+ x )
    fg-+ (in2 x) = cong in2 (g-+ x )
    fg+- : ∀ x → fg+ (fg- x) ≡ x
    fg+- (in1 x) = cong in1 (f+- x )
    fg+- (in2 x) = cong in2 (g+- x )

id≃ : ∀ (A : Set) → A ≃ A
id≃ A = iso (λ x → x ) (λ x → x ) (λ _ → refl) (λ _ → refl)


_≡≃_ : ∀ {A B C : Set} → A ≡ B → B ≃ C → A ≃ C
refl ≡≃ BC = BC

refl2iso : ∀ {A B} → A ≡ B → A ≃ B
refl2iso refl = id≃ _

_iso∘_ : ∀ {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
(iso f+ f- f-+ f+-) iso∘ (iso f+1 f-1 f-+1 f+-1) = iso (f+1 ∘ f+) (f- ∘ f-1 ) (forward  ) backward where
  forward : ∀ x → f- (f-1 (f+1 (f+ x))) ≡ x
  forward x rewrite f-+1 (f+ x) rewrite f-+ x = refl
  backward : ∀ y → f+1 (f+ (f- (f-1 y))) ≡ y
  backward y rewrite f+- (f-1 y) rewrite f+-1 y = refl

iso~ : ∀ {A B : Set} → A ≃ B → B ≃ A
iso~ (iso f+ f- f-+ f+-) = iso f- f+ f+- f-+

isodistrL : ∀ {A B C : Set} → (A ∧ (B ∨ C)) ≃ ((A ∧ B) ∨ (A ∧ C))
isodistrL {A} {B} {C} = iso f+ f- f-+ f+- where
  f+ : A ∧ (B ∨ C) → A ∧ B ∨ A ∧ C
  f+ (x , in1 x₁) = in1 (x , x₁ )
  f+ (x , in2 x₁) = in2 (x , x₁ )
  f- : A ∧ B ∨ A ∧ C → A ∧ (B ∨ C)
  f- (in1 (x , x₁)) = x , (in1 x₁ )
  f- (in2 (x , x₁)) = x , (in2 x₁ )
  f-+ : (x : A ∧ (B ∨ C)) → f- (f+ x) ≡ x
  f-+ (x , in1 x₁) = refl
  f-+ (x , in2 x₁) = refl
  f+- : (y : A ∧ B ∨ A ∧ C) → f+ (f- y) ≡ y
  f+- (in1 (x , x₁)) = refl
  f+- (in2 (x , x₁)) = refl

isodistrR : ∀ {A B C : Set} → ((A ∨ B) ∧ C) ≃ ((A ∧ C) ∨ (B ∧ C))
isodistrR {A} {B} {C} = iso f+ f- f-+ f+- where
  f+ : (A ∨ B) ∧ C → A ∧ C ∨ B ∧ C
  f+ (in1 x , x₁) = in1 (x , x₁ )
  f+ (in2 x , x₁) = in2 (x , x₁ )
  f- : A ∧ C ∨ B ∧ C → (A ∨ B) ∧ C
  f- (in1 (x , x₁)) = (in1 x) , x₁
  f- (in2 (x , x₁)) = (in2 x) , x₁
  f-+ : (x : (A ∨ B) ∧ C) → f- (f+ x) ≡ x
  f-+ (in1 x , x₁) = refl
  f-+ (in2 x , x₁) = refl
  f+- : (y : A ∧ C ∨ B ∧ C) → f+ (f- y) ≡ y
  f+- (in1 (x , x₁)) = refl
  f+- (in2 (x , x₁)) = refl

assoc∧ : ∀ {A B C} → (A ∧ (B ∧ C)) ≃ ((A ∧ B) ∧ C)
assoc∧ {A} {B} {C} = iso f+ f- f-+ f+- where
  f+ : A ∧ (B ∧ C) → (A ∧ B) ∧ C
  f+ (x , (x₁ , x₂)) = (x , x₁ ) , x₂
  f- : (A ∧ B) ∧ C → A ∧ (B ∧ C)
  f- ((x , x₂) , x₁) = x , (x₂ , x₁ )
  f-+ : (x : A ∧ (B ∧ C)) → f- (f+ x) ≡ x
  f-+ (x , (x₁ , x₂)) = refl
  f+- : (y : (A ∧ B) ∧ C) → f+ (f- y) ≡ y
  f+- ((x₁ , x₂) , x) = refl

assoc∨ : ∀ {A B C} → (A ∨ (B ∨ C)) ≃ ((A ∨ B) ∨ C)
assoc∨ {A} {B} {C} = iso f+ f- f-+ f+- where
  f+ : A ∨ (B ∨ C) → (A ∨ B) ∨ C
  f+ (in1 x) = in1 (in1 x )
  f+ (in2 (in1 x)) = in1 (in2 x )
  f+ (in2 (in2 x)) = in2 x
  f- : (A ∨ B) ∨ C → A ∨ (B ∨ C)
  f- (in1 (in1 x)) = in1 x
  f- (in1 (in2 x)) = in2 (in1 x)
  f- (in2 x) = in2 (in2 x)
  f-+ : (x : A ∨ (B ∨ C)) → f- (f+ x) ≡ x
  f-+ (in1 x) = refl
  f-+ (in2 (in1 x)) = refl
  f-+ (in2 (in2 x)) = refl
  f+- : (y : (A ∨ B) ∨ C) → f+ (f- y) ≡ y
  f+- (in1 (in1 x)) = refl
  f+- (in1 (in2 x)) = refl
  f+- (in2 x) = refl

comm∧ : ∀ {A B} → (A ∧ B) ≃ (B ∧ A)
comm∧ {A} {B} = iso f+ f- f-+ f+- where
  f+ : A ∧ B → B ∧ A
  f+ (x , x₁) = x₁ , x
  f- : B ∧ A → A ∧ B
  f- (x , x₁) = x₁ , x
  f-+ : (x : A ∧ B) → f- (f+ x) ≡ x
  f-+ (x , x₁) = refl
  f+- : (y : B ∧ A) → f+ (f- y) ≡ y
  f+- (x , x₁) = refl

comm∨ : ∀ {A B} → (A ∨ B) ≃ (B ∨ A)
comm∨ {A} {B} = iso f+ f- f-+ f+- where
  f+ : A ∨ B → B ∨ A
  f+ (in1 x) = in2 x
  f+ (in2 x) = in1 x
  f- : B ∨ A → A ∨ B
  f- (in1 x) = in2 x
  f- (in2 x) = in1 x
  f-+ : (x : A ∨ B) → f- (f+ x) ≡ x
  f-+ (in1 x) = refl
  f-+ (in2 x) = refl
  f+- : (y : B ∨ A) → f+ (f- y) ≡ y
  f+- (in1 x) = refl
  f+- (in2 x) = refl

id∧ : ∀ {A} → A ≃ (⊤ ∧ A)
id∧ {A} = iso f+ f- f-+ f+- where
  f+ : A → ⊤ ∧ A
  f+ x = tt , x
  f- : ⊤ ∧ A → A
  f- (tt , x) = x
  f-+ : (x : A) → f- (f+ x) ≡ x
  f-+ x = refl
  f+- : (y : ⊤ ∧ A) → f+ (f- y) ≡ y
  f+- (tt , x) = refl

id∨ : ∀ {A} → A ≃ (⊥ ∨ A)
id∨ {A} = iso f+ f- f-+ f+- where
  f+ : A → ⊥ ∨ A
  f+ = in2
  f- : ⊥ ∨ A → A
  f- (in2 x) = x
  f-+ : (x : A) → f- (f+ x) ≡ x
  f-+ x = refl
  f+- : (y : ⊥ ∨ A) → f+ (f- y) ≡ y
  f+- (in2 x) = refl

annih∧ : ∀ {A} → (A ∧ ⊥) ≃ ⊥
annih∧ {A} = iso f+ f- f-+ f+- where
  f+ : A ∧ ⊥ → ⊥
  f+ (x , ())
  f- : ⊥ → A ∧ ⊥
  f- ()
  f-+ : (x : A ∧ ⊥) → f- (f+ x) ≡ x
  f-+ (x , ())
  f+- : (y : ⊥) → f+ (f- y) ≡ y
  f+- ()
