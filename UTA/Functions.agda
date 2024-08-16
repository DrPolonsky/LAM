module Functions {A B : Set} (f : A → B) where

open import BasicLogic
open import SetOperations

-- The forward image (AKA direct image) of a subset X ⊆ A under f
-- consists of all elements y ∈ B which result from applying f to some x ∈ X
data Im (X : Pred A) : Pred B where
  im : ∀ (x : A) → x ∈ X → f x ∈ Im X

-- Alt. notation
f[_] : Pred A → Pred B
f[ X ] = Im X

-- The inverse image (AKA preimage) of a subset Y ⊆ B under f
-- consists of all elements x ∈ X which get mapped into Y by f
Pre : Pred B → Pred A
Pre Y = λ x → f x ∈ Y

-- Alt. notation
f-[_] : Pred B → Pred A
f-[ Y ] = Pre Y

open LogicOps

-- A function is injective if it's one-to-one
-- (No two distinct elements of A are mapped to the same value in B.)
inj : Set
inj = ∀ {x} {y} → f x ≡ f y → x ≡ y

-- A function is surjective if it's onto
-- (Every element of B can be reached by some input from A.)
surj : Set
surj = K⊤ {B} ⊆ Im K⊤ -- "The image of A contains all of B."

-- A function is bijective if it's injective and surjective
bij : Set
bij = inj ∧ surj

-- Lemma about images under injective functions.
injIm : inj → ∀ (X : Pred A) {x : A} {y : B} → f x ≡ y → y ∈ Im X → x ∈ X
injIm injf X e (im x p) with injf e
... | refl x = p

-- ⊆ is \sub=
Im⊆ : ∀ {X Y : Pred A} → X ⊆ Y → f[ X ] ⊆ f[ Y ]
Im⊆ X⊆Y .(f x) (im x p) = im x (X⊆Y x p)

Pre⊆ : ∀ {X Y : Pred B} → X ⊆ Y → f-[ X ] ⊆ f-[ Y ]
Pre⊆ X⊆Y z z∈f-X = X⊆Y (f z) z∈f-X

-- ∪ is \cup
Im∪ : ∀ {X Y : Pred A} → f[ X ∪ Y ] ⇔ f[ X ] ∪ f[ Y ]
Im∪ y = (   λ { (im x (in1 p)) → in1 (im x p) ; (im x (in2 q)) → in2 (im x q)})
         , (λ { (in1 (im x p)) → im x (in1 p) ; (in2 (im x q)) → im x (in2 q)})

Pre∪ : ∀ {X Y : Pred B} → f-[ X ∪ Y ] ⇔ f-[ X ] ∪ f-[ Y ]
Pre∪ z = (λ xy → xy) , (λ xy → xy)

-- ∩ is \cap
Im∩+ : ∀ {X Y : Pred A} → f[ X ∩ Y ] ⊆ (f[ X ] ∩ f[ Y ])
Im∩+ {X} {Y} .(f x) (im x (p , q)) = (im x p , im x q)

Im∩- : inj → ∀ {X} {Y}  → f[ X ] ∩ f[ Y ] ⊆ f[ X ∩ Y ]
Im∩- injf .(f x) (im x p , y∈fY) = im x (p , injIm injf _ (refl (f x) ) y∈fY )

Pre∩ : ∀ {X Y : Pred B} → f-[ X ∩ Y ] ⇔ f-[ X ] ∩ f-[ Y ]
Pre∩ z = (λ xy → xy) , (λ xy → xy)

-- - is -
inj- :   inj → ∀ (X : Pred A) → Im (- X) ⊆ - Im X
inj- injf X .(f _) (im x p) y∈fX = p (injIm injf X (refl (f x)) y∈fX)

surj- : surj → ∀ (X : Pred A) → - Im X ⊆ Im (- X)
surj- sf X y y∉fX with sf y tt
... | im x q = im x (λ x∈X → y∉fX (im x x∈X) )

bij- :   bij → ∀ (X : Pred A) → Im (- X) ⇔ - Im X
bij- (injf , srjf) X z = (inj- injf X z , surj- srjf X z)

Pre- : ∀ {X : Pred B} → f-[ - X ] ⇔ - f-[ X ]
Pre- = λ x → (λ n → n) , (λ n → n)

-- -- Equal points cannot belong to a subset and its complement at the same time.
-- -∈lemma : ∀ {A : Set} (P : Pred A) {x y : A} → x ∈ P → y ∈ (- P) → ¬ (x ≡ y)
-- -∈lemma P Px ¬Px (refl _) = ¬Px Px

-- ext : ∀ {x y : A} → x ≡ y → f x ≡ f y
-- ext (refl x) = refl (f x)
