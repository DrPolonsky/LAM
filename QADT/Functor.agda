open import Logic
-- open import BasicDatatypes
open import QADT.Functions
open import QADT.Isomorphisms

module QADT.Functor where

-- Functors and natural transformations
Functor : (Set → Set) → Set₁
Functor F = ∀ {X Y : Set} → (X → Y) → F X → F Y

NatTran : (Set → Set) → (Set → Set) → Set₁
NatTran F G = ∀ X → F X → G X

-- Least fixed points
{-# NO_POSITIVITY_CHECK  #-}
data LFP (F : Set → Set) : Set where
  lfp : F (LFP F) → LFP F

{-# TERMINATING #-}
fold : ∀ {F : Set → Set} (Fmap : Functor F) {A : Set} (a : F A → A) → LFP F → A
fold Fmap a (lfp x) = a (Fmap (fold Fmap a) x )

-- Lambek's Lemma
Lambek : ∀ (F : Set → Set) → F (LFP F) ≃ (LFP F)
Lambek F = iso (f+ ) f- f-+ f+- where
  f+ : F (LFP F) → LFP F
  f+ x = lfp x
  f- : LFP F → F (LFP F)
  f- (lfp x) = x
  f-+ : (x : F (LFP F)) → x ≡ x
  f-+ x = refl
  f+- : (y : LFP F) → f+ (f- y) ≡ y
  f+- (lfp x) = refl

LFP→ : ∀ (f g : Set → Set) → Functor f → NatTran f g → LFP f → LFP g
LFP→ f g fmap fg = fold fmap (λ z → lfp (fg (LFP g) z) )

{-# TERMINATING #-}
LFP≃ : ∀ (f g : Set → Set) → (∀ x y → x ≃ y → f x ≃ g y) → LFP f ≃ LFP g
LFP≃ f g h = iso i j ij ji where
  i : LFP f → LFP g
  i (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h)
  ... | iso f+ f- f-+ f+- = lfp (f+ x )
  j : LFP g → LFP f
  j (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h)
  ... | iso f+ f- f-+ f+- = lfp (f- x )
  ij : (x : LFP f) → j (i x) ≡ x
  ij (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h) in r
  ... | iso f+ f- f-+ f+- = cong lfp (f-+ x )
  ji : (y : LFP g) → i (j y) ≡ y
  ji (lfp x) with h (LFP f) (LFP g) (LFP≃ f g h) in r
  ... | iso f+ f- f-+ f+- = cong lfp (f+- x )

-- Decidability

decFunctor : (Set → Set) → Set₁
decFunctor F = (∀ A → dec≡ A → dec≡ (F A))

{-# TERMINATING #-}
decLFP : ∀ (F : Set → Set) → decFunctor F → dec≡ (LFP F)
decLFP F Fdec (lfp x) (lfp y) with Fdec (LFP F) (decLFP F Fdec) x y
... | in1 x=y = in1 (cong lfp x=y)
... | in2 x≠y = in2 (λ {  (refl) → x≠y (refl) })

-- Injectivity
lfpInj : ∀ (F : Set → Set) {x1 x2 : F (LFP F)} → lfp {F} x1 ≡ lfp {F} x2 → x1 ≡ x2
lfpInj F (refl) = refl

FunctorInj : ∀ (F : Set → Set) → Functor F → Set₁
FunctorInj F Fmap = ∀ {X Y : Set} (f : X → Y) → inj f → inj (Fmap f)

{-# TERMINATING #-}
foldInj : ∀ {F : Set → Set} (Fmap : Functor F) → FunctorInj F Fmap
            → ∀ {A : Set} (α : F A → A) → inj α → inj (fold Fmap α)
foldInj {F} Fmap Finj {A} α injα {lfp x} {lfp y} fx=fy =
  cong lfp (Finj (fold Fmap α) (foldInj {F} Fmap Finj {A} α injα) (injα fx=fy))
