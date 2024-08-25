-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-meta #-}

module ADTs where

open import BasicLogic
open import BasicDatatypes
open import Functions
open import Isomorphisms

open import Environment
open import Functor

-- Definition of Algebraic Datatypes
data ADT (n : ℕ) : Set where
  𝕍 : Fin n → ADT n
  𝟎 : ADT n
  𝟏 : ADT n
  _×_ : ADT n → ADT n → ADT n
  _⊔_ : ADT n → ADT n → ADT n
  μ : ADT (succ n) → ADT n

infixr 28 _×_
infixr 27 _⊔_

-- Some common ADT expressions
1+ : ∀ {n} → ADT n → ADT n
1+ a = 𝟏 ⊔ a

_² : ∀ {n} → ADT n → ADT n
_² a = a × a

_³ : ∀ {n} → ADT n → ADT n
_³ a = a × a ²

Num : ∀ {n} → ℕ → ADT n
Num zero = 𝟎
Num (succ n) = 1+ (Num n)

𝕧₀ : ∀ {n} → ADT (succ n)
𝕧₀ = 𝕍 (here _)

infix 50 _²
infix 50 _³

-- Set interpretation of ADTs
⟦_⟧_ : ∀ {n : ℕ} → ADT n → Env n → Set
⟦ 𝕍 x ⟧ e = e x
⟦ 𝟎 ⟧ e = ⊥
⟦ 𝟏 ⟧ e = ⊤
⟦ x × y ⟧ e = ⟦ x ⟧ e ∧ ⟦ y ⟧ e
⟦ x ⊔ y ⟧ e = ⟦ x ⟧ e ∨ ⟦ y ⟧ e
⟦ μ x ⟧ e = LFP λ X → ⟦ x ⟧ (extEnv X e)

-- Functoriality of ADTs
⟦_⟧→_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : Env n} → Env→ ρ σ → (⟦ e ⟧ ρ → ⟦ e ⟧ σ)
⟦ 𝕍 x ⟧→ ρσ = ρσ x
⟦ 𝟎 ⟧→ ρσ = I
⟦ 𝟏 ⟧→ ρσ = I
(⟦ (e1 × e2) ⟧→ ρσ) (x , y) = ( (⟦ e1 ⟧→ ρσ) x , (⟦ e2 ⟧→ ρσ) y )
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in1 x) = in1 ((⟦ e1 ⟧→ ρσ) x)
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in2 y) = in2 ((⟦ e2 ⟧→ ρσ) y)
⟦_⟧→_ (μ e) {ρ} {σ} ρσ = LFP→ (λ X → ⟦ e ⟧ extEnv X ρ) (λ X → ⟦ e ⟧ extEnv X σ)
  (λ f → ⟦ e ⟧→ ConsEnv→ f (reflEnv→ ρ ) ) λ X → (⟦ e ⟧→ ConsEnv→ I ρσ )

-- ⟦_⟧→refl : ∀ {n : ℕ} (e : ADT n) (Γ : Env n) x → ⟦ e ⟧→ (reflEnv→ Γ) x ≡ x
-- ⟦ e ⟧→refl Γ x = ?

-- Decidability of ADTs
decADT : ∀ {n} (a : ADT n) (ρ : Env n) (de : decEnv ρ) → dec≡ (⟦ a ⟧ ρ)
decADT (𝕍 x) ρ de = λ x₁ y → de x x₁ y
decADT 𝟎 ρ de = λ x y → exFalso x
decADT 𝟏 ρ de = λ {tt tt → in1 (refl tt) }
decADT (a1 × a2) ρ de (x1 , x2) (y1 , y2) with decADT a1 ρ de x1 y1 | decADT a2 ρ de x2 y2
... | in1 x | in1 x₁ = in1 (x ≡,≡ x₁ )
... | in1 x | in2 x₁ = in2 (λ x₂ → x₁ (pr2≡,≡ x₂ ) )
... | in2 x | d2 = in2 λ x₁ → x (pr1≡,≡ x₁ )
decADT (a ⊔ a₁) ρ de (in1 x) (in1 x₁) with decADT a ρ de x x₁
... | in1 x₂ = in1 (ext in1 x₂ )
... | in2 x₂ = in2 (λ x₃ → x₂ (prin1≡ {A = ⟦ a ⟧ ρ} x₃ ) )
decADT (a ⊔ a₁) ρ de (in1 x) (in2 x₁) = in2 (λ x₂ → in1≠in2 x₂ )
decADT (a ⊔ a₁) ρ de (in2 x) (in1 x₁) = in2 (λ x₂ → in2≠in1 x₂ )
decADT (a ⊔ a₁) ρ de (in2 x) (in2 x₁) with decADT a₁ ρ de x x₁
... | in1 x₂ = in1 (ext (in2) x₂ )
... | in2 x₂ = in2 (λ x₃ → x₂ (prin2≡ {B = ⟦ a₁ ⟧ ρ} x₃ ) )
decADT (μ a) ρ de = decLFP ((λ X → ⟦ a ⟧ extEnv X ρ)) (λ A dA → decADT a (extEnv A ρ) (decExtEnv ρ A de dA) )

-- Injectivity of ADTs map functions
ADTFunctorInj : ∀ {n : ℕ} (e : ADT n) {ρ σ : Env n} (ρ→σ : Env→ ρ σ)
                  → Env→Inj ρ→σ → inj (⟦ e ⟧→ ρ→σ)
ADTFunctorInj (𝕍 v) ρ→σ ρ→σInj = ρ→σInj v
ADTFunctorInj 𝟏 ρ→σ ρ→σInj = λ z → z
ADTFunctorInj (e1 × e2) ρ→σ ρ→σInj {x1 , x2} {y1 , y2} x12=y12 =
   ADTFunctorInj e1 ρ→σ ρ→σInj (pr1≡,≡ x12=y12 ) ≡,≡ ADTFunctorInj e2 ρ→σ ρ→σInj (pr2≡,≡ x12=y12 )
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in1 x} {in1 y} x=y = ext in1 (ADTFunctorInj e1 ρ→σ ρ→σInj (prin1≡ x=y ) )
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in1 x} {in2 y} ()
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in2 x} {in1 y} ()
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in2 x} {in2 y} x=y = ext in2 (ADTFunctorInj e2 ρ→σ ρ→σInj (prin2≡ x=y ) )
ADTFunctorInj {n} (μ e) {ρ} {σ} ρ→σ ρ→σInj {lfp x} {lfp y} lx=ly with lfpInj (λ z → ⟦ e ⟧ extEnv z σ) lx=ly
... | x=y = ext lfp (ADTFunctorInj e {!   !} {!   !} {!   !}  )
-- ADTFunctorInj {n} (μ e) {ρ} {σ} ρ→σ ρ→σInj  {x} {y} x=y = foldinj x=y where
--       F : Set → Set
--       F = λ X → ⟦ e ⟧ (extEnv X ρ)
--       Fmap : Functor F
--       Fmap {X} {Y} f z = ⟦_⟧→_ {succ n} e {extEnv X ρ} {extEnv Y ρ} (ConsEnv→ f (reflEnv→ ρ) ) z
--       Finj : FunctorInj F Fmap
--       Finj {A} {B} f finj = ADTFunctorInj e {extEnv A ρ} {extEnv B ρ} (ConsEnv→ f (reflEnv→ ρ))
--            λ { (here .n) → finj ; (down z) → I }
--       A : Set
--       A = ⟦ μ e ⟧ σ
--       α : F A → A  
--       α = (λ z → lfp ((⟦ e ⟧→ ConsEnv→ (λ x₁ → x₁) ρ→σ) z))
--       αinj : inj α
--       αinj {z1} {z2} z12 with lfpInj (λ z → ⟦ e ⟧ extEnv z σ) z12
--       -- ... | c = {!   !}
--       ... | c = ADTFunctorInj e {extEnv A ρ} {extEnv A ρ} (reflEnv→ (extEnv A ρ)) (reflEnv→Inj (coskip ρ (here n) (LFP (λ z → ⟦ e ⟧ coskip σ (here n) z))) ) g
--         where g = {!   !}
--       foldinj = foldInj Fmap Finj α αinj

   -- fold (λ f z → (⟦ e ⟧→ ConsEnv→ f (λ x₁ x₂ → x₂)) z)
   --   (λ z → lfp ((⟦ e ⟧→ ConsEnv→ (λ x₁ → x₁) ρ→σ) z)) x
   --   ≡
   --   fold (λ f z → (⟦ e ⟧→ ConsEnv→ f (λ x₁ x₂ → x₂)) z)
   --   (λ z → lfp ((⟦ e ⟧→ ConsEnv→ (λ x₁ → x₁) ρ→σ) z)) y
   --
   -- fold (λ f → ⟦ e ⟧→ ConsEnv→ f (λ x₁ x₂ → x₂))
   --           (λ z → lfp ((⟦ e ⟧→ ConsEnv→ (λ x₁ → x₁) ρ→σ) z)) x
   --           ≡
   --           fold (λ f → ⟦ e ⟧→ ConsEnv→ f (λ x₁ x₂ → x₂))
   --           (λ z → lfp ((⟦ e ⟧→ ConsEnv→ (λ x₁ → x₁) ρ→σ) z)) y

-- ADTFunctorInj (μ e) ρ→σ ρ→σInj {x} {y} x=y = foldInj ? {!   !} {!   !} {!   !} {!   !}
-- foldInj : ∀ {F : Set → Set} (Fmap : Functor F) → FunctorInj F Fmap
--             → ∀ {A : Set} (α : F A → A) → inj α → inj (fold Fmap α)
-- ConsEnv→ : ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : Env n} (e12 : Env→ e1 e2)
--              → Env→ (extEnv X e1) (extEnv Y e2)

foldADT : ∀ {n} (a : ADT (succ n)) (ρ : Env n) (X : Set) (f : ⟦ a ⟧ (extEnv X ρ) → X)
          → ⟦ μ a ⟧ ρ → X
foldADT {n} a ρ X = fold (λ f →  ⟦ a ⟧→ ConsEnv→ f (reflEnv→ ρ ) )

foldInjADT : ∀ {n} (ρ : Env n) (t : ADT (succ n)) {A : Set} (a : ⟦ t ⟧ (extEnv A ρ) → A) → inj a → inj (foldADT t ρ A a)
foldInjADT {n} ρ t {A} a inja = {!   !}

-- Interpretation of ADTs preserves isomorphisms
⟦_⟧≃_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : Env n} → Env≃ ρ σ → ⟦ e ⟧ ρ ≃ ⟦ e ⟧ σ
⟦ 𝕍 x ⟧≃ ρ≃σ = ρ≃σ x
⟦ 𝟎 ⟧≃ ρ≃σ = iso (λ x → x ) (λ x → x ) refl refl
⟦ 𝟏 ⟧≃ ρ≃σ = iso (λ z → z) (λ z → z) refl refl
⟦ e × e₁ ⟧≃ ρ≃σ = iso∧ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦ e ⊔ e₁ ⟧≃ ρ≃σ = iso∨ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦_⟧≃_ (μ e) {ρ = ρ} {σ = σ} ρ≃σ = LFP≃ (λ z → ⟦ e ⟧ extEnv z ρ) (λ z → ⟦ e ⟧ extEnv z σ) f where
  f : (x y : Set) → x ≃ y → (⟦ e ⟧ extEnv x ρ) ≃ (⟦ e ⟧ extEnv y σ)
  f x y xy with coskipEnv≃Set≃ xy ρ≃σ
  ... | μ1 = ⟦ e ⟧≃ μ1

wk : ∀ {n} → Fin (succ n) → ADT (n) → ADT (succ n)
wk {n} f (𝕍 x) = 𝕍 (skip f x )
wk {n} f 𝟎 = 𝟎
wk {n} f 𝟏 = 𝟏
wk {n} f (e × e₁) = wk f e × wk f e₁
wk {n} f (e ⊔ e₁) = wk f e ⊔ wk f e₁
wk {n} f (μ e) = μ (wk (down f) e)

subst-level : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → Fin (succ n) → ADT n
subst-level {n} (𝕍 x) e' f = coskip 𝕍 f e' x
subst-level 𝟎 e' f = 𝟎
subst-level 𝟏 e' f = 𝟏
subst-level (e × e₁) e' f = subst-level e e' f × subst-level e₁ e' f
subst-level (e ⊔ e₁) e' f = subst-level e e' f ⊔ subst-level e₁ e' f
subst-level {n} (μ e) e' f = μ (subst-level e (wk (here _) e' ) (down f))

subst : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → ADT n
subst e e' = subst-level e e' (here _)

_[_:=_] :  ∀ {n} (e : ADT (succ n)) → Fin (succ n) → (e' : ADT n) → ADT n
e [ x := e' ] = subst-level e e' x

_[_] : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → ADT n
e [ e' ] = subst e e'

-- The following lemmas are used in the proofs of weakinglemma≃
big~ : ∀ {l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
big~ (refl x) = refl x

transpRewrite : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) → B a1 → B a2
transpRewrite B (a12) ba1 rewrite a12 = ba1

transp-+ : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) (b : B a1)
           → transpRewrite B (~ e) (transpRewrite B e b) ≡ b
transp-+ B (refl a1) b = refl b

rewriteRoot : ∀ {A B : Set} → (E : A ≡ B) → A → B
rewriteRoot (refl _) a = a

rewriteRoot-+ : ∀ {A B : Set} → (E : A ≡ B) → (a : A) → rewriteRoot (big~ E) (rewriteRoot E a) ≡ a
rewriteRoot-+ (refl _) a = refl a

rewriteRoot+- : ∀ {A B : Set} → (E : A ≡ B) → (b : B) → rewriteRoot E (rewriteRoot (big~ E) b) ≡ b
rewriteRoot+-  (refl _) b = refl b

weakeningLemma≃ : ∀ {n} (x : Fin (succ n)) (A : ADT n) {A' : Set} (ρ : Env n) → ⟦ wk x A ⟧ (coskip ρ x A') ≃ ⟦ A ⟧ ρ
weakeningLemma≃ {n} x A {A'} ρ = iso (wkl+ A) (wkl- A) (wkl-+ A) (wkl+- A) where
  wkl+ : (e : ADT n) → ⟦ wk x e ⟧ coskip ρ x A' → ⟦ e ⟧ ρ
  wkl+ (𝕍 v) y = rewriteRoot (skipcoskip ρ x v A' ) y
  wkl+ 𝟏 y = tt
  wkl+ (e1 × e2) (y1 , y2) = (wkl+ e1 y1 , wkl+ e2 y2)
  wkl+ (e1 ⊔ e2) (in1 y1) = in1 (wkl+ e1 y1)
  wkl+ (e1 ⊔ e2) (in2 y2) = in2 (wkl+ e2 y2)
  wkl+ (μ e) y = _≃_.f+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ coskipEnv≃Set≃ X≃Y (reflEnv ρ)) )) y
  wkl- : (e : ADT n) → ⟦ e ⟧ ρ → ⟦ wk x e ⟧ coskip ρ x A'
  wkl- (𝕍 v) y = rewriteRoot (big~ (skipcoskip ρ x v A' ) ) y
  wkl- 𝟏 y = tt
  wkl- (e × e₁) (y , z) = wkl- e y , wkl- e₁ z
  wkl- (e ⊔ e₁) (in1 x) = in1 (wkl- e x )
  wkl- (e ⊔ e₁) (in2 x) = in2 (wkl- e₁ x )
  wkl- (μ e) y = _≃_.f- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ coskipEnv≃Set≃ X≃Y (reflEnv ρ)) )) y
  wkl-+ : (e : ADT n) → ∀ z → wkl- e (wkl+ e z) ≡ z
  wkl-+ (𝕍 v) z = rewriteRoot-+ (skipcoskip ρ x v A' ) z
  wkl-+ 𝟏 tt = refl tt
  wkl-+ (e × e₁) (x , x₁) = (wkl-+ e x ) ≡,≡ wkl-+ e₁ x₁
  wkl-+ (e ⊔ e₁) (in1 x) = ext in1 (wkl-+ e x )
  wkl-+ (e ⊔ e₁) (in2 x) = ext in2 (wkl-+ e₁ x )
  wkl-+ (μ e) y = _≃_.f-+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ coskipEnv≃Set≃ X≃Y (reflEnv ρ)) )) y
  wkl+- : (e : ADT n) → ∀ z → wkl+ e (wkl- e z) ≡ z
  wkl+- (𝕍 v) z = rewriteRoot+- (skipcoskip ρ x v A' ) z
  wkl+- 𝟏 tt = refl tt
  wkl+- (e × e₁) (x , x₁) = wkl+- e x ≡,≡ wkl+- e₁ x₁
  wkl+- (e ⊔ e₁) (in1 x) = ext in1 (wkl+- e x )
  wkl+- (e ⊔ e₁) (in2 x) = ext in2 (wkl+- e₁ x )
  wkl+- (μ e) y = _≃_.f+- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (down x) e ⟧≃ λ z → refl2iso (coskipLemma x z ρ {A'} {X}) ) iso∘ (weakeningLemma≃ (down x) e (extEnv X ρ))) iso∘ (⟦ e ⟧≃ coskipEnv≃Set≃ X≃Y (reflEnv ρ)) )) y


substlemmagen : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → (ρ : Env n) → (x : Fin (succ n)) → ⟦ e [ x := e' ] ⟧ ρ ≃ ⟦ e ⟧ (coskip ρ x (⟦ e' ⟧ ρ))
substlemmagen {n} (𝕍 v) e' ρ x = refl2iso (substlemmaNoADT (λ e → ⟦ e ⟧ ρ) (𝕍) x e' v)
substlemmagen {n} 𝟎 e' ρ x = iso (λ z → z) (λ z → z) refl refl
substlemmagen {n} 𝟏 e' ρ x = iso (λ z → z) (λ z → z) refl refl
substlemmagen {n} (e × e₁) e' ρ x = iso∧ (substlemmagen e e' ρ x ) (substlemmagen e₁ e' ρ x )
substlemmagen {n} (e ⊔ e₁) e' ρ x = iso∨ (substlemmagen e e' ρ x) (substlemmagen e₁ e' ρ x)
substlemmagen {n} (μ e) e' ρ x = LFP≃ ((λ X → ⟦ e [ (down x) := (wk (here n) e') ] ⟧ coskip ρ (here n) X)) ((λ X → ⟦ e ⟧ coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) X)) (isom ) where
        cosk : (A B : Set) → A ≃ B → Env≃
          (coskip (coskip ρ (here n) A) (down x)
          (⟦ wk (here n) e' ⟧ coskip ρ (here n) A))
          (coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) B)
        -- cosk A B A≃B y = {!   !} -- (weakeningLemma≃ (here n) e' ρ)
        cosk A B A≃B y = -- (weakeningLemma≃ (here n) e' ρ)
          let e1 = (coskipLemma x y ρ {⟦ e' ⟧ ρ} {B})
              e2 = (coskipLemma x y  ρ {⟦ wk (here n) e' ⟧ coskip ρ (here n) A} {A})
              e3 = coskipSet≃ {S1 = A} {S2 = B} (coskip ρ x (⟦ wk (here n) e' ⟧ coskip ρ (here n) A)) (here _) A≃B y
              e4 =  (weakeningLemma≃ (here n) e' {A} ρ)
              e5 = coskipSet≃ (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) A≃B y
              e6 = coskipEnv≃ (here (succ n)) A (coskipSet≃ ρ x e4) y
           in big~ e2  ≡≃ (e6  iso∘ e5 )
        isom : (A B : Set) → A ≃ B → (⟦ e [ (down x) := (wk (here n) e') ] ⟧ coskip ρ (here n) A) ≃ (⟦ e ⟧ coskip (coskip ρ x (⟦ e' ⟧ ρ)) (here (succ n)) B)
        isom A B AB with substlemmagen e (wk (here n) e' ) (coskip ρ (here n) A ) (down x)
        ... | r = r iso∘ (⟦ e ⟧≃ cosk A B AB )
