-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-meta #-}

module QADT.ADTs where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functions
open import QADT.Isomorphisms

open import QADT.Functor
open import Environment

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
𝕧₀ = 𝕍 (o)

infix 50 _²
infix 50 _³

-- Set interpretation of ADTs
⟦_⟧_ : ∀ {n : ℕ} → ADT n → SetEnv n → Set
⟦ 𝕍 x ⟧ e = e x
⟦ 𝟎 ⟧ e = ⊥
⟦ 𝟏 ⟧ e = ⊤
⟦ x × y ⟧ e = ⟦ x ⟧ e ∧ ⟦ y ⟧ e
⟦ x ⊔ y ⟧ e = ⟦ x ⟧ e ∨ ⟦ y ⟧ e
⟦ μ x ⟧ e = LFP λ X → ⟦ x ⟧ (e ⅋o:= X)

-- Functoriality of ADTs
⟦_⟧→_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : SetEnv n} → SetEnv→ ρ σ → (⟦ e ⟧ ρ → ⟦ e ⟧ σ)
⟦ 𝕍 x ⟧→ ρσ = ρσ x
⟦ 𝟎 ⟧→ ρσ = I
⟦ 𝟏 ⟧→ ρσ = I
(⟦ (e1 × e2) ⟧→ ρσ) (x , y) = ( (⟦ e1 ⟧→ ρσ) x , (⟦ e2 ⟧→ ρσ) y )
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in1 x) = in1 ((⟦ e1 ⟧→ ρσ) x)
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in2 y) = in2 ((⟦ e2 ⟧→ ρσ) y)
⟦_⟧→_ (μ e) {ρ} {σ} ρσ = LFP→ (λ X → ⟦ e ⟧ (ρ ⅋o:= X)) (λ X → ⟦ e ⟧ (σ ⅋o:= X))
  (λ f → ⟦ e ⟧→ ConsSetEnv→ (reflSetEnv→ ρ ) f o ) λ X → (⟦ e ⟧→ ConsSetEnv→ ρσ I o)

-- ⟦_⟧→refl : ∀ {n : ℕ} (e : ADT n) (Γ : SetEnv n) x → ⟦ e ⟧→ (reflSetEnv→ Γ) x ≡ x
-- ⟦ e ⟧→refl Γ x = ?

-- Enumeration of ADTS
Enum : Set → Set
Enum A = List A

EnumEnv : ∀ {n} → SetEnv n → Set
EnumEnv Γ = ∀ x → Enum (Γ x)

EnumΓ₀ : EnumEnv Γ₀
EnumΓ₀ = λ ()

{-# TERMINATING #-}
EnumADT : ∀ {n} → (e : ADT n) → (Γ : SetEnv n) → EnumEnv Γ → Enum (⟦ e ⟧ Γ)
EnumADT (𝕍 x) Γ GG = GG x
EnumADT 𝟎 Γ GG = []
EnumADT 𝟏 Γ GG = tt ∷ []
EnumADT (e1 × e2) Γ GG = lazyProd (EnumADT e1 Γ GG) ((EnumADT e2 Γ GG))
EnumADT (e1 ⊔ e2) Γ GG = merge (List→ in1 (EnumADT e1 Γ GG)) (List→ in2 (EnumADT e2 Γ GG))
EnumADT (μ e) Γ GG with EnumADT e (Γ ⅋o:= (⟦ (μ e) ⟧ Γ) ) (io𝓟 _ GG (EnumADT (μ e) Γ GG))
  -- where f = λ { (i x) → GG x ; o → EnumADT (μ e) Γ GG }
... | c = List→ lfp c

{-# TERMINATING #-}
EnumADTk : ∀ {n} → (e : ADT n) → (Γ : SetEnv n) → EnumEnv Γ → ℕ → Enum (⟦ e ⟧ Γ)
EnumADTk _ _ _ 0 = []
EnumADTk (𝕍 x) Γ GG k = (GG x)
EnumADTk 𝟎 Γ GG _ = []
EnumADTk 𝟏 Γ GG _ = tt ∷ []
EnumADTk (e1 × e2) Γ GG k = lazyProd (EnumADTk e1 Γ GG k) ((EnumADTk e2 Γ GG k))
EnumADTk (e1 ⊔ e2) Γ GG k = merge (List→ in1 (EnumADTk e1 Γ GG k)) (List→ in2 (EnumADTk e2 Γ GG k))
EnumADTk (μ e) Γ GG (succ k) =
  List→ lfp (EnumADTk e (Γ ⅋o:= (⟦ (μ e) ⟧ Γ))
            (io𝓟 _ GG (EnumADTk (μ e) Γ GG k)) (succ k))

decΓ₀ : decSetEnv Γ₀
decΓ₀ ()

-- Decidability of ADTs
decADT : ∀ {n} (a : ADT n) (ρ : SetEnv n) (de : decSetEnv ρ) → dec≡ (⟦ a ⟧ ρ)
decADT (𝕍 x) ρ de = λ x₁ y → de x x₁ y
decADT 𝟎 ρ de = λ x y → ∅ x
decADT 𝟏 ρ de = λ {tt tt → in1 (refl) }
decADT (a1 × a2) ρ de (x1 , x2) (y1 , y2) with decADT a1 ρ de x1 y1 | decADT a2 ρ de x2 y2
... | in1 x | in1 x₁ = in1 (cong2 _,_ x x₁ )
... | in1 x | in2 x₁ = in2 (λ x₂ → x₁ (cong pr2 x₂ ) )
... | in2 x | d2 = in2 λ x₁ → x (cong pr1 x₁ )
decADT (a ⊔ a₁) ρ de (in1 x) (in1 x₁) with decADT a ρ de x x₁
... | in1 x₂ = in1 (cong in1 x₂ )
... | in2 x₂ = in2 λ z → x₂ (in1inj z)
-- ... | in2 x₂ = in2 (λ x₃ → x₂ (in1inj {A = ⟦ a ⟧ ρ} x₃ ) )
decADT (a ⊔ a₁) ρ de (in1 x) (in2 x₁) = in2 (λ x₂ → in1≠in2 x₂ )
decADT (a ⊔ a₁) ρ de (in2 x) (in1 x₁) = in2 (λ x₂ → in1≠in2 (~ x₂) )
decADT (a ⊔ a₁) ρ de (in2 x) (in2 x₁) with decADT a₁ ρ de x x₁
... | in1 x₂ = in1 (cong (in2) x₂ )
... | in2 x₂ = in2 (λ x₃ → x₂ (in2inj x₃) )
decADT (μ a) ρ de = decLFP ((λ X → ⟦ a ⟧ (ρ ⅋o:= X))) (λ A dA → decADT a ((ρ ⅋o:= A)) (decExtEnv ρ A de dA) )

==ADT : ∀ {A : ADT 0} → (⟦ A ⟧ Γ₀ → ⟦ A ⟧ Γ₀ → 𝔹)
==ADT {A} x y with decADT A Γ₀ decΓ₀ x y
... | in1 _ = true
... | in2 _ = false

==ADT-correct : (A : ADT 0) → (x y : ⟦ A ⟧ Γ₀) → (x ≡ y) ↔ ==ADT {A} x y ≡ true
==ADT-correct A x y with decADT A Γ₀ decΓ₀ x y in r
... | in1 x₁ = K refl , K x₁
... | in2 x₁ = (λ x₂ → ∅ (x₁ x₂) ) , λ {()}

-- Injectivity of ADTs map functions
ADTFunctorInj : ∀ {n : ℕ} (e : ADT n) {ρ σ : SetEnv n} (ρ→σ : SetEnv→ ρ σ)
                  → SetEnv→Inj ρ→σ → inj (⟦ e ⟧→ ρ→σ)
ADTFunctorInj (𝕍 v) ρ→σ ρ→σInj = ρ→σInj v
ADTFunctorInj 𝟏 ρ→σ ρ→σInj = λ z → z
ADTFunctorInj (e1 × e2) ρ→σ ρ→σInj {x1 , x2} {y1 , y2} x12=y12 = cong2 _,_ x1=y1 x2=y2 where
  x1=y1 = ADTFunctorInj e1 ρ→σ ρ→σInj ((cong pr1) x12=y12 )
  x2=y2 = ADTFunctorInj e2 ρ→σ ρ→σInj ((cong pr2) x12=y12 )
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in1 x} {in1 y} x=y = cong in1 (ADTFunctorInj e1 ρ→σ ρ→σInj (in1inj x=y ) )
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in1 x} {in2 y} ()
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in2 x} {in1 y} ()
ADTFunctorInj (e1 ⊔ e2) ρ→σ ρ→σInj {in2 x} {in2 y} x=y = cong in2 (ADTFunctorInj e2 ρ→σ ρ→σInj (in2inj x=y ) )
-- ADTFunctorInj {n} (μ e) {ρ} {σ} ρ→σ ρ→σInj {lfp x} {lfp y} lx=ly with lfpInj (λ z → ⟦ e ⟧ (σ ⅋o:= z)) lx=ly
-- ... | x=y = cong lfp (ADTFunctorInj e {!   !} {!   !} {!   !}  )
ADTFunctorInj {n} (μ e) {ρ} {σ} ρ→σ ρ→σInj  {x} {y} x=y = foldInj Fmap Finj α αinj x=y where
      F : Set → Set
      F = λ X → ⟦ e ⟧ ((ρ ⅋o:= X))
      G : Set → Set
      G = λ X → ⟦ e ⟧ ((σ ⅋o:= X))
      Fmap : Functor F
      Fmap {X} {Y} f z = ⟦_⟧→_ {succ n} e {(ρ ⅋o:= X)} {(ρ ⅋o:= Y)} (ConsSetEnv→ (reflSetEnv→ ρ) f o ) z
      Finj : FunctorInj F Fmap
      Finj {A} {B} f finj = ADTFunctorInj e {(ρ ⅋o:= A)} {(ρ ⅋o:= B)} (ConsSetEnv→ (reflSetEnv→ ρ) f o)
           λ { o → finj ; (i z) → I }
      α : F (LFP G) → LFP G
      α = (λ z → lfp ((⟦ e ⟧→ ConsSetEnv→ ρ→σ (λ x₁ → x₁) o) z))
      αinj : inj α
      αinj {u} {v} au=av =
        ADTFunctorInj e (ConsSetEnv→ ρ→σ I o) (ConsSetEnv→Inj I ρ→σ I ρ→σInj ) (lfpInj G au=av)

-- ADTFunctorInj (μ e) ρ→σ ρ→σInj {x} {y} x=y = foldInj ? {!   !} {!   !} {!   !} {!   !}
-- foldInj : ∀ {F : Set → Set} (Fmap : Functor F) → FunctorInj F Fmap
--             → ∀ {A : Set} (α : F A → A) → inj α → inj (fold Fmap α)
-- ConsSetEnv→ : ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : SetEnv n} (e12 : SetEnv→ e1 e2)
--              → SetEnv→ ((e ⅋o:= X)1) ((e ⅋o:= Y)2)

foldADT : ∀ {n} (a : ADT (succ n)) (ρ : SetEnv n) (X : Set) (f : ⟦ a ⟧ ((ρ ⅋o:= X)) → X)
          → ⟦ μ a ⟧ ρ → X
foldADT {n} a ρ X = fold (λ f →  ⟦ a ⟧→ ConsSetEnv→ (reflSetEnv→ ρ ) f o )

-- ADTFunctorInj : ∀ {n : ℕ} (e : ADT n) {ρ σ : SetEnv n} (ρ→σ : SetEnv→ ρ σ)
--                   → SetEnv→Inj ρ→σ → inj (⟦ e ⟧→ ρ→σ)

foldInjADT : ∀ {n} (ρ : SetEnv n) (t : ADT (succ n)) {A : Set} (a : ⟦ t ⟧ ((ρ ⅋o:= A)) → A)
             → inj a → inj (foldADT t ρ A a)
foldInjADT {n} ρ t {A} a inja {lfp x} {lfp y} foldx=foldy = {!   !}


open import QADT.EnvIsomorphisms
-- Interpretation of ADTs preserves isomorphisms
⟦_⟧≃_ : ∀ {n : ℕ} → (e : ADT n) → ∀ {ρ σ : SetEnv n} → SetEnv≃ ρ σ → ⟦ e ⟧ ρ ≃ ⟦ e ⟧ σ
⟦ 𝕍 x ⟧≃ ρ≃σ = ρ≃σ x
⟦ 𝟎 ⟧≃ ρ≃σ = id≃ ⊥
⟦ 𝟏 ⟧≃ ρ≃σ = id≃ ⊤
⟦ e × e₁ ⟧≃ ρ≃σ = iso∧ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦ e ⊔ e₁ ⟧≃ ρ≃σ = iso∨ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦_⟧≃_ (μ e) {ρ = ρ} {σ = σ} ρ≃σ = LFP≃ (λ z → ⟦ e ⟧ (ρ ⅋o:= z)) (λ z → ⟦ e ⟧ (σ ⅋o:= z)) f where
  f : (x y : Set) → x ≃ y → (⟦ e ⟧ (ρ ⅋o:= x)) ≃ (⟦ e ⟧ (σ ⅋o:= y))
  f x y xy with coskipSetEnv≃Set≃ xy ρ≃σ
  ... | μ1 = ⟦ e ⟧≃ μ1

-- ≃⟦_⟧≃ :

iso≡trans : ∀ {A B C D : Set} {ab : A ≃ B} {bc : B ≃ C} {cd : C ≃ D} → ((ab iso∘ bc) iso∘ cd) ≡ (ab iso∘ (bc iso∘ cd))
iso≡trans = {!   !}

iso≃ : {A A' B B' : Set} → A ≃ A' → B ≃ B' → (A ≃ B) ≃ (A' ≃ B')
iso≃ {A} {A'} {B} {B'} aa' bb' = iso f+ f- f-+ f+- where
  f+ : A ≃ B → A' ≃ B'
  f+ ab = iso~ aa' iso∘ (ab [=!=] bb' )
  f- : A' ≃ B' → A ≃ B
  f- a'b' = (aa' iso∘ a'b' ) iso∘ iso~ bb'

  -- (aa' iso∘ (iso~ aa' iso∘ (ab iso∘ bb' )) ) iso∘ iso~ bb'
  f-+ : (x : A ≃ B) → f- (f+ x) ≡ x
  f-+ x = {!   !}
  f+- : (y : A' ≃ B') → f+ (f- y) ≡ y
  f+- = {!   !}

wk : ∀ {n} → Fin (succ n) → ADT (n) → ADT (succ n)
wk {n} f (𝕍 x) = 𝕍 (skip f x )
wk {n} f 𝟎 = 𝟎
wk {n} f 𝟏 = 𝟏
wk {n} f (e × e₁) = wk f e × wk f e₁
wk {n} f (e ⊔ e₁) = wk f e ⊔ wk f e₁
wk {n} f (μ e) = μ (wk (i f) e)

-- coskip : ∀ {n} {k} {A : Set k} → (Fin n → A) → Fin (succ n) → A → (Fin (succ n) → A)
-- coskip f o a o = a
-- coskip f o a (i y) = f y
-- coskip {succ n} f (i x) a (o) = f o
-- coskip {succ n} f (i x) a (i y) = coskip (λ x₁ → f (i x₁ ) ) x a y

subst-level : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → Fin (succ n) → ADT n
subst-level {n} (𝕍 x) e' f = (𝕍 ⅋ f := e') x
subst-level 𝟎 e' f = 𝟎
subst-level 𝟏 e' f = 𝟏
subst-level (e × e₁) e' f = subst-level e e' f × subst-level e₁ e' f
subst-level (e ⊔ e₁) e' f = subst-level e e' f ⊔ subst-level e₁ e' f
subst-level {n} (μ e) e' f = μ (subst-level e (wk (o) e' ) (i f))

subst : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → ADT n
subst e e' = subst-level e e' (o)

_[_:=_] :  ∀ {n} (e : ADT (succ n)) → Fin (succ n) → (e' : ADT n) → ADT n
e [ x := e' ] = subst-level e e' x

_[_] : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → ADT n
e [ e' ] = subst e e'

-- The following lemmas are used in the proofs of weakinglemma≃
big~ : ∀ {l} {A : Set l} {a b : A} → a ≡ b → b ≡ a
big~ refl = refl

transpRewrite : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) → B a1 → B a2
transpRewrite B (a12) ba1 rewrite a12 = ba1

transp-+ : ∀ {A : Set} (B : A → Set) {a1 a2 : A} (e : a1 ≡ a2) (b : B a1)
           → transpRewrite B (~ e) (transpRewrite B e b) ≡ b
transp-+ B refl b = refl

rewriteRoot : ∀ {A B : Set} → (E : A ≡ B) → A → B
rewriteRoot refl a = a

rewriteRoot-+ : ∀ {A B : Set} → (E : A ≡ B) → (a : A) → rewriteRoot (big~ E) (rewriteRoot E a) ≡ a
rewriteRoot-+ refl a = refl

rewriteRoot+- : ∀ {A B : Set} → (E : A ≡ B) → (b : B) → rewriteRoot E (rewriteRoot (big~ E) b) ≡ b
rewriteRoot+-  refl b = refl

weakeningLemma≃ : ∀ {n} (x : Fin (succ n)) (A : ADT n) {A' : Set} (ρ : SetEnv n) → ⟦ wk x A ⟧ (ρ ⅋ x := A') ≃ ⟦ A ⟧ ρ
weakeningLemma≃ {n} x A {A'} ρ = iso (wkl+ A) (wkl- A) (wkl-+ A) (wkl+- A) where
  wkl+ : (e : ADT n) → ⟦ wk x e ⟧ (ρ ⅋ x := A') → ⟦ e ⟧ ρ
  wkl+ (𝕍 v) y = rewriteRoot (skipCons ρ x A' v) y
  wkl+ 𝟏 y = tt
  wkl+ (e1 × e2) (y1 , y2) = (wkl+ e1 y1 , wkl+ e2 y2)
  wkl+ (e1 ⊔ e2) (in1 y1) = in1 (wkl+ e1 y1)
  wkl+ (e1 ⊔ e2) (in2 y2) = in2 (wkl+ e2 y2)
  wkl+ (μ e) y = _≃_.f+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (i x) e ⟧≃ λ z → refl2iso (EnvConsLemma ρ x A' X z )) iso∘ (weakeningLemma≃ (i x) e ((ρ ⅋o:= X)))) iso∘ (⟦ e ⟧≃ coskipSetEnv≃Set≃ X≃Y (reflSetEnv≃ ρ)) )) y
  wkl- : (e : ADT n) → ⟦ e ⟧ ρ → ⟦ wk x e ⟧ (ρ ⅋ x := A')
  wkl- (𝕍 v) y = rewriteRoot (big~ (skipCons ρ x A' v) ) y
  wkl- 𝟏 y = tt
  wkl- (e × e₁) (y , z) = wkl- e y , wkl- e₁ z
  wkl- (e ⊔ e₁) (in1 x) = in1 (wkl- e x )
  wkl- (e ⊔ e₁) (in2 x) = in2 (wkl- e₁ x )
  wkl- (μ e) y = _≃_.f- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (i x) e ⟧≃ λ z → refl2iso (EnvConsLemma ρ x A' X z ) ) iso∘ (weakeningLemma≃ (i x) e ((ρ ⅋o:= X)))) iso∘ (⟦ e ⟧≃ coskipSetEnv≃Set≃ X≃Y (reflSetEnv≃ ρ)) )) y
  wkl-+ : (e : ADT n) → ∀ z → wkl- e (wkl+ e z) ≡ z
  wkl-+ (𝕍 v) z = rewriteRoot-+ (skipCons ρ x A' v ) z
  wkl-+ 𝟏 tt = refl
  wkl-+ (e × e₁) (x , x₁) = cong2 _,_ (wkl-+ e x ) (wkl-+ e₁ x₁)
  wkl-+ (e ⊔ e₁) (in1 x) = cong in1 (wkl-+ e x )
  wkl-+ (e ⊔ e₁) (in2 x) = cong in2 (wkl-+ e₁ x )
  wkl-+ (μ e) y = _≃_.f-+ (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (i x) e ⟧≃ λ z → refl2iso (EnvConsLemma ρ x A' X z ) ) iso∘ (weakeningLemma≃ (i x) e ((ρ ⅋o:= X)))) iso∘ (⟦ e ⟧≃ coskipSetEnv≃Set≃ X≃Y (reflSetEnv≃ ρ)) )) y
  wkl+- : (e : ADT n) → ∀ z → wkl+ e (wkl- e z) ≡ z
  wkl+- (𝕍 v) z = rewriteRoot+- (skipCons ρ x A' v) z
  wkl+- 𝟏 tt = refl
  wkl+- (e × e₁) (x , x₁) = cong2 _,_ (wkl+- e x) (wkl+- e₁ x₁)
  wkl+- (e ⊔ e₁) (in1 x) = cong in1 (wkl+- e x )
  wkl+- (e ⊔ e₁) (in2 x) = cong in2 (wkl+- e₁ x )
  wkl+- (μ e) y = _≃_.f+- (LFP≃ _ _
      (λ X Y X≃Y → ((⟦ wk (i x) e ⟧≃ λ z → refl2iso (EnvConsLemma ρ x A' X z) ) iso∘ (weakeningLemma≃ (i x) e ((ρ ⅋o:= X)))) iso∘ (⟦ e ⟧≃ coskipSetEnv≃Set≃ X≃Y (reflSetEnv≃ ρ)) )) y


substlemmagen : ∀ {n} (e : ADT (succ n)) → (e' : ADT n) → (ρ : SetEnv n) → (x : Fin (succ n)) → ⟦ e [ x := e' ] ⟧ ρ ≃ ⟦ e ⟧ (ρ ⅋ x := (⟦ e' ⟧ ρ))
substlemmagen {n} (𝕍 v) e' ρ x = refl2iso (EnvSubstLemma 𝕍 ((λ x₁ → ⟦ x₁ ⟧ ρ )) e' x v  )
substlemmagen {n} 𝟎 e' ρ x = id≃ ⊥
substlemmagen {n} 𝟏 e' ρ x = id≃ ⊤
substlemmagen {n} (e × e₁) e' ρ x = iso∧ (substlemmagen e e' ρ x ) (substlemmagen e₁ e' ρ x )
substlemmagen {n} (e ⊔ e₁) e' ρ x = iso∨ (substlemmagen e e' ρ x) (substlemmagen e₁ e' ρ x)
substlemmagen {n} (μ e) e' ρ x = LFP≃ ((λ X → ⟦ e [ (i x) := (wk (o) e') ] ⟧ (ρ ⅋o:= X))) ((λ X → ⟦ e ⟧ ((ρ ⅋ x := (⟦ e' ⟧ ρ)) ⅋o:= X))) isom where
  cosk : (A B : Set) → A ≃ B → SetEnv≃
            ((ρ ⅋o:= A) ⅋ (i x) :=
            (⟦ wk (o) e' ⟧ (ρ ⅋o:= A)))
            ((ρ ⅋ x := (⟦ e' ⟧ ρ)) ⅋o:= B)
  cosk A B AB y =
    let e1 = coskipSet≃ (ρ ⅋ x := (⟦ e' ⟧ ρ)) o AB y
        e2 = EnvConsLemma ρ x (⟦ wk (o) e' ⟧ (ρ ⅋o:= A)) A y
        e4 = weakeningLemma≃ o e' {A} ρ
        e6 = coskipSetEnv≃ o A (coskipSet≃ ρ x e4) y
    in big~ e2 ≡≃ (e6 iso∘ e1 )
  isom : (A B : Set) → A ≃ B → (⟦ e [ (i x) := (wk (o) e') ] ⟧ (ρ ⅋o:= A)) ≃ ⟦ e ⟧ ((ρ ⅋ x := (⟦ e' ⟧ ρ)) ⅋o:= B)
  isom A B AB with substlemmagen e (wk o e') (ρ ⅋o:= A) (i x)
  ... | r = r iso∘ (⟦ e ⟧≃ cosk A B AB)
