-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --allow-unsolved-meta #-}

module QADT.ADTs where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functions
open import QADT.Isomorphisms

open import QADT.Functor
open import Environment

-- Definition of Algebraic Datatypes
data ADT (V : Set) : Set where
  𝕍 : V → ADT V
  𝟎 : ADT V
  𝟏 : ADT V
  _×_ : ADT V → ADT V → ADT V
  _⊔_ : ADT V → ADT V → ADT V
  μ : ADT (↑ V) → ADT V

infixr 28 _×_
infixr 27 _⊔_

-- Some common ADT expressions
1+ : ∀ {V} → ADT V → ADT V
1+ a = 𝟏 ⊔ a

_² : ∀ {V} → ADT V → ADT V
_² a = a × a

_³ : ∀ {V} → ADT V → ADT V
_³ a = a × a ²

_⁴ : ∀ {V} → ADT V → ADT V
_⁴ a = a × a ³

_⁵ : ∀ {V} → ADT V → ADT V
_⁵ a = a × a ⁴

Pow : ∀ {V} → ADT V → (n : ℕ) → ADT V
Pow a zero = 𝟏
Pow a (succ n) = a × Pow a n

Pow' : ∀ {V} → ADT V → (n : ℕ) → ADT V
Pow' a zero = 𝟏
Pow' a (succ zero) = a
Pow' a (succ n) = a × Pow' a n

Num : ∀ {V} → ℕ → ADT V
Num zero = 𝟎
Num (succ n) = 1+ (Num n)

Num' : ∀ {V} → ℕ → ADT V
Num' zero = 𝟎
Num' (succ zero) = 𝟏
Num' (succ n) = 1+ (Num' n)

𝕧₀ : ∀ {V} → ADT (↑ V)
𝕧₀ = 𝕍 (o)

infix 50 _²
infix 50 _³
infix 50 _⁴
infix 50 _⁵

-- Set interpretation of ADTs
⟦_⟧_ : ∀ {V : Set} → ADT V → TypeEnv V → Set
⟦ 𝕍 x ⟧ e = e x
⟦ 𝟎 ⟧ e = ⊥
⟦ 𝟏 ⟧ e = ⊤
⟦ x × y ⟧ e = ⟦ x ⟧ e ∧ ⟦ y ⟧ e
⟦ x ⊔ y ⟧ e = ⟦ x ⟧ e ∨ ⟦ y ⟧ e
⟦ μ T ⟧ e = LFP λ X → ⟦ T ⟧ (e ⅋o:= X)


-- Functoriality of ADTs
⟦_⟧→_ : ∀ {V : Set} → (e : ADT V) → ∀ {ρ σ : SetEnv V} → SetEnv→ ρ σ → (⟦ e ⟧ ρ → ⟦ e ⟧ σ)
⟦ 𝕍 x ⟧→ ρσ = ρσ x
⟦ 𝟎 ⟧→ ρσ = I
⟦ 𝟏 ⟧→ ρσ = I
(⟦ (e1 × e2) ⟧→ ρσ) (x , y) = ( (⟦ e1 ⟧→ ρσ) x , (⟦ e2 ⟧→ ρσ) y )
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in1 x) = in1 ((⟦ e1 ⟧→ ρσ) x)
(⟦ e1 ⊔ e2 ⟧→ ρσ) (in2 y) = in2 ((⟦ e2 ⟧→ ρσ) y)
⟦_⟧→_ (μ e) {ρ} {σ} ρσ = LFP→ (λ X → ⟦ e ⟧ (ρ ⅋o:= X)) (λ X → ⟦ e ⟧ (σ ⅋o:= X))
  (λ f → ⟦ e ⟧→ ConsSetEnv→ (reflSetEnv→ ρ ) f) λ X → (⟦ e ⟧→ ConsSetEnv→ ρσ I)

-- ⟦_⟧→refl : ∀ {n : ℕ} (e : ADT n) (Γ : SetEnv n) x → ⟦ e ⟧→ (reflSetEnv→ Γ) x ≡ x
-- ⟦ e ⟧→refl Γ x = ?


-- Enumeration of ADTS
Enum : Set → Set
Enum A = List A

EnumEnv : ∀ {V} → SetEnv V → Set
EnumEnv Γ = ∀ x → Enum (Γ x)

EnumΓ₀ : EnumEnv Γ₀
EnumΓ₀ = λ ()

{-# TERMINATING #-}
EnumADT : ∀ {V} → (e : ADT V) → (Γ : SetEnv V) → EnumEnv Γ → Enum (⟦ e ⟧ Γ)
EnumADT (𝕍 x) Γ GG = GG x
EnumADT 𝟎 Γ GG = []
EnumADT 𝟏 Γ GG = tt ∷ []
EnumADT (e1 × e2) Γ GG = lazyProd (EnumADT e1 Γ GG) ((EnumADT e2 Γ GG))
EnumADT (e1 ⊔ e2) Γ GG = merge (List→ in1 (EnumADT e1 Γ GG)) (List→ in2 (EnumADT e2 Γ GG))
EnumADT (μ e) Γ GG with EnumADT e (Γ ⅋o:= (⟦ (μ e) ⟧ Γ) ) (io𝓟 _ GG (EnumADT (μ e) Γ GG))
  -- where f = λ { (i x) → GG x ; o → EnumADT (μ e) Γ GG }
... | c = List→ lfp c

{-# TERMINATING #-}
EnumADTk : ∀ {V} → (e : ADT V) → (Γ : SetEnv V) → EnumEnv Γ → ℕ → Enum (⟦ e ⟧ Γ)
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
decADT : ∀ {V} (a : ADT V) (ρ : SetEnv V) (de : decSetEnv ρ) → dec≡ (⟦ a ⟧ ρ)
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

==ADT : ∀ {A : ADT ⊥} → (⟦ A ⟧ Γ₀ → ⟦ A ⟧ Γ₀ → 𝔹)
==ADT {A} x y with decADT A Γ₀ decΓ₀ x y
... | in1 _ = true
... | in2 _ = false

==ADT-correct : (A : ADT ⊥) → (x y : ⟦ A ⟧ Γ₀) → (x ≡ y) ↔ ==ADT {A} x y ≡ true
==ADT-correct A x y with decADT A Γ₀ decΓ₀ x y in r
... | in1 x₁ = K refl , K x₁
... | in2 x₁ = (λ x₂ → ∅ (x₁ x₂) ) , λ {()}

-- Injectivity of ADTs map functions
ADTFunctorInj : ∀ {V : Set} (e : ADT V) {ρ σ : SetEnv V} (ρ→σ : SetEnv→ ρ σ)
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
ADTFunctorInj {V} (μ e) {ρ} {σ} ρ→σ ρ→σInj  {x} {y} x=y = foldInj Fmap Finj α αinj x=y where
      F : Set → Set
      F = λ X → ⟦ e ⟧ ((ρ ⅋o:= X))
      G : Set → Set
      G = λ X → ⟦ e ⟧ ((σ ⅋o:= X))
      Fmap : Functor F
      Fmap {X} {Y} f z = ⟦_⟧→_ {↑ V} e {(ρ ⅋o:= X)} {(ρ ⅋o:= Y)} (ConsSetEnv→ (reflSetEnv→ ρ) f) z
      Finj : FunctorInj F Fmap
      Finj {A} {B} f finj = ADTFunctorInj e {(ρ ⅋o:= A)} {(ρ ⅋o:= B)} (ConsSetEnv→ (reflSetEnv→ ρ) f)
           λ { o → finj ; (i z) → I }
      α : F (LFP G) → LFP G
      α = (λ z → lfp ((⟦ e ⟧→ ConsSetEnv→ ρ→σ (λ x₁ → x₁)) z))
      αinj : inj α
      αinj {u} {v} au=av =
        ADTFunctorInj e (ConsSetEnv→ ρ→σ I) (ConsSetEnv→Inj I ρ→σ I ρ→σInj ) (lfpInj G au=av)

-- ADTFunctorInj (μ e) ρ→σ ρ→σInj {x} {y} x=y = foldInj ? {!   !} {!   !} {!   !} {!   !}
-- foldInj : ∀ {F : Set → Set} (Fmap : Functor F) → FunctorInj F Fmap
--             → ∀ {A : Set} (α : F A → A) → inj α → inj (fold Fmap α)
-- ConsSetEnv→ : ∀ {n} {X Y : Set} (f : X → Y) → {e1 e2 : SetEnv n} (e12 : SetEnv→ e1 e2)
--              → SetEnv→ ((e ⅋o:= X)1) ((e ⅋o:= Y)2)

foldADT : ∀ {V} (a : ADT (↑ V)) (ρ : SetEnv V) (X : Set) (f : ⟦ a ⟧ ((ρ ⅋o:= X)) → X)
          → ⟦ μ a ⟧ ρ → X
foldADT {n} a ρ X = fold (λ f →  ⟦ a ⟧→ ConsSetEnv→ (reflSetEnv→ ρ ) f)

-- ADTFunctorInj : ∀ {n : ℕ} (e : ADT n) {ρ σ : SetEnv n} (ρ→σ : SetEnv→ ρ σ)
--                   → SetEnv→Inj ρ→σ → inj (⟦ e ⟧→ ρ→σ)

-- foldInjADT : ∀ {n} (ρ : SetEnv n) (t : ADT (succ n)) {A : Set} (a : ⟦ t ⟧ ((ρ ⅋o:= A)) → A)
--              → inj a → inj (foldADT t ρ A a)
-- foldInjADT {n} ρ t {A} a inja {lfp x} {lfp y} foldx=foldy = let
--   e = inja foldx=foldy
--   e2 = ADTFunctorInj t (reflSetEnv→ ((ρ ⅋o:= A)) ) (reflSetEnv→Inj (ρ ⅋o:= A)) {!   !}
--     in {! e2  !}


open import QADT.EnvIsomorphisms
-- Interpretation of ADTs preserves isomorphisms
⟦_⟧≃_ : ∀ {V : Set} → (e : ADT V) → ∀ {ρ σ : SetEnv V} → SetEnv≃ ρ σ → ⟦ e ⟧ ρ ≃ ⟦ e ⟧ σ
⟦ 𝕍 x ⟧≃ ρ≃σ = ρ≃σ x
⟦ 𝟎 ⟧≃ ρ≃σ = id≃ ⊥
⟦ 𝟏 ⟧≃ ρ≃σ = id≃ ⊤
⟦ e × e₁ ⟧≃ ρ≃σ = iso∧ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦ e ⊔ e₁ ⟧≃ ρ≃σ = iso∨ (⟦ e ⟧≃ ρ≃σ) (⟦ e₁ ⟧≃ ρ≃σ)
⟦_⟧≃_ (μ e) {ρ = ρ} {σ = σ} ρ≃σ = LFP≃ (λ z → ⟦ e ⟧ (ρ ⅋o:= z)) (λ z → ⟦ e ⟧ (σ ⅋o:= z)) f where
  f : (x y : Set) → x ≃ y → (⟦ e ⟧ (ρ ⅋o:= x)) ≃ (⟦ e ⟧ (σ ⅋o:= y))
  f x y xy with coskipSetEnv≃Set≃ xy ρ≃σ
  ... | μ1 = ⟦ e ⟧≃ μ1

ADT→ : ∀ {V W} → (V → W) → ADT V → ADT W
ADT→ f (𝕍 x) = 𝕍 (f x)
ADT→ f 𝟎 = 𝟎
ADT→ f 𝟏 = 𝟏
ADT→ f (a1 × a2) = ADT→ f a1 × ADT→ f a2
ADT→ f (a1 ⊔ a2) = ADT→ f a1 ⊔ ADT→ f a2
ADT→ f (μ a) = μ (ADT→ (↑→ f) a )

wk₀ : ∀ {V} → ADT V → ADT (↑ V)
wk₀ = ADT→ i

liftADT : ∀ {V W} → (V → ADT W) → ↑ V → ADT (↑ W)
liftADT f = io (wk₀ ∘ f) (𝕍 o)

_[_] : ∀ {V W} → ADT V → (V → ADT W) → ADT W
𝕍 x [ f ] = f x
𝟎 [ f ] = 𝟎
𝟏 [ f ] = 𝟏
(a1 × a2) [ f ] = (a1 [ f ]) × (a2 [ f ])
(a1 ⊔ a2) [ f ] = (a1 [ f ]) ⊔ (a2 [ f ])
μ a [ f ] = μ (a [ liftADT f ])

subst : ∀ {V} (e : ADT (↑ V)) → (e' : ADT V) → ADT V
subst e e' = e [ io 𝕍 e' ]
-- subst (𝕍 (i x)) e' = 𝕍 x
-- subst (𝕍 o) e' = e'
-- subst 𝟎 e' = 𝟎
-- subst 𝟏 e' = 𝟏
-- subst (e1 × e2) e' = subst e1 e' × subst e2 e'
-- subst (e1 ⊔ e2) e' = subst e1 e' ⊔ subst e2 e'
-- subst (μ e) e' = μ (subst e (wk₀ e'))

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

mapLemma≃ : ∀ {V W} (e : ADT V) (f : V → W) (ρ : SetEnv W) → ⟦ ADT→ f e ⟧ ρ ≃ ⟦ e ⟧ (ρ ∘ f)
mapLemma≃ (𝕍 v) f ρ = refl2iso refl
mapLemma≃ 𝟎 f ρ = refl2iso refl
mapLemma≃ 𝟏 f ρ = refl2iso refl
mapLemma≃ (e1 × e2) f ρ = iso∧ (mapLemma≃ e1 f ρ) (mapLemma≃ e2 f ρ)
mapLemma≃ (e1 ⊔ e2) f ρ = iso∨ (mapLemma≃ e1 f ρ) (mapLemma≃ e2 f ρ)
mapLemma≃ (μ e) f ρ = LFP≃ _ _ h where
  h = λ X Y XY → mapLemma≃ e (↑→ f) (ρ ⅋o:= X) iso∘ (⟦ e ⟧≃ io𝓟 _ (λ x → refl2iso refl ) XY  )

weakLemma≃ : ∀ {V} (e : ADT V) (A : Set) (ρ : SetEnv V) → ⟦ ADT→ i e ⟧ (ρ ⅋o:= A) ≃ ⟦ e ⟧ ρ
weakLemma≃ e A ρ = mapLemma≃ e i (ρ ⅋o:= A )

substlemma : ∀ {V W} (e : ADT V) (f : V → ADT W) (ρ : SetEnv W) → ⟦ (e [ f ]) ⟧ ρ ≃ ⟦ e ⟧ (λ v → ⟦ f v ⟧ ρ)
substlemma (𝕍 x) f ρ = id≃ (⟦ f x ⟧ ρ)
substlemma 𝟎 f ρ = id≃ ⊥
substlemma 𝟏 f ρ = id≃ ⊤
substlemma (e1 × e2) f ρ = iso∧ (substlemma e1 f ρ) (substlemma e2 f ρ)
substlemma (e1 ⊔ e2) f ρ = iso∨ (substlemma e1 f ρ) (substlemma e2 f ρ)
substlemma (μ e) f ρ = LFP≃ g1 g2 g12 where
  g1 = λ X → ⟦ e [ liftADT f ] ⟧ (ρ ⅋o:= X)
  g2 = λ X → ⟦ e ⟧ ((λ v → ⟦ f v ⟧ ρ) ⅋o:= X)
  g12 : _
  g12 X Y X=Y with substlemma e (liftADT f) (ρ ⅋o:= X)
  ... | c = c iso∘ (⟦ e ⟧≃ λ { (i x) → weakLemma≃ (f x) X ρ ; o → X=Y } )
