-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --inversion-max-depth=100  #-}
{-# OPTIONS --allow-unsolved-metas #-}

module RelationsCore where

open import Logic
-- open import Logic-Levels
open import Lifting using (ℕ; zero; succ)
open import Predicates

Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- Identity, Converse, and Composition
≡R : ∀ {A} → Rel A A
≡R = _≡_

~R : ∀ {A B} → Rel A B → Rel B A
~R R = λ x y → R y x

_∘R_ : ∀ {A B C} → Rel A B → Rel B C → Rel A C
_∘R_ {B = B} R S = λ x z → Σ[ y ∈ B ] (R x y × S y z)

_R∘_ : ∀ {A B C} → Rel B C → Rel A B → Rel A C
S R∘ R = R ∘R S

Graph : ∀ {A B} → (A → B) → Rel A B
Graph f = λ a b → f a ≡ b

-- isTotal : ∀ {A B} → Rel A B → Set
-- isTotal {A} {B} R = ∀ x → Σ[ y ∈ B ] R x y
--
-- total→Fun : ∀ {A B} (R : Rel A B) → isTotal R → (A → B)
-- total→Fun R totR x with totR x
-- ... | t1 ,, t2 = t1
--
-- data Graph {A B : Set} (f : A → B) : Rel A B where
--   gra : ∀ x → Graph f x (f x)

module LogicOps₂ {A B : Set} where

  -- The empty relation ∅ ⊆ 𝓟 A×B.
  K⊥₂ : Rel A B
  K⊥₂ _ _ = ⊥

  -- The maximal relation A×B ⊆ 𝓟 A×B.
  K⊤₂ : Rel A B
  K⊤₂ _ _ = ⊤

  _∩₂_ : Rel A B → Rel A B → Rel A B
  R ∩₂ S = λ x y → R x y  ×  S x y
  infix 17 _∩₂_

  _∪₂_ : Rel A B → Rel A B → Rel A B
  R ∪₂ S = λ x y →  R x y  ⊔  S x y
  infix 17 _∪₂_

  ∁₂_ : Rel A B → Rel A B
  ∁₂ R = λ x y → ¬ R x y
  infix 19 ∁₂_

  -- Inclusion of relations.
  _⊆₂_ : Rel A B → Rel A B → Set
  R ⊆₂ S = ∀ x y → R x y → S x y
  infix 16 _⊆₂_

  -- Extensional equivalence of relations.
  _⇔₂_ : Rel A B → Rel A B → Set
  R ⇔₂ S = R ⊆₂ S × S ⊆₂ R
  infix 15 _⇔₂_

  relEq : ∀ {R S : Rel A B} →   R ⇔₂ S   ↔   ∀ x y → R x y ↔ S x y
  relEq = (λ RS x y → pr1 RS x y , pr2 RS x y )
        , λ H → (λ x y → pr1 (H x y)) , (λ x y → pr2 (H x y))

  _⊆!⊆₂_ : ∀ {P Q R : Rel A B} → P ⊆₂ Q → Q ⊆₂ R → P ⊆₂ R
  PQ ⊆!⊆₂ QR = λ x y → QR x y ∘ PQ x y

  _⇔!⇔₂_ : ∀ {P Q R : Rel A B} → P ⇔₂  Q → Q ⇔₂  R → P ⇔₂  R
  (PQ , QP) ⇔!⇔₂ (QR , RQ) = (PQ ⊆!⊆₂ QR) , (RQ ⊆!⊆₂ QP)
  infixr 18 _⇔!⇔₂_

open LogicOps₂ public

-- check : ∀ {A : Set} (R Q : Rel A A) → (_⇔_ R Q) ↔ (R ⇔₂ Q)
-- check R Q = (λ x → x ) , (λ x → x )

module RelationLaws where

  law1 : ∀ {A B : Set} (R : Rel A B) → ≡R ∘R R ⇔₂ R
  law2 : ∀ {A B : Set} (R : Rel A B) → R ∘R ≡R ⇔₂ R
  law3 : ∀ {A : Set} → ~R (≡R {A}) ⇔ ≡R
  law4 : ∀ {A B C : Set} (R : Rel A B) (S : Rel B C) → ~R (R ∘R S) ⇔₂ (~R S) ∘R (~R R)
  law5 : ∀ {A B C D : Set} (R : Rel A B) (S : Rel B C) (T : Rel C D)
          → ((R ∘R S) ∘R T) ⇔₂ (R ∘R (S ∘R T))
  law6 : ∀ {A B : Set} (R : Rel A B) → ~R (~R R) ⇔₂ R

  pr1 (law1 R) x y (.x ,, refl , Rxy) = Rxy
  pr2 (law1 R) x y Rxy = x ,, (refl , Rxy)

  pr1 (law2 R) x y (.y ,, Rxy , refl) = Rxy
  pr2 (law2 R) x y Rxy = y ,, Rxy , refl

  pr1 law3 x .x refl = refl
  pr2 law3 x .x refl = refl

  pr1 (law4 R S) x y (z ,, Ryx , Szx) = z ,, Szx , Ryx
  pr2 (law4 R S) x y (z ,, Szx , Ryz) = z ,, Ryz , Szx

  pr1 (law5 R S T) a d (c ,, (b ,, Rab , Sbc) , Tcd) = b ,, (Rab , (c ,, Sbc , Tcd))
  pr2 (law5 R S T) a d (b ,, Rab , (c ,, Sbc , Tcd)) = c ,, ((b ,, (Rab , Sbc)) , Tcd)

  pr1 (law6 R) x y LHS = LHS
  pr2 (law6 R) x y Rxy = Rxy

module ClosureOperators {U : Set} where
  --reflexive closure
  data _⁼ (R : 𝓡 U) : 𝓡 U where
    ax⁼ : ∀ {x y : U} → R x y → (R ⁼) x y
    ε⁼  : ∀ {x} → (R ⁼) x x

  -- Transitive closure
  data _⁺ (R : 𝓡 U) : 𝓡 U   where
    ax⁺  : ∀ {x y : U}   → R x y → (R ⁺) x y
    _,⁺_ : ∀ {x y z : U} → R x y → (R ⁺) y z → (R ⁺) x z

  -- Transitive closure, starting from the tail
  data _₊ (R : 𝓡 U) : 𝓡 U   where
    ax₊  : ∀ {x y : U}   → R x y → (R ₊) x y
    _₊,_ : ∀ {x y z : U} → (R ₊) x y → R y z → (R ₊) x z

  -- symmetric closure
  data _ˢ (R : 𝓡 U) : 𝓡 U where
    axˢ+ : ∀ {x y} → R x y → (R ˢ) x y
    axˢ- : ∀ {x y} → R y x → (R ˢ) x y

  -- reflexive transitive closure
  -- ⋆ is \*
  data _⋆ (R : 𝓡 U) : 𝓡 U where
    ax⋆ : ∀ {x y : U} → R x y → (R ⋆) x y
    ε⋆  :  ∀ {x} → (R ⋆) x x
    _,⋆_ : ∀ {x y z} → R x y → (R ⋆) y z → (R ⋆) x z

  infix 19 _⁼
  infix 19 _ˢ
  infix 19 _⁺
  infix 19 _₊
  infix 19 _⋆

  TCisTran : ∀ (R : 𝓡 U) {x y z : U} → (R ⋆) x y → (R ⋆) y z → (R ⋆) x z
  TCisTran R (ax⋆ x) R*yz = x ,⋆ R*yz
  TCisTran R ε⋆ R*yz = R*yz
  TCisTran R (x ,⋆ R*xy) R*yz = x ,⋆ (TCisTran R R*xy R*yz)

  TCisSym : ∀ (R : 𝓡 U) {x y : U} → ((R ˢ) ⋆) x y → ((R ˢ) ⋆) y x
  TCisSym R (ax⋆ (axˢ+ x)) = ax⋆ ((axˢ- x))
  TCisSym R (ax⋆ (axˢ- x)) = ax⋆ ((axˢ+ x))
  TCisSym R ε⋆ = ε⋆
  TCisSym R (axˢ+ x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym R rxy) (axˢ- x ,⋆ ε⋆ )
  TCisSym R (axˢ- x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym R rxy) (axˢ+ x ,⋆ ε⋆ )

  EQ : 𝓡 U → 𝓡 U
  EQ R = (R ˢ) ⋆

  ~⁺ : ∀ {R : 𝓡 U} {x y z : U} → (R ⁺) x y → R y z → (R ⁺) x z
  ~⁺ (ax⁺ Rxy) Ryz = Rxy ,⁺ ax⁺ Ryz
  ~⁺ (Rxy₁ ,⁺ R⁺y₁z) Ryz = Rxy₁ ,⁺ ~⁺ R⁺y₁z Ryz

  ~₊ : ∀ {R : 𝓡 U} {x y z : U} → R x y → (R ₊) y z → (R ₊) x z
  ~₊ Rxy (ax₊ Ryz) = ax₊ Rxy ₊, Ryz
  ~₊ Rxy (R₊xy ₊, Ryz) = ~₊ Rxy R₊xy ₊, Ryz

  TC⁺⇔TC₊ : ∀ (R : 𝓡 U) → R ⁺ ⇔ R ₊
  TC⁺⇔TC₊ R = ⁺⊆₊ , ₊⊆⁺ where
    ⁺⊆₊ : R ⁺ ⊆ R ₊
    ⁺⊆₊ x y (ax⁺ Rxy) = ax₊ Rxy
    ⁺⊆₊ x y (Rxy ,⁺ R⁺yz) = ~₊ Rxy (⁺⊆₊ _ y R⁺yz)
    ₊⊆⁺ : R ₊ ⊆ R ⁺
    ₊⊆⁺ x y (ax₊ Rxy) = ax⁺ Rxy
    ₊⊆⁺ x y (R₊xy ₊, Ryz) = ~⁺ (₊⊆⁺ x _ R₊xy) Ryz
open ClosureOperators public

module ClosureOpsPreserveEquivalence {A} {R1 R2 : 𝓡 A} (R12 : R1 ⇔ R2) where

  ⇔⁼ : R1 ⁼ ⇔ R2 ⁼
  pr1 ⇔⁼ x y (ax⁼ R1xy) = ax⁼ (pr1 R12 x y R1xy)
  pr1 ⇔⁼ x .x ε⁼ = ε⁼
  pr2 ⇔⁼ x y (ax⁼ R2xy) = ax⁼ (pr2 R12 x y R2xy)
  pr2 ⇔⁼ x .x ε⁼ = ε⁼

  ⇔ˢ : R1 ˢ ⇔ R2 ˢ
  pr1 ⇔ˢ x y (axˢ+ R1xy) = axˢ+ (pr1 R12 x y R1xy)
  pr1 ⇔ˢ x y (axˢ- R1yx) = axˢ- (pr1 R12 y x R1yx)
  pr2 ⇔ˢ x y (axˢ+ R2xy) = axˢ+ (pr2 R12 x y R2xy)
  pr2 ⇔ˢ x y (axˢ- R2yx) = axˢ- (pr2 R12 y x R2yx)

  ⇔⁺ : R1 ⁺ ⇔ R2 ⁺
  pr1 ⇔⁺ x y (ax⁺ R1xy) = ax⁺ (pr1 R12 x y R1xy)
  pr1 ⇔⁺ x y (R1xy ,⁺ R1⁺yz) = (pr1 R12 x _ R1xy) ,⁺ (pr1 ⇔⁺ _ y R1⁺yz)
  pr2 ⇔⁺ x y (ax⁺ R2xy) = ax⁺ (pr2 R12 x y R2xy)
  pr2 ⇔⁺ x y (R2xy ,⁺ R2⁺yz) = (pr2 R12 x _ R2xy) ,⁺ pr2 ⇔⁺ _ y R2⁺yz

  -- ⊆₊ : R1 ₊ ⊆ R2 ₊
  -- ⊆₊ = (pr2 (TC⁺⇔TC₊ R1)) ⊆!⊆₂
  --                    (pr1 ⇔⁺ ⊆!⊆₂ (pr1 (TC⁺⇔TC₊ R2)))

  ⇔₊ : R1 ₊ ⇔ R2 ₊
  ⇔₊ = (~⇔ {n = 2} (TC⁺⇔TC₊ R1)) ⇔!⇔₂ ⇔⁺ ⇔!⇔₂ (TC⁺⇔TC₊ R2)
  -- pr1 ⇔₊ x y (ax₊ R1xy) = ax₊ (pr1 R12 x y R1xy)
  -- pr1 ⇔₊ x y (R1₊xy ₊, R1yz) = pr1 ⇔₊ x _ R1₊xy ₊, pr1 R12 _ y R1yz
  -- pr2 ⇔₊ x y (ax₊ R2xy) = ax₊ (pr2 R12 x y R2xy)
  -- pr2 ⇔₊ x y (R2₊xy ₊, R2yz) = pr2 ⇔₊ x _ R2₊xy ₊, (pr2 R12 _ y R2yz)

  ⇔⋆ : R1 ⋆ ⇔ R2 ⋆
  pr1 ⇔⋆ x y (ax⋆ Rxy) = ax⋆ (pr1 R12 x y Rxy)
  pr1 ⇔⋆ x .x ε⋆ = ε⋆
  pr1 ⇔⋆ x y (R1xy ,⋆ R2⋆yz) = (pr1 R12 x _ R1xy) ,⋆ pr1 ⇔⋆ _ y R2⋆yz
  pr2 ⇔⋆ x y (ax⋆ R2xy) = ax⋆ (pr2 R12 x y R2xy)
  pr2 ⇔⋆ x .x ε⋆ = ε⋆
  pr2 ⇔⋆ x y (R2xy ,⋆ R2⋆yz) = pr2 R12 x _ R2xy ,⋆ pr2 ⇔⋆ _ y R2⋆yz

-- Properties of relations
module RelationProperties {U : Set} (R : 𝓡 U) where
  reflR   : Set
  irreflR : Set
  symmR   : Set
  asymmR  : Set
  tranR   : Set
  acyclic : Set

  reflR   = ∀ x → R x x
  irreflR = ∀ x → ¬ R x x
  acyclic = ∀ x → ¬ (R ⁺) x x
  symmR   = ∀ x y → R x y → R y x
  asymmR  = ∀ x y → R x y → R y x → x ≡ y
  tranR   = ∀ x y z → R x y → R y z → R x z

  record isEquivalence : Set where
    field
      isRefl : reflR
      isSymm : symmR
      isTran : tranR

  record isPartialOrder : Set where
    field
      isRefl : reflR
      isAsym : asymmR
      isTran : tranR

  record isStrictOrder : Set where
    field
      isIrrefl : irreflR
      isTran   : tranR

  record isPreorder : Set where
    field
      isRefl : reflR
      isTran : tranR

open RelationProperties public
