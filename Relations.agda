-- {-# OPTIONS --type-in-type #-}
-- {-# OPTIONS --inversion-max-depth=100  #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Relations where

open import Logic
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

module WellFoundedness {A : Set} (R : 𝓡 A) where

  -- is_-nf : 𝓟 A
  -- is_-nf x = ∀ y → ¬ R x y
  --
  -- is_~nf : 𝓟 A
  -- is_~nf x = ∀ y → ¬ R y x

  is_-decreasing_ : 𝓟 (ℕ → A)
  is_-decreasing_ s = ∀ n → ~R R (s n) (s (succ n)) -- xₙ > xₙ₊₁

  -- The classical concept of a well-founded relation [TeReSe]
  isWFseq : Set
  isWFseq = ∀ (s : ℕ → A) → ¬ (is_-decreasing_ s)

  -- An element is R-accessible if all elements R-below it are R-accessible
  data is_-accessible_ : 𝓟 A where
    acc : ∀ {x : A} → (∀ y → R y x → is_-accessible_ y) → is_-accessible_ x

  -- A relation is well-founded if every element is accessible
  isWFacc : Set
  isWFacc = ∀ (x : A) → is_-accessible_ x

  is_-inductive_ : 𝓟 A → Set
  is_-inductive_ φ = ∀ x → (∀ y → R y x → φ y) → φ x

  -- The constructive concept of a well-founded relation
  isWFind : Set₁
  isWFind = ∀ (φ : 𝓟 A) → is_-inductive_ φ → ∀ x → φ x

  isWFind→isWFacc : isWFind → isWFacc
  isWFind→isWFacc wfInd = wfInd is_-accessible_ (λ x → acc {x})

  isWFacc→isWFind : isWFacc → isWFind
  isWFacc→isWFind wfAcc φ φ-ind x₀ = f x₀ (wfAcc x₀) where
      f : ∀ x → is_-accessible_ x → φ x
      f x (acc Hx) = φ-ind x (λ y Ryx → f y (Hx y Ryx) )

  isWFind→WFseq : isWFind → isWFseq
  isWFind→WFseq RisWF s sIsR-Dec =
    let φ : 𝓟 A
        φ a = ∀ n → ¬ a ≡ s n -- a ∉ Im [ s ]
        φ-ind : is_-inductive_ φ
        φ-ind x IH m x≡sm = IH (s (succ m))
              (transp (R (s (succ m))) (~ x≡sm) (sIsR-Dec m)) (succ m) refl
     in RisWF φ φ-ind (s zero) zero refl
<<<<<<< HEAD
open WellFoundedness public
=======

open WellFoundedness public
>>>>>>> cd07188a55ca38bd28e5592ad798f67d43609741

module ClosureOperatorProperties {A : Set} (R : 𝓡 A) where

  ¬WF⁼ : A → ¬ (isWFind (R ⁼))
  ¬WF⁼ a WFR⁼ = WFR⁼ K⊥ isR=indK⊥ (WFR⁼ (K A) (λ x _ → x) a) where
                             isR=indK⊥ : is (R ⁼) -inductive K⊥
                             isR=indK⊥ x h = h x ε⁼

  R₊acc-Lemma : ∀ {x} → is (R ₊) -accessible x → ∀ y → (R ₊) y x → is (R ₊) -accessible y
  R₊acc-Lemma (acc xa) = xa

  Racc₊⊆Racc : ∀ (x : A) → is R ₊ -accessible x → is R -accessible x
  Racc₊⊆Racc x (acc H) = acc (λ y Ryx → Racc₊⊆Racc y (H y (ax₊ Ryx) ) )

  Racc⊆R₊acc : ∀ (x : A) → is R -accessible x → is R ₊ -accessible x
  Racc⊆R₊acc x (acc xacc) = acc (λ y → λ {  (ax₊ Ryx) → Racc⊆R₊acc y (xacc y Ryx)
                                            ; (R+yz ₊, Rzx) → R₊acc-Lemma (Racc⊆R₊acc _ (xacc _ Rzx)) y R+yz })

  WFacc₊ : isWFacc R → isWFacc (R ₊)
  WFacc₊ WFaccR x = Racc⊆R₊acc x (WFaccR x)

  wfR+→wfR : isWFacc (R ₊) → isWFacc R
  wfR+→wfR wfR+ x = Racc₊⊆Racc x (wfR+ x)

  WFind₊ : isWFind R → isWFind (R ₊)
  WFind₊ WFindR = isWFacc→isWFind (R ₊) (WFacc₊ (isWFind→isWFacc R WFindR ) )

  lemma⁺→⋆ : ∀ {x y : A} → (R ⁺) x y →  (R ⋆) x y
  lemma⁺→⋆ (ax⁺ Rxy) = ax⋆ Rxy
  lemma⁺→⋆ (Rxy₁ ,⁺ R⁺yy₁) = Rxy₁ ,⋆ lemma⁺→⋆ R⁺yy₁

  TransitiveClosure : R ⋆ ⇔ (R ⁺ ∪ R ⁼)
  TransitiveClosure = TC+ , TC- where
    TC+ : (R ⋆) ⊆ (R ⁺) ∪ (R ⁼)
    TC+ a b (ax⋆ Rab) = in1 (ax⁺ Rab )
    TC+ a .a ε⋆ = in2 ε⁼
    TC+ a b (Ray ,⋆ R⋆yb) = in1 (case (_,⁺_ Ray) -- (λ R⁺yb → (Ray ,⁺ R⁺yb))
                                      (λ { (ax⁼ Ryb) → (Ray ,⁺ (ax⁺ Ryb)) ; ε⁼ → ax⁺ Ray})
                                      (TC+ _ _ R⋆yb))
    TC- : (R ⁺) ∪ (R ⁼) ⊆ (R ⋆)
    TC- x y (in1 (ax⁺ Rxy)) = ax⋆ Rxy
    TC- x y (in1 (Rxy₁ ,⁺ R⁺y₁y)) = Rxy₁ ,⋆ lemma⁺→⋆ R⁺y₁y
    TC- x y (in2 (ax⁼ Rxy)) = ax⋆ Rxy
    TC- x .x (in2 ε⁼) = ε⋆


module Knaster-Tarski {S : Set} (Δ : 𝓟 S → 𝓟 S) (Δ⊆ : ∀ {X Y : 𝓟 S} → X ⊆ Y → Δ X ⊆ Δ Y) where
  -- May need to define it as a datatype: data M : S → Set where ....
  M : 𝓟 S
  M = {!   !}

  M⇔ΔM : M ⇔ Δ M
  M⇔ΔM = {!   !}

  M=μΔ : ∀ N → (Δ N ⊆ N) → M ⊆ N
  M=μΔ N ΔN⊆N = {!   !}


-- Proofs involving classical logic
module ClassicalPropertiesOfRelations where
  open import Classical

  -- This part will be moved elsewhere
  module Preliminaries where
    -- ¬¬Closed : ∀ {A} → 𝓟 A → Set
    -- ¬¬Closed P = ∀ x → ¬¬ P x → P x
    --
    -- ¬¬Lemma : ∀ X → ¬¬ (¬¬ X → X)
    -- ¬¬Lemma X = λ ¬¬X→X → ¬¬X→X (λ ¬¬X → ∅ (¬¬X λ x → ¬¬X→X (K x)))
    --
    -- ¬¬∃→¬∀¬ : ∀ {A} (P : 𝓟 A) → ¬¬ (Σ[ x ∈ A ] P x) → ¬ (∀ x → ¬ P x)
    -- ¬¬∃→¬∀¬ P h x→¬Px = h λ { (y ,, yP) → x→¬Px y yP }
    --
    -- ¬∀¬→¬¬∃ : ∀ {A} (P : 𝓟 A) → ¬ (∀ x → ¬ P x) → ¬¬ (Σ[ x ∈ A ] P x)
    -- ¬∀¬→¬¬∃ P ¬∀¬ ¬∃ = ¬∀¬ λ x Px → ¬∃ (x ,, Px)
    --
    -- DeMorgan∀∃ : Set → Set₁
    -- DeMorgan∀∃ A = ∀ (P : 𝓟 A) → ¬ (∀ x → P x) → Σ[ x ∈ A ] (¬ P x)
    --
    -- MP : ∀ {A} (P : 𝓟 A) → Set
    -- MP {A} P = (∀ x → P x ⊔ ¬ P x) → ¬ (∀ x → ¬ P x) → Σ[ x ∈ A ] P x

    -- DM∀∃ : ∀ {A} (R : 𝓡 A) → Set₁
    -- DM∀∃ {A} R = ∀ x → ∀ (φ : 𝓟 A) → DeMorgan∀∃rel (~R R x) φ

    -- DeMorg→¬¬Closed : ∀ {A} {B : 𝓟 A} → DeMorgan∀∃ A → ¬ (¬¬Closed B) → ⊥
    -- DeMorg→¬¬Closed {A}{B} DeMorg ¬nnC with DeMorg (λ x → ¬¬ (B x) → B x) ¬nnC
    -- ... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

    -- ⟪ is \<<
    _⟪_ : ∀ {A} → 𝓟 A → 𝓟 A → Set
    P ⟪ Q = ¬ (P ⊆ Q) → Σ[ y ∈ _ ] (P y × ¬ Q y)

    -- A relation is well-supported if, for every element in its domain,
    -- and every property, if it's not the case that every element related to x
    -- has the property, then we can exhibit one that doesn't.
    WellSupported : ∀ {A} → 𝓡 A → Set₁
    WellSupported R = ∀ x → ∀ φ → dec φ → (~R R x ⟪ φ)

  open Preliminaries

  module MarkovRelations {A} (R : 𝓡 A) (RisWS : WellSupported R) where

--  Proving that isWFseq → isWFacc
-- Question: Does DeMorgan∀∃ A imply that every predicate on A is decidable?
-- Question: Do we need it to be this general?

    ¬acc→seq : ∀ x → ¬ is R -accessible x → ℕ → A
    ¬acc→seq x ¬accx zero = {!   !}
    ¬acc→seq x ¬accx (succ n) = {!   !}

    isWFseq→isWFacc : isWFseq R → ∀ x → ¬¬ (is R -accessible x)
    isWFseq→isWFacc WFseqR x ¬accx = ¬accx (acc λ y Ryx → {!   !} )

    -- with RisWS x (λ z → R z x) {!   !} (λ H → ¬accx (acc (λ y Ryx → ∅ {!   !})))
    -- ... | y ,, Ryx , pr4 = pr4 Ryx

      -- let ws = RisWS x (λ y → ¬ (is R -accessible y)) λ H → ¬accx {!   !}
      --  in {!   !}

-- Feel free to assume ∀ x → ¬ (φ x) ∨ ¬¬ (φ x)

-- MPrel : ∀ {A} (B P : 𝓟 A) → Set
-- MPrel {A} B P = (∀ x → B x → P x ⊔ ¬ P x) → ¬ (∀ x → B x → ¬ P x) → Σ[ x ∈ A ] (B x × P x)
--
-- fromΣ : ∀ {A} {B : 𝓟 A} {C : Set} → Σ[ x ∈ A ] B x → (∀ x → B x → C) → C
-- fromΣ (x ,, p) f = f x p
--
-- is-ind¬¬ : ∀ {A : Set} (R : 𝓡 A) (φ : 𝓟 A) → (∀ x → DeMorgan∀∃rel (~R R x) φ)  → is R -inductive (λ x → φ x) → is R -inductive (λ x → ¬¬ φ x)
-- is-ind¬¬ R φ DM φ-ind x H ¬φx =
--   let φ-ind' : ¬ (∀ z → R z x → φ z)
--       φ-ind' =  λ G → ¬φx (φ-ind x G )
--       DMcont = DM x φ-ind'
--    in fromΣ DMcont (λ y p → H y (pr1 p) (pr2 p) )
--
-- -- Not provable unless an assumption is added, find the assumption!
-- open import Classical
--
-- MPrel→DMrel : ∀ {A} (B P : 𝓟 A) → MPrel B P → EM A →  DeMorgan∀∃rel B P
-- MPrel→DMrel {A} B P MPBP (in1 x) ¬B⊆P  = {!   !}
-- MPrel→DMrel {A} B P MPBP (in2 ¬x) ¬B⊆P = {!   !}
-- -- MPrel→DMrel B P MPBP WEM ¬B⊆P with MPBP (λ x Bx → in2 λ Px → ¬B⊆P (λ x₁ x₂ → {!   !})) {!   !}
-- -- ... | y ,, By , Py = y ,, By , λ Py → ¬B⊆P λ x Bx → {!   !}

{-
-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
DeMorgan∀∃→DeMorgan∀∃rel : {A : Set} → (B P : 𝓟 A) → DeMorgan∀∃ A → DeMorgan∀∃rel B P
DeMorgan∀∃→DeMorgan∀∃rel {A} B P DeMorg ¬B⊆P with DeMorg {!   !} (λ x→Px → ¬B⊆P (λ x x∈B → x→Px x))
... | x ,, ¬Px = x ,, ( {!   !} , ¬Px) -- (∅ (¬B⊆P {!   !}) , ¬Px)

¬ind→step : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ
             → (∀ x → DeMorgan∀∃rel (~R R x) φ)
             → ∀ x → ¬ φ x → Σ[ y ∈ A ] (~R R x y × ¬ φ y)
¬ind→step R φ φ-ind DeMorg x ¬φx = DeMorg x (λ ↓x⊆φ → ¬φx (φ-ind x ↓x⊆φ ) )

¬ind→seq1 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → ¬ φ x
              → ℕ → A
¬ind→seq2 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → (∀ n → ¬ φ (¬ind→seq1 {A} R φ φ-ind DeMorg x ¬φx n))
¬ind→seq3 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → is R -decreasing (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)

¬ind→seq1 R φ φ-ind DeMorg x ¬φx zero = x
¬ind→seq1 R φ φ-ind DeMorg x ¬φx (succ n) = fst (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n))

¬ind→seq2 R φ φ-ind DeMorg x ¬φx  zero = ¬φx
¬ind→seq2 R φ φ-ind DeMorg x ¬φx (succ n) = pr2 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

-- Not mutually recursive with seq1 and seq2
¬ind→seq3 R φ φ-ind DeMorg x ¬φx n = pr1 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

-- ¬ind→seq = ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) →

WFisWFseq- : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → isWFseq R → is R -inductive φ → (¬¬Closed φ)
                → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → φ x
WFisWFseq- R φ RisWFseq φ-ind DNEφ DeMorg x = DNEφ x
  (λ ¬φx → RisWFseq (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)
                    (¬ind→seq3 R φ φ-ind DeMorg x ¬φx) )

-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
-- Question: Does either of them imply ¬¬Closed φ (possibly using φ is R-inductive)
-- NOT PROVABLE!
DeMorgan∀∃rel→¬¬Closed : ∀ {A} → (B P : 𝓟 A) → DeMorgan∀∃rel B P → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed B P DeMorgRel x ¬¬Bx with DeMorgRel (λ B⊆P →  ¬¬Bx λ Bx → {!   !})
... | y ,, By , ¬Py = {!   !}

DeMorgan∀∃rel→¬¬Closed2 : ∀ {A} → (B : 𝓟 A) → (H : ∀ (P : 𝓟 A) → DeMorgan∀∃rel B P) → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed2 = {!   !}
-}

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg (λ x → ¬¬ (B x) → B x) (λ H → ¬¬Bx (λ Bx → {!   !} ))
-- ... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg B (λ x→Bx → ¬¬Bx (λ Bx → {!   !}))

-- Question: If φ is decidable, does the implication WF→WFseq follow automatically.

-- is_-minimal_ : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S
-- -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
-- is R -minimal {S} x = ∀ y → R y x → ⊥

-- weaklyBounded : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S → Set
-- weaklyBounded R A = Σ[ a ∈ A ] → is R -minimal a

{-
module A18Constructive where

  is_-_-minimal_ : ∀ {S : Set} (R : 𝓡 S) (A : 𝓟 S) → 𝓟 S
  -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
  is R - A -minimal x = x ∈ A × (∀ y → y ∈ A → R y x → ⊥)

  lemmaA18φ : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
  lemmaA18φ S R A x = (x ∈ A) → Σ[ y ∈ S ] (is R - A -minimal y)

  -- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

  A18←seq : ∀ {S : Set} (R : 𝓡 S) → (∀ (A : 𝓟 S) → nonEmpty A → Σ[ x ∈ S ] (x ∈ A × is R - A -minimal x))
           → isWFseq R
  A18←seq R H s s-dec with H (λ x → Σ[ n ∈ ℕ ] (s n ≡ x)) ((s zero ,, zero ,, refl ))
  ... | x ,, (n ,, sn≡x) , ((m ,, sm=x) , p) = p (s (succ n)) (succ n ,, refl ) (transp (R (s (succ n))) sn≡x (s-dec n) )

  A18← : ∀ {S : Set} (R : 𝓡 S) → (∀ (A : 𝓟 S) → nonEmpty A → Σ[ x ∈ S ] (x ∈ A × is R - A -minimal x))
           → ∀ φ → is R -inductive φ → ∀ x → ¬¬ φ x
  -- A18← R H φ φ-ind x ¬φx =

  A18← R H φ φ-ind x ¬φx with H (λ z → ¬ φ z) ((x ,, ¬φx))
  ... | y ,, ¬φy , (_ , pr4) = ¬φy (φ-ind y λ z Rzy → φ-ind z {!   !} )

  A18→ : ∀ {S : Set} (R : 𝓡 S) → isWFind R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
           → ¬¬ Σ[ y ∈ S ] is R - A -minimal y
  A18→ {S} R WFR A x x∈A ¬miny =
    let φ    = λ y → y ∈ A → ∀ z → z ∈ A → ¬¬ R z y
        -- φ₂ : 𝓟 S
        -- φ₂ = λ z → (R z z) → ⊥
        WFRφ : is R -inductive φ
        WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, (y∈A , (λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A y1 y1∈A
                                               λ _ →  H y1 Ry1y y1∈A y1 y1∈A
                                                    (WFR (λ z → (x : R z z) → ⊥) (λ w H₂ Rww → H₂ w Rww Rww) y1))))
        -- WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, y∈A , λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A z z∈A (λ Rzy1 → H y1 Ry1y y1∈A z z∈A {!     !} ) )
        -- WFRφ₂ : is R -inductive φ₂
        -- WFRφ₂ y H Rxx = H y Rxx Rxx
     in  WFR φ WFRφ x x∈A x x∈A (WFR (λ z → (x : R z z) → ⊥) (λ x z x₁ → z x x₁ x₁) x)
-}


-- ↓R-dec : ∀ (S : Set) (R : 𝓡 S) → 𝓟 S
-- ↓R-dec S R x = ¬ (∀ y → ¬ R y x) → Σ[ y ∈ S ] R y x

-- lemmaA18 : ∀ S R A → (∀ a → ↓R-dec S R a) → is R -inductive (lemmaA18φ S R A) -- (λ _ → Σ S (is R - A -minimal_)) -- this is quite messy. don't really understand what I have
-- lemmaA18 S R A ↓Rdec x H x∈A with ↓Rdec x {!   !}
-- ... | y ,, Ryx = {!   !}
-- lemmaA18 {S} R {A} x H with H x {!   !}
-- ... | y ,, Ay , H2 = y ,, Ay , H2

-- A.1.8
-- A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
--          → Σ[ y ∈ S ] is R - A -minimal y
-- A18→ {S} R WFR A x x∈A =
--   let WFRφ = WFR (lemmaA18φ S R A) (lemmaA18 S R A ?) x
--    in WFRφ x∈A -- pr2 WFRφ
-- A18→ {S} R WFR A a a∈A = pr2 (WFR φ {!   !} a ) where
--               φ : S → Set
--               φ x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)


-- A18→ {S} R WFR A a a∈A = WFR φ (lemmaA18 R) a where   -- (λ _ → Σ S (is_-_-minimal_ R A))
--                         φ : (x : S) → Set
--                         φ = λ _ → Σ S (is R - A -minimal_ )
  -- Hint. Use WFR with φ x := x ∈ A → Σ[ y ∈ A ] (is R - A -minimal y)
  -- Try to prove this φ is R-inductive.
  -- Otherwise, try φ x := x ∈ A × Σ[ y ∈ A ] (is R - A -minimal y)
-- A18→ R WFR x y Ryx = WFR (λ x₁ → ⊥) (λ x₁ h → h y {!   !}) x

-- For the converse, try to prove "Every non-empty A contains a R-minimal element" → "isWFseq R"





-- The End
