{-# OPTIONS --allow-unsolved-metas #-}
module ClosureOperators {U : Set} where

open import Logic-Levels
open import Predicates
open import RelationsCore

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

lemma**→* : ∀ {a b : A} →  ((R ⋆) ⋆) a b → (R ⋆) a b  -- Rename this to TCisTC in ClosureOperators?
lemma**→* (ax⋆ R*ab) = R*ab
lemma**→* ε⋆ = ε⋆
lemma**→* (R*ay ,⋆ R**yb) = TCisTran R R*ay (lemma**→* R**yb)

lemma**→*⁼ : ∀ {a b : A} → ((R ⋆)⋆) a b → ((R ⋆)⁼) a b
lemma**→*⁼ = ax⁼ ∘ lemma**→*

lemma*=→* : ∀ {a b : A} → ((R ⋆)⁼) a b → (R ⋆) a b
lemma*=→* (ax⁼ R*ab) = R*ab
lemma*=→* ε⁼ = ε⋆

lemmaSymisSym : ∀ {a b : A} → (R ˢ) a b → (R ˢ) b a
lemmaSymisSym (axˢ+ Rab) = axˢ- Rab
lemmaSymisSym (axˢ- Rba) = axˢ+ Rba

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

lemma⁺→⋆ : ∀ {x y : U} {R : 𝓡 U} → (R ⁺) x y →  (R ⋆) x y
lemma⁺→⋆ (ax⁺ Rxy) = ax⋆ Rxy
lemma⁺→⋆ (Rxy₁ ,⁺ R⁺yy₁) = Rxy₁ ,⋆ lemma⁺→⋆ R⁺yy₁

TransitiveClosure :  ∀ {R : 𝓡 U} → R ⋆ ⇔ (R ⁺ ∪ R ⁼)
TransitiveClosure {R} = TC+ , TC- where
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

module ClosureOpsPreserveContainment {R1 R2 : 𝓡 U} (R12 : R1 ⊆ R2) where

  ⊆⁼ : R1 ⁼ ⊆ R2 ⁼
  ⊆⁼ x y (ax⁼ R1xy) = ax⁼ (R12 x y R1xy)
  ⊆⁼ x .x ε⁼ = ε⁼

  ⊆ˢ : R1 ˢ ⊆ R2 ˢ
  ⊆ˢ x y (axˢ+ R1xy) = axˢ+ (R12 x y R1xy)
  ⊆ˢ x y (axˢ- R1yx) = axˢ- (R12 y x R1yx)

  ⊆⁺ : R1 ⁺ ⊆ R2 ⁺
  ⊆⁺ x y (ax⁺ R1xy) = ax⁺ (R12 x y R1xy)
  ⊆⁺ x y (R1xy ,⁺ R1⁺yz) = (R12 x _ R1xy) ,⁺ (⊆⁺ _ y R1⁺yz)

  ⊆₊ : R1 ₊ ⊆ R2 ₊
  ⊆₊ = (pr2 (TC⁺⇔TC₊ R1)) ⊆!⊆₂
                     (⊆⁺ ⊆!⊆₂ (pr1 (TC⁺⇔TC₊ R2)))

  ⊆⋆ : R1 ⋆ ⊆ R2 ⋆
  ⊆⋆ x y (ax⋆ Rxy) = ax⋆ (R12 x y Rxy)
  ⊆⋆ x .x ε⋆ = ε⋆
  ⊆⋆ x y (R1xy ,⋆ R2⋆yz) = (R12 x _ R1xy) ,⋆ ⊆⋆ _ y R2⋆yz

module ClosureOpsPreserveEquivalence {R1 R2 : 𝓡 U} (R12 : R1 ⇔ R2) where

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

  ⊆₊ : R1 ₊ ⊆ R2 ₊
  ⊆₊ = (pr2 (TC⁺⇔TC₊ R1)) ⊆!⊆₂
                     (pr1 ⇔⁺ ⊆!⊆₂ (pr1 (TC⁺⇔TC₊ R2)))

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
