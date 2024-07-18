{-# OPTIONS --allow-unsolved-metas #-}
module Relations.ClosureOperators {U : Set}  where

open import Logic-Levels
open import Predicates
open import Relations.Core

module ClosureDefinitions where
  --reflexive closure
  data _ʳ (R : 𝓡 U) : 𝓡 U where
    axʳ : ∀ {x y : U} → R x y → (R ʳ) x y
    εʳ  : ∀ {x} → (R ʳ) x x

  -- symmetric closure
  data _ˢ (R : 𝓡 U) : 𝓡 U where
    axˢ+ : ∀ {x y} → R x y → (R ˢ) x y
    axˢ- : ∀ {x y} → R y x → (R ˢ) x y

  -- Transitive closure
  data _⁺ (R : 𝓡 U) : 𝓡 U   where
    ax⁺  : ∀ {x y : U}   → R x y → (R ⁺) x y
    _,⁺_ : ∀ {x y z : U} → R x y → (R ⁺) y z → (R ⁺) x z

  -- Transitive closure, starting from the tail
  data _₊ (R : 𝓡 U) : 𝓡 U   where
    ax₊  : ∀ {x y : U}   → R x y → (R ₊) x y
    _₊,_ : ∀ {x y z : U} → (R ₊) x y → R y z → (R ₊) x z

  -- reflexive transitive closure
  -- ⋆ is \*
  data _⋆ (R : 𝓡 U) : 𝓡 U where
    ax⋆ : ∀ {x y : U} → R x y → (R ⋆) x y
    ε⋆  :  ∀ {x} → (R ⋆) x x
    _,⋆_ : ∀ {x y z} → R x y → (R ⋆) y z → (R ⋆) x z

  _⁼ : 𝓡 U → 𝓡 U
  R ⁼ = (R ˢ) ⋆

  infix 19 _ʳ
  infix 19 _ˢ
  infix 19 _⁺
  infix 19 _₊
  infix 19 _⋆
  infix 19 _⁼

open ClosureDefinitions public

module ClosureProperties where
  TCisTran : ∀ (R : 𝓡 U) {x y z : U} → (R ⋆) x y → (R ⋆) y z → (R ⋆) x z
  TCisTran R (ax⋆ x) R*yz = x ,⋆ R*yz
  TCisTran R ε⋆ R*yz = R*yz
  TCisTran R (x ,⋆ R*xy) R*yz = x ,⋆ (TCisTran R R*xy R*yz)

  TCisSym : ∀ {R : 𝓡 U} {x y : U} → ((R ˢ) ⋆) x y → ((R ˢ) ⋆) y x
  TCisSym (ax⋆ (axˢ+ x)) = ax⋆ ((axˢ- x))
  TCisSym (ax⋆ (axˢ- x)) = ax⋆ ((axˢ+ x))
  TCisSym ε⋆ = ε⋆
  TCisSym {R} (axˢ+ x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym rxy) (axˢ- x ,⋆ ε⋆ )
  TCisSym {R} (axˢ- x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym rxy) (axˢ+ x ,⋆ ε⋆ )

  SymisSym : ∀ {R : 𝓡 U} {x y : U} → (R ˢ) x y → (R ˢ) y x
  SymisSym (axˢ+ Rxy) = axˢ- Rxy
  SymisSym (axˢ- Ryx) = axˢ+ Ryx

  *⊆EQ : ∀ {R : 𝓡 U} {x y : U} → (R ⋆) x y → (R ⁼) x y
  *⊆EQ (ax⋆ Rxy) = ax⋆ (axˢ+ Rxy)
  *⊆EQ ε⋆ = ε⋆
  *⊆EQ (Rxy₁ ,⋆ R*y₁y) = axˢ+ Rxy₁ ,⋆ *⊆EQ R*y₁y

  s⊆EQ : ∀ {R : 𝓡 U} {x y : U} → (R ˢ) x y → (R ⁼) x y
  s⊆EQ (axˢ+ Rxy) = ax⋆ (axˢ+ Rxy)
  s⊆EQ (axˢ- Ryx) = ax⋆ (axˢ- Ryx)

  EQisTran : ∀ {R : 𝓡 U} {x y z : U} → (R ⁼) x y → (R ⁼) y z → (R ⁼) x z
  EQisTran (ax⋆ Rˢxy) EQRyz = Rˢxy ,⋆ EQRyz
  EQisTran ε⋆ EQRyz = EQRyz
  EQisTran (Rˢxy₁ ,⋆ EQRy₁y) EQRyz = Rˢxy₁ ,⋆ EQisTran EQRy₁y EQRyz

  EQisSym : ∀ {R : 𝓡 U} {x y : U} → (R ⁼) x y → (R ⁼) y x
  EQisSym (ax⋆ Rˢxy) = s⊆EQ (SymisSym Rˢxy)
  EQisSym ε⋆ = ε⋆
  EQisSym (Rˢxy₁ ,⋆ Rˢ*y₁y) = EQisTran (EQisSym Rˢ*y₁y) (s⊆EQ (SymisSym Rˢxy₁))

open ClosureProperties public

module ClosureTransformations (R : 𝓡 U) where
  **→* : ∀ {x y} → ((R ⋆) ⋆) x y → (R ⋆) x y
  **→* (ax⋆ R*xy) = R*xy
  **→* ε⋆ = ε⋆
  **→* (R*xy ,⋆ R**yz) =  TCisTran R R*xy (**→* R**yz)

  **→*ʳ : ∀ {x y : U} → ((R ⋆)⋆) x y → ((R ⋆)ʳ) x y
  **→*ʳ = axʳ ∘ **→*

  *ʳ→* : ∀ {x y : U} → ((R ⋆)ʳ) x y → (R ⋆) x y
  *ʳ→* (axʳ R*xy) = R*xy
  *ʳ→* εʳ = ε⋆

  ~⁺ : ∀ {x y z : U} → (R ⁺) x y → R y z → (R ⁺) x z
  ~⁺ (ax⁺ Rxy) Ryz = Rxy ,⁺ ax⁺ Ryz
  ~⁺ (Rxy₁ ,⁺ R⁺b₁c) Ryz = Rxy₁ ,⁺ ~⁺ R⁺b₁c Ryz

  ~₊ : ∀ {x y z : U} → R x y → (R ₊) y z → (R ₊) x z
  ~₊ Rxy (ax₊ Ryz) = ax₊ Rxy ₊, Ryz
  ~₊ Rxy (R₊xy ₊, Ryz) = ~₊ Rxy R₊xy ₊, Ryz

  TC⁺⇔TC₊ : R ⁺ ⇔ R ₊
  TC⁺⇔TC₊ = ⁺⊆₊ , ₊⊆⁺ where
    ⁺⊆₊ : R ⁺ ⊆ R ₊
    ⁺⊆₊ x y (ax⁺ Rxy) = ax₊ Rxy
    ⁺⊆₊ x y (Rxy ,⁺ R⁺yz) = ~₊ Rxy (⁺⊆₊ _ y R⁺yz)
    ₊⊆⁺ : R ₊ ⊆ R ⁺
    ₊⊆⁺ x y (ax₊ Rxy) = ax⁺ Rxy
    ₊⊆⁺ x y (R₊xy ₊, Ryz) = ~⁺ (₊⊆⁺ x _ R₊xy) Ryz

  ⁺→⋆ : ∀ {x y : U} → (R ⁺) x y →  (R ⋆) x y
  ⁺→⋆ (ax⁺ Rxy) = ax⋆ Rxy
  ⁺→⋆ (Rxy₁ ,⁺ R⁺bb₁) = Rxy₁ ,⋆ ⁺→⋆ R⁺bb₁

  TransitiveClosure :  R ⋆ ⇔ (R ⁺ ∪ R ʳ)
  TransitiveClosure = TC+ , TC- where
    TC+ : (R ⋆) ⊆ (R ⁺) ∪ (R ʳ)
    TC+ x y (ax⋆ Rxy) = in1 (ax⁺ Rxy )
    TC+ x .x ε⋆ = in2 εʳ
    TC+ x y (Rxy₁ ,⋆ R⋆y₁y) = in1 (case (_,⁺_ Rxy₁) -- (λ R⁺y₁y → (Rxy₁ ,⁺ R⁺y₁y))
                                      (λ { (axʳ Ry₁y) → (Rxy₁ ,⁺ (ax⁺ Ry₁y)) ; εʳ → ax⁺ Rxy₁})
                                      (TC+ _ _ R⋆y₁y))
    TC- : (R ⁺) ∪ (R ʳ) ⊆ (R ⋆)
    TC- x y (in1 (ax⁺ Rxy)) = ax⋆ Rxy
    TC- x y (in1 (Rxy₁ ,⁺ R⁺y₁y)) = Rxy₁ ,⋆ ⁺→⋆ R⁺y₁y
    TC- x y (in2 (axʳ Rxy)) = ax⋆ Rxy
    TC- a .a (in2 εʳ) = ε⋆

open ClosureTransformations public

module ClosureOpsPreserveContainment {R1 R2 : 𝓡 U} (R12 : R1 ⊆ R2) where

  ⊆ʳ : R1 ʳ ⊆ R2 ʳ
  ⊆ʳ x y (axʳ R1xy) = axʳ (R12 x y R1xy)
  ⊆ʳ x .x εʳ = εʳ

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

  ⊆⁼ : R1 ⁼ ⊆ R2 ⁼
  ⊆⁼ x .x ε⋆ = ε⋆
  ⊆⁼ x y (ax⋆ R1ˢxy) = ax⋆ (⊆ˢ x y R1ˢxy)
  ⊆⁼ x y (R1ˢxy₁ ,⋆ R1⁼y₁y) =  ⊆ˢ x _ R1ˢxy₁ ,⋆  ⊆⁼ _ y R1⁼y₁y
open ClosureOpsPreserveContainment public

module ClosureOpsPreserveEquivalence {R1 R2 : 𝓡 U} (R12 : R1 ⇔ R2) where

  ⇔ʳ : R1 ʳ ⇔ R2 ʳ
  pr1 ⇔ʳ x y (axʳ R1xy) = axʳ (pr1 R12 x y R1xy)
  pr1 ⇔ʳ x .x εʳ = εʳ
  pr2 ⇔ʳ x y (axʳ R2xy) = axʳ (pr2 R12 x y R2xy)
  pr2 ⇔ʳ x .x εʳ = εʳ

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

  ⇔⁼ : R1 ⁼ ⇔ R2 ⁼ 
  pr1 ⇔⁼ x .x ε⋆ = ε⋆
  pr1 ⇔⁼ x y (ax⋆ R1ˢxy) = ax⋆ (pr1 ⇔ˢ x y R1ˢxy)  
  pr1 ⇔⁼ x y (R1ˢxy₁ ,⋆ R1⁼y₁y) = (pr1 ⇔ˢ x _ R1ˢxy₁) ,⋆ pr1 ⇔⁼ _ y R1⁼y₁y 
  pr2 ⇔⁼ x .x ε⋆ = ε⋆
  pr2 ⇔⁼ x y (ax⋆ R2ˢxy) = ax⋆ (pr2 ⇔ˢ x y R2ˢxy)
  pr2 ⇔⁼ x y (R2ˢxy₁ ,⋆ R2⁼y₁y) = (pr2 ⇔ˢ x _ R2ˢxy₁) ,⋆ pr2 ⇔⁼ _ y R2⁼y₁y   