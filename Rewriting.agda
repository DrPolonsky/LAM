module Rewriting (𝔸 : Set) where

open import Logic
open import Relations

data 𝕋 : Set where
  atom : 𝔸 → 𝕋
  _⇒_  : 𝕋 → 𝕋 → 𝕋

-- 𝓡 𝕋 is the type of relations on 𝕋

data ⇒C (R : 𝓡 𝕋) : 𝓡 𝕋 where
  ax⇒C : ∀ {A B : 𝕋} → R A B → ⇒C R A B
  atom⇒C : ∀ {a : 𝔸} → ⇒C R (atom a) (atom a)
  ⇒CR : ∀ {A1 A2 B1 B2 : 𝕋} → ⇒C R A1 A2 → ⇒C R B1 B2 → ⇒C R (A1 ⇒ B1) (A2 ⇒ B2)

refl⇒C : ∀ (R : 𝓡 𝕋) (A : 𝕋) → ⇒C R A A
refl⇒C R (atom x) = atom⇒C
refl⇒C R (A ⇒ B) = ⇒CR (refl⇒C R A) (refl⇒C R B)

-- E ⊢ a = b  is  EL E a b
data EL (R : 𝓡 𝕋) : 𝓡 𝕋 where
  axEL : ∀ {A B : 𝕋} → R A B → EL R A B
  reflEL : ∀ {A : 𝕋} → EL R A A
  symmEL : ∀ {A B : 𝕋} → EL R A B → EL R B A
  tranEL : ∀ {A B C : 𝕋} → EL R A B → EL R B C → EL R A C
  congEL : ∀ {A1 A2 B1 B2 : 𝕋} → EL R A1 A2 → EL R B1 B2 → EL R (A1 ⇒ B1) (A2 ⇒ B2)

-- SC⇒C : ∀ (R : 𝓡 𝕋) {A B C D : 𝕋} → ((⇒C R) ˢ) A B → ((⇒C R) ˢ) C D → ((⇒C R) ˢ) (A ⇒ C) (B ⇒ D)
-- SC⇒C R (axˢ+ AB) (axˢ+ CD) = axˢ+ (⇒CR AB CD)
-- SC⇒C R (axˢ+ x) (axˢ- x₁) = {!   !}
-- SC⇒C R (axˢ- x) (axˢ+ x₁) = {!   !}
-- SC⇒C R (axˢ- x) (axˢ- x₁) = axˢ- (⇒CR x x₁)

SC⇒CL : ∀ (R : 𝓡 𝕋) {A1 A2} B → ((⇒C R) ˢ) A1 A2 → ((⇒C R) ˢ) (A1 ⇒ B) (A2 ⇒ B)
SC⇒CL R B (axˢ+ x) = axˢ+ (⇒CR x (refl⇒C R B))
SC⇒CL R B (axˢ- x) = axˢ- (⇒CR x (refl⇒C R B))

SC⇒CR : ∀ (R : 𝓡 𝕋) {A1 A2} B → ((⇒C R) ˢ) A1 A2 → ((⇒C R) ˢ) (B ⇒ A1) (B ⇒ A2)
SC⇒CR R B (axˢ+ x) = axˢ+ (⇒CR (refl⇒C R B) x)
SC⇒CR R B (axˢ- x) = axˢ- (⇒CR (refl⇒C R B) x)

TC⇒CL : ∀ (R : 𝓡 𝕋) {A1 A2} B → (((⇒C R) ˢ) ⋆) A1 A2 → (((⇒C R) ˢ) ⋆) (A1 ⇒ B) (A2 ⇒ B)
TC⇒CL R B (ax⋆ x) = ax⋆ (SC⇒CL R B x)
TC⇒CL R B ε⋆ = ε⋆
TC⇒CL R B (x ,⋆ A12) = SC⇒CL R B x ,⋆ TC⇒CL R B A12

TC⇒CR : ∀ (R : 𝓡 𝕋) {A1 A2} B → (((⇒C R) ˢ) ⋆) A1 A2 → (((⇒C R) ˢ) ⋆) (B ⇒ A1) (B ⇒ A2)
TC⇒CR R B (ax⋆ x) = ax⋆ (SC⇒CR R B x)
TC⇒CR R B ε⋆ = ε⋆
TC⇒CR R B (x ,⋆ A12) = SC⇒CR R B x ,⋆ TC⇒CR R B A12

EL⊆Conv : ∀ (R : 𝓡 𝕋) → EL R ⊆₂ EQ (⇒C R)
EL⊆Conv R x y (axEL Rxy) = ax⋆ (axˢ+ (ax⇒C Rxy ) )
EL⊆Conv R x .x reflEL = ε⋆
EL⊆Conv R x y (symmEL R⊢y=x) = TCisSym _ (EL⊆Conv R y x R⊢y=x)
EL⊆Conv R x y (tranEL R⊢x=y R⊢y=z) = TCisTran _ (EL⊆Conv R _ _ R⊢x=y) (EL⊆Conv R _ _ R⊢y=z)
EL⊆Conv R (A ⇒ B) (C ⇒ D) (congEL R⊢A=C R⊢B=D) =
  let recAC = EL⊆Conv R A C R⊢A=C
      recBD = EL⊆Conv R B D R⊢B=D
   in TCisTran (⇒C R ˢ) (TC⇒CL R B recAC) (TC⇒CR R C recBD)

⇒C⊆EL : ∀ (R : 𝓡 𝕋) → ⇒C R ⊆₂ EL R
⇒C⊆EL R x y (ax⇒C x₁) = axEL x₁
⇒C⊆EL R .(atom _) .(atom _) atom⇒C = reflEL
⇒C⊆EL R .(_ ⇒ _) .(_ ⇒ _) (⇒CR xy zw) = congEL (⇒C⊆EL R _ _ xy) (⇒C⊆EL R _ _ zw)

Conv⊆EL : ∀ (R : 𝓡 𝕋) → EQ (⇒C R) ⊆₂ EL R
Conv⊆EL R A B (ax⋆ (axˢ+ (ax⇒C x))) = axEL x
Conv⊆EL R .(atom _) .(atom _) (ax⋆ (axˢ+ atom⇒C)) = reflEL
Conv⊆EL R .(_ ⇒ _) .(_ ⇒ _) (ax⋆ (axˢ+ (⇒CR A12 B12))) = congEL (Conv⊆EL R _ _ (ax⋆ (axˢ+ (A12)))) (Conv⊆EL R _ _ (ax⋆ (axˢ+ (B12))))
Conv⊆EL R A B (ax⋆ (axˢ- (ax⇒C x))) = symmEL (axEL x)
Conv⊆EL R .(atom _) .(atom _) (ax⋆ (axˢ- atom⇒C)) = reflEL
Conv⊆EL R .(_ ⇒ _) .(_ ⇒ _) (ax⋆ (axˢ- (⇒CR B12 A12))) = congEL (Conv⊆EL R _ _ (ax⋆ (axˢ- (B12)))) (Conv⊆EL R _ _ (ax⋆ (axˢ- (A12))))
Conv⊆EL R A .A ε⋆ = reflEL
Conv⊆EL R A B (axˢ+ x ,⋆ A=B) = tranEL (⇒C⊆EL R _ _ x) (Conv⊆EL R _ _ A=B)
Conv⊆EL R A B (axˢ- x ,⋆ A=B) = tranEL (symmEL (⇒C⊆EL R _ _ x) ) (Conv⊆EL R _ _ A=B)
