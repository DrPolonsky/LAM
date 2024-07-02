open import Predicates

module ClosureOperators {A : Set} (R : 𝓡 A) where

open import Logic-Levels
open import RelationsCore
open import Wellfounded

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
