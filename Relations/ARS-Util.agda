open import Relations.Relations
open import Predicates
open import Logic

module Relations.ARS-Util {A : Set } {R : 𝓡 A} where

open import Relations.ARS-Properties {A}
open LocalProperties {R}
open import Relations.ARS-Base

{- This file contains utility functions used throughout the ARS formalization
 which do not cleanly fit within a particular theme-}

NF→ε : ∀ {x : A} → x ∈ NF → ∀ {y} → (R ⋆) x y → x ≡ y
NF→ε {x} x∈NF {.x} ε⋆ = refl
NF→ε {x} x∈NF {y} (Rxy₀ ,⋆ R⋆y₀y) = ∅ (x∈NF Rxy₀)

¬¬NF⊆NF : ∀ x → ¬¬ (NF x) → NF x
¬¬NF⊆NF x nnNFx  Rxy = nnNFx (λ x∈NF → x∈NF Rxy)



weakly-confluent→WCR : weakly-confluent R → R isWCR
weakly-confluent→WCR x x₁ x₂ x₃ = x (x₁ ,, x₂ , x₃)

WCR→weakly-confluent : R isWCR → weakly-confluent R
WCR→weakly-confluent RisWCR (x ,, Rxy , Rxz) = RisWCR x Rxy Rxz

CR→confluent : R isCR → confluent R
CR→confluent RisCR (x ,, R*xy , R*xz)  with RisCR x R*xy R*xz
... | RisConfluent = RisConfluent

-- move to implications
WCR∧SNx→WNFPx : R isWCR → SN ⊆ WNFP
WCR∧SNx→WNFPx RisWCR x x∈SN y∈NF ε⋆ ε⋆ = ε⋆
WCR∧SNx→WNFPx RisWCR x x∈SN y∈NF ε⋆ (Rxx₀ ,⋆ R*x₀z) = ∅ (y∈NF Rxx₀)
WCR∧SNx→WNFPx RisWCR x x∈SN y∈NF (Rxy₀ ,⋆ R*y₀y) ε⋆ = Rxy₀ ,⋆ R*y₀y
WCR∧SNx→WNFPx RisWCR x (acc xacc) y∈NF (Rxy₀ ,⋆ R*y₀y) (Rxz₀ ,⋆ R*z₀z) with RisWCR x Rxy₀ Rxz₀
... | w ,, R*y₀w , R*z₀w with WCR∧SNx→WNFPx RisWCR  _ (xacc _ Rxy₀) y∈NF R*y₀y R*y₀w
... | R*wy = WCR∧SNx→WNFPx RisWCR _ (xacc _ Rxz₀) y∈NF (R*z₀w ⋆!⋆ R*wy) R*z₀z

-- Move to implications
WCR∧SNx→UNx : R isWCR → ∀ (x : A) → SN x → UN x
WCR∧SNx→UNx RisWCR x x∈SN y∈NF z∈NF R*xy R*xz with WCR∧SNx→WNFPx RisWCR x x∈SN y∈NF R*xy R*xz
... | R*zy = ~ (NF→ε z∈NF R*zy)

-- Move to implications
CR→WCR : R isCR → R isWCR
CR→WCR RisCR x Rxy Rxz = RisCR x (Rxy ,⋆ ε⋆) (Rxz ,⋆ ε⋆)



open ClassicalImplications using (decMin; isMinDec-)

SNdec→WN : decMin (~R R) → SN ⊆ WN
SNdec→WN decR x (acc accx) with decR x
... | in2 y∈NF = x ,, (ε⋆ , y∈NF _)
... | in1 (y ,, Rxy) with SNdec→WN decR y (accx y Rxy)
... | (n ,, R*yn , n∈NF) = n ,, (Rxy ,⋆ R*yn) , n∈NF


WN→isMinDec- : ∀ (x : A) → x ∈ WN  → isMinDec- (~R R) x
WN→isMinDec- x (.x ,, ε⋆ , n∈NF) x∉NF = ∅ (x∉NF (λ y → n∈NF))
WN→isMinDec- x (n ,, (_,⋆_ {y = y} Rxy R*yn) , n∈NF) x∉NF = y ,, Rxy

SN⊆∁∁WN : SN ⊆ ∁ (∁ WN)
SN⊆∁∁WN x (acc xacc) ¬WNx = ¬WNx (x ,, ε⋆ , x∈NF _) where
    x∈NF : ∀ y → ¬ R x y
    x∈NF y Rxy = SN⊆∁∁WN y (xacc y Rxy)
            (λ { (n ,, (R*yn , n∈NF)) → ¬WNx ((n ,, (Rxy ,⋆ R*yn) , n∈NF )) } )
