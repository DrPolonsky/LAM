open import Relations.Relations
open import Predicates
open import Logic

module Relations.ARS-NewmansLemma {A : Set } (R : 𝓡 A) where

open import Relations.ARS-Properties {A}
open LocalProperties {R}

{-This file contains formalizations of Newman's lemma and variants-}

module Newmans-Lemma where

    wCR→conflInd : R isWCR → is (~R R) -inductive CR
    wCR→conflInd RisWCR x IND ε⋆ R*xz = _ ,, R*xz , ε⋆
    wCR→conflInd RisWCR x IND (Rxy₀ ,⋆ R*y₀y) ε⋆ = _ ,, ε⋆ , (Rxy₀ ,⋆ R*y₀y)
    wCR→conflInd RisWCR x IND (Rxy₀ ,⋆ R*y₀y) (Rxz₀ ,⋆ R*z₀z) with RisWCR x Rxy₀ Rxz₀
    ... | w ,, R*y₀w , R*z₀w with IND _ Rxy₀ R*y₀y R*y₀w
    ... | v ,, R*yv , R*wv with IND _ Rxz₀ R*z₀z (R*z₀w ⋆!⋆ R*wv)
    ... | u ,, R*zu , R*vu = u ,, ((R*yv ⋆!⋆ R*vu) , R*zu)

    wCR→Conf : R isWCR → SN ⊆ CR
    wCR→Conf RisWCR = acc⊆ind (~R R) (λ x → CR x) (wCR→conflInd RisWCR)

    NewmansLemma : R isSN → R isWCR → R isCR
    NewmansLemma RisSN RisWCR x R*xy R*xz = wCR→Conf RisWCR x (RisSN x) R*xy R*xz

module Newmans-Lemma-SM where
    LocalNewmansLemmaRecurrent : R isWCR → SM ⊆ CR
    LocalNewmansLemmaRecurrent RisWCR x (SMrec .x x∈Rec) R*xy R*xz = x ,, x∈Rec _ R*xy , x∈Rec _ R*xz           -- Start by casing on SR. Recurrent case is simple
    LocalNewmansLemmaRecurrent RisWCR x (SMacc .x x∈Acc) ε⋆ R*xz = _ ,, R*xz , ε⋆                               -- Then case on the reductions, ε⋆ cases are simple
    LocalNewmansLemmaRecurrent RisWCR x (SMacc .x x∈Acc) (Rxy₁ ,⋆ R*y₁y) ε⋆ = _ ,, ε⋆ , (Rxy₁ ,⋆ R*y₁y)
    LocalNewmansLemmaRecurrent RisWCR x (SMacc .x x∈Acc) (Rxy₁ ,⋆ R*y₁y) (Rxz₁ ,⋆ R*z₁z)                        -- Now apply WCR to get common reduct w
                with RisWCR x Rxy₁ Rxz₁
    ... | w ,, R*y₁w , R*z₁w  with LocalNewmansLemmaRecurrent RisWCR _ (x∈Acc _ Rxy₁) R*y₁y R*y₁w               -- Recursive twice
    ... | y₂ ,, R*yy₂ , R*wy₂ with LocalNewmansLemmaRecurrent RisWCR _ (x∈Acc _ Rxz₁) R*z₁z (R*z₁w ⋆!⋆ R*wy₂)
    ... | z₂ ,, R*zz₂ , R*y₂z₂ = z₂ ,, ((R*yy₂ ⋆!⋆ R*y₂z₂) , R*zz₂)

    GlobalNewmansLemmaRecurrent : R isWCR → R isSM → R isCR
    GlobalNewmansLemmaRecurrent RisWCR RisSM x = LocalNewmansLemmaRecurrent RisWCR x (RisSM x)
