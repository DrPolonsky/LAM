
open import Relations.Relations
open import Relations.ARS
open import Predicates
open import Logic
open import Datatypes using (ℕ ; zero; succ; Fin)

module Relations.Implications {A : Set} {R : 𝓡 A} where


module Definitions where
    -- Weakly recurrent
    is_-WR_ : 𝓟 A
    is_-WR_ x = Σ[ r ∈ A ] ((R ⋆) x r × is R -recurrent r)

    -- Strongly recurrent
    is_-SR_ : 𝓟 A
    is_-SR_ x = ∀ (f : ℕ → A) → f zero ≡ x → is R -increasing f → Σ[ i ∈ ℕ ] (is R -recurrent (f i))

    -- Alternative definition. Every infinite sequence hits a recurrent term
    is_-SRv2_ : 𝓟 A
    is_-SRv2_ x = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → Σ[ i ∈ ℕ ] (is R -recurrent (f i))

    -- RP: like WNFP but for recurrent terms
    -- A term is recurrent iff in the reduction graph for that term is strongly connected
    -- Equivalently, the transitive-reflexive closure of the reduction relation R
    -- is symmetric (when restricted to the terms reachable from x).
    is_-RP_ : 𝓟 A
    is_-RP_ x = ∀ {y z} → is R -recurrent y → (R ⋆) x y → (R ⋆) x z → (R ⋆) z y

    -- Weak normal form property (denoted NP in notes)
    is_-WNFP_ : 𝓟 A
    is_-WNFP_ x = ∀ {y z} → is R -NF y → (R ⋆) x y → (R ⋆) x z → (R ⋆) z y

open Definitions public

module Basic-Implications where

    CR→RP : ∀ {x} → is R -CR x → is_-RP_ x
    CR→RP isR_CR_x isR_rec_y R*xy R*xz with isR_CR_x R*xy R*xz
    ... | q ,, (R*yq , R*zq) with isR_rec_y q R*yq
    ... | R*qy = R*zq ⋆!⋆ R*qy

    -- Normal form is a subset of recurrence
    NF⊆Rec : ∀ {x} → is R -NF x → is R -recurrent x
    NF⊆Rec isNF_x y ε⋆ = ε⋆
    NF⊆Rec isNF_x y (Rxx₁ ,⋆ R*x₁y) = ∅ (isNF _ x Rxx₁)

    RP→NP : ∀ {x} → is_-RP_ x → is_-WNFP_ x
    RP→NP isRec_x isNF_y R*xy R*xz = isRec_x (NF⊆Rec isNF_y) R*xy R*xz

    NP→UN : ∀ {x} → is_-WNFP_ x → is R -UN x
    NP→UN isNP_x isNF_y isNF_z R*xy R*xz with isNP_x isNF_y R*xy R*xz
    ... | ε⋆ = refl
    ... | Rzz₁ ,⋆ R*z₁y = ∅ (isNF _ z Rzz₁)

    SN→SR : ∀ {x} → is R -SN x → is_-SR_ x
    SN→SR (acc accx) f refl fisRinc
      with SN→SR (accx (f (succ zero)) (fisRinc zero)) (λ m → f (succ m)) refl
                 (λ n → fisRinc (succ n) )
    ... | (k ,, H) = (succ k ,, H )

    SN→WN∧SR : ∀ {x} → is R -SN x → (is R -WN x × is_-SR_ x)
    SN→WN∧SR (acc accx) = {!   !} -- We'll need dec min here

    SR→WR : ∀ {x} → is_-SR_ x → is_-WR_ x
    SR→WR isSR_x = {!   !}

    SR2→WR : ∀ {x} → is_-SRv2_ x → is_-WR_ x
    SR2→WR isSR_x = {!   !}

    WN→WR : ∀ {x} → is R -WN x → is_-WR_ x
    WN→WR (y ,, (R*xy , isNF_y)) = y ,, (R*xy , (NF⊆Rec isNF_y))

open Basic-Implications public

module Normalizing-Implications where

    WN∧NP→SR : ∀ {x} → is R -WN x → is_-WNFP_ x → is_-SR_ x
    WN∧NP→SR isWN_x isNP_x R*xy = {!   !}  -- Hold off on this until we agree on a defn of SR

    WN∧NP→SN : ∀ {x} → is R -WN x → is_-WNFP_ x → is R -SN x -- I think this might hold. As always, proving something is SN is a pain. Why not define SN as for all reductions from x, those reductions are WN?
    WN∧NP→SN (n ,, (R*xn , isNF_n)) isNP_x with isNP_x isNF_n R*xn
    ... | R*_n = acc ({!   !})


module Confluent-Implications where

    WR∧RP→CR : ∀ {x} → is_-WR_ x → is_-RP_ x → is R -CR x
    WR∧RP→CR (q ,, (R*xq , isRec_q)) isRP_x R*xy R*xz = q ,, isRP isRec_q x R*xq R*xy , isRP isRec_q x R*xq R*xz

    WN∧NP→CR : ∀ {x} → is R -WN x → is_-WNFP_ x → is R -CR x
    WN∧NP→CR (n ,, (R*xn , isNF_x)) isWNFP_x R*xy R*xz = n ,, isWNFP isNF_x x R*xn R*xy , isWNFP isNF_x x R*xn R*xz



    SN∧UN→CR : ∀ {x} → is R -SN x → is R -UN x → is R -CR x
    SN∧UN→CR isSN_x isUN_x R*xy R*xz = {!   !}
