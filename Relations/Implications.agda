
open import Relations.Relations
open import Relations.ARS
open import Predicates
open import Logic
open import Datatypes using (ℕ ; zero; succ; Fin)

module Relations.Implications {A : Set} (R : 𝓡 A) where

module Definitions where
    -- Weakly recurrent
    is_-WR_ : 𝓟 A
    is_-WR_ x = Σ[ r ∈ A ] ((R ⋆) x r × is R -recurrent r)

    -- Strongly recurrent
    data is_-SR_ : 𝓟 A where
      SRrec : ∀ x → is R -recurrent x → is_-SR_ x
      SRacc : ∀ x → (∀ y → R x y → is_-SR_ y) → is_-SR_ x

    is_-SRseq_ : 𝓟 A
    is_-SRseq_ x = ∀ (f : ℕ → A) → f zero ≡ x → is R -increasing f → Σ[ i ∈ ℕ ] (is R -recurrent (f i))

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
    NF⊆Rec x∈NF y ε⋆ = ε⋆
    NF⊆Rec x∈NF y (Rxx₁ ,⋆ R*x₁y) = ∅ (x∈NF _ Rxx₁)

    RP→NP : ∀ {x} → is_-RP_ x → is_-WNFP_ x
    RP→NP x∈Rec isNF_y R*xy R*xz = x∈Rec (NF⊆Rec isNF_y) R*xy R*xz

    NP→UN : ∀ {x} → is_-WNFP_ x → is R -UN x
    NP→UN isNP_x isNF_y isNF_z R*xy R*xz with isNP_x isNF_y R*xy R*xz
    ... | ε⋆ = refl
    ... | Rzz₁ ,⋆ R*z₁y = ∅ (isNF _ z Rzz₁)

    SN→SR : ∀ {x} → is R -SN x → is_-SRseq_ x
    SN→SR (acc accx) f refl fisRinc
      with SN→SR (accx (f (succ zero)) (fisRinc zero)) (λ m → f (succ m)) refl
                 (λ n → fisRinc (succ n) )
    ... | (k ,, H) = (succ k ,, H )

    WN→WR : ∀ {x} → is R -WN x → is_-WR_ x
    WN→WR (y ,, (R*xy , isNF_y)) = y ,, (R*xy , (NF⊆Rec isNF_y))

    open ClassicalImplications using (decMin)

    SN→WN∧SR : ∀ {x} → decMin (~R R) →  is R -SN x → (is R -WN x × is_-SRseq_ x)
    SN→WN∧SR {x} decMin x∈SN = (SNdec→WN R decMin x x∈SN) , (SN→SR x∈SN)

    decMin→SR→WR : ∀ {x} → decMin (~R R) → is_-SR_ x → is_-WR_ x
    decMin→SR→WR {x} dM (SRrec .x x∈Rec) = x ,, ε⋆ , x∈Rec
    decMin→SR→WR {x} dM (SRacc .x x∈SN) with dM x
    ... | in2 xIsMin = x ,, ε⋆ , λ { y ε⋆ → ε⋆ ; y (Rxz ,⋆ Ryz) → ∅ (xIsMin _ Rxz) }
    ... | in1 (y ,, Rxy) with decMin→SR→WR dM (x∈SN y Rxy)
    ...| (r ,, R*yr , r∈R) = r ,, (Rxy ,⋆ R*yr) , r∈R

open Basic-Implications public

module Normalizing-Implications where

    -- Rewriting UNlemma from ARS without decidability
    -- Try to do induction on x∈SN [not obvious?]
    SN∧UN→WN : ∀ x → is R -SN x → is R -UN x → is_-WNFP_ x
    SN∧UN→WN x isSN_x isUN_x isNF_y ε⋆ ε⋆ = ε⋆
    SN∧UN→WN x isSN_x isUN_x isNF_y ε⋆ (Rxx₁ ,⋆ R*x₁z) = ∅ (isNF _ y Rxx₁)
    SN∧UN→WN x isSN_x isUN_x isNF_y   (_,⋆_ {y = x₁}  Rxx₁  R*x₁y) R*xz = {!   !}

    WN∧SR∧NP→SN : ∀ x → is R -WN x → is R -UN x → is_-SR_ x → is R -SN x  -- SA: I don't think this holds due to CE-6
    WN∧SR∧NP→SN x x∈WN x∈UN x∈SR = {!  ? !} 


    SR↓⊆SR : ∀ {x y} → is_-SR_ x → (R ⋆) x y → is_-SR_ y
    SR↓⊆SR {x} (SRrec _ x∈rec) ε⋆ = SRrec x x∈rec
    SR↓⊆SR {y} (SRrec _ x∈rec) (Rxx₀ ,⋆ R*x₀y) = SR↓⊆SR (SRrec _ (ReductionClosureProperties.rec↓⊆rec R x∈rec (Rxx₀ ,⋆ ε⋆))) R*x₀y
    SR↓⊆SR {x} (SRacc _ x∈acc) ε⋆ = SRacc x x∈acc
    SR↓⊆SR (SRacc _ x) (Rxx₀ ,⋆ R*x₀y) = SR↓⊆SR (x _ Rxx₀) R*x₀y 

    LemmaSR : weakly-confluent R → ∀ x → is_-SR_ x → ∀ y z → R x y → R x z →  -- Don't think this lemma is really needed as we know gloablly SR
        Σ[ w ∈ A ] (is_-SR_ w × ((R ⋆) y w × (R ⋆) z w)) -- If x is SR and has two single step reductions and is WCR then there is 
        -- a common reduct that is SR
    LemmaSR RisWCR x x∈SR y z Rxy Rxz with RisWCR (x ,, (Rxy , Rxz)) 
    ... | w ,, R*yw , R*zw = w ,, ((SR↓⊆SR x∈SR (Rxz ,⋆ R*zw)) , (R*yw , R*zw)) 

    findRecInReduction : ∀ x → (∀ y → R x y → is_-SR_ y) → Σ[ r ∈ A ] ((R ⋆) x r × is R -recurrent r)
    findRecInReduction x x∈Acc with x∈Acc x {!   !} 
    ... | z = {!   !} 

    SRx→Recr : ∀ x → is_-SR_ x → Σ A (λ r → is R -recurrent r × (R ⋆) x r)
    SRx→Recr x (SRrec .x x∈Rec) = x ,, x∈Rec , ε⋆
    SRx→Recr x (SRacc .x x∈Acc) with (λ y → SRx→Recr y (x∈Acc y {!   !})) 
    ... | z = {!   !} 

    LocalNewmansLemmaRecurrent : weakly-confluent R → ∀ x → is_-SR_ x → is R -CR x 
    LocalNewmansLemmaRecurrent RisWCR x (SRrec .x x∈Rec) R*xy R*xz = x ,, x∈Rec _ R*xy , x∈Rec _ R*xz
    LocalNewmansLemmaRecurrent RisWCR x (SRacc .x x∈Acc) ε⋆ R*xz = _ ,, R*xz , ε⋆
    LocalNewmansLemmaRecurrent RisWCR x (SRacc .x x∈Acc) (Rxy₁ ,⋆ R*y₁y) ε⋆ = _ ,, ε⋆ , (Rxy₁ ,⋆ R*y₁y)
    LocalNewmansLemmaRecurrent RisWCR x (SRacc .x x∈Acc) (Rxy₁ ,⋆ R*y₁y) (Rxz₁ ,⋆ R*z₁z) 
                with LemmaSR RisWCR x (SRacc x x∈Acc) _ _ Rxy₁ Rxz₁ 
    ... | w ,, w∈SR , (R*y₁w , R*z₁w)  with LocalNewmansLemmaRecurrent RisWCR _ (x∈Acc _ Rxy₁) R*y₁y R*y₁w 
                                 | LocalNewmansLemmaRecurrent RisWCR _ (x∈Acc _ Rxz₁) R*z₁z R*z₁w 
                                                
    ... | y₂ ,, R*yy₂ , R*wy₂ | z₂ ,, R*zz₂ , R*wz₂ = {!   !} 
    -- with LocalNewmansLemmaRecurrent RisWCR w w∈SR R*wy₂ R*wz₂ 
    -- ... | w₂ ,, R*y₂w₂ , R*z₂w₂ = w₂ ,, ((R*yy₂ ⋆!⋆ R*y₂w₂) , (R*zz₂ ⋆!⋆ R*z₂w₂))


    NewmansLemmaRecurrent : SR → weakly-confluent R → CR R  
    NewmansLemmaRecurrent RisSR RisWCR x ε⋆ R*xz = _ ,, R*xz , ε⋆
    NewmansLemmaRecurrent RisSR RisWCR x (Rxy₁ ,⋆ R*y₁y) ε⋆ = _ ,, ε⋆ , (Rxy₁ ,⋆ R*y₁y)
    NewmansLemmaRecurrent RisSR RisWCR x (Rxy₁ ,⋆ R*y₁y) (Rxz₁ ,⋆ Rz₁z) = 
        let 
            w ,, w∈SR , (R*y₁w , R*z₁w) = LemmaSR RisWCR x (RisSR x)  _ _ Rxy₁ Rxz₁ -- We have a common reduct (w) from y₁ and z₁. w is SR
            
            -- We know that w has a reduction to y₁ and z₁ 
            -- y₁∈SR = SR↓⊆SR (RisSR x) (Rxy₁ ,⋆ {!   !} )
            Rwy₁ = SR↓⊆SR (RisSR _ ) R*y₁w 



            r = NewmansLemmaRecurrent RisSR RisWCR w {! (R*y₁w ,⋆ R*y₁y) !} {!   !} 
        in 
            {!   !}


module Confluent-Implications where

    WR∧RP→CR : ∀ {x} → is_-WR_ x → is_-RP_ x → is R -CR x
    WR∧RP→CR (q ,, (R*xq , isRec_q)) isRP_x R*xy R*xz = q ,, isRP isRec_q x R*xq R*xy , isRP isRec_q x R*xq R*xz

    WN∧NP→CR : ∀ {x} → is R -WN x → is_-WNFP_ x → is R -CR x
    WN∧NP→CR (n ,, (R*xn , x∈NF)) isWNFP_x R*xy R*xz = n ,, isWNFP x∈NF x R*xn R*xy , isWNFP x∈NF x R*xn R*xz

    -- SR∧RP→SL : ∀ {x} → is_-SR_ x → is_-RP_ x → ∀ {y z} → R x y → (R ⋆) x z → y ↘ R ⋆ ↙ z
    -- SR∧RP→SL {x} (SRrec _ isRec_x) x∈RP {y} {z} Rxy R*xz = {!   !}
    -- SR∧RP→SL {x} (SRacc _ x∈SR) x∈RP {y} {.x} Rxy ε⋆ = y ,, ε⋆ , (Rxy ,⋆ ε⋆)
    -- SR∧RP→SL {x} (SRacc _ x∈SR) x∈RP {y} {z} Rxy (_,⋆_ {y = w} Rxw R*wz) =
    --   let w∈SR : is_-SR_ w
    --       w∈SR = x∈SR w Rxw
    --       w∈RP : is_-RP_ w
    --       w∈RP = {!   !}
    --       IH = SR∧RP→SL {w} w∈SR w∈RP
    --    in {!   !}

    -- SR∧RP→CR : ∀ {x} → is_-SR_ x → is_-RP_ x → is R -CR x
    -- SR∧RP→CR {x} (SRrec _ isRec_x) isRP_x R*xy R*xz = x ,, isRec _ x R*xy , isRec _ x R*xz
    -- SR∧RP→CR {x} (SRacc _ isSR_x₁) isRP_x R*xy R*xz = {!   !}
    -- SR∧RP→SL {x} (SRacc _ x∈SR) x∈RP {y} {z} Rxy ( _,⋆_ {y = w} Rxw R*wz) =
    --   let w∈SR : is_-SR_ w
    --       w∈SR = x∈SR w Rxw
    --       w∈RP : is_-RP_ w
    --       w∈RP = {!   !}
    --       IH = SR∧RP→SL {w} w∈SR w∈RP
    --    in {!   !}

    -- Counterexample WN∧SR∧UN→CR

    SN∧UN→CR : ∀ {x} → is R -SN x → is R -UN x → is R -CR x
    SN∧UN→CR isSN_x isUN_x R*xy R*xz = {!   !}

    SN∧UN→NP : ∀ x → is R -SN x → is R -UN x → is_-WNFP_ x -- WTS R*zy. know y is uniquely normal. Know strongly normal. So z should terminate. Must terminate at y
    SN∧UN→NP x (acc xacc) x∈UN y∈NF R*xy R*xz = {!   !}  