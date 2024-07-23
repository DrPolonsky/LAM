module Relations.ARS {A : Set} where

open import Relations.Relations
open import Predicates
open import Logic-Levels

{-
What we want to do:
provide a formalisation of the proofs in Term Rewriting Systems Chapter 1: Abstract reduction systems

The chapter is focussed on an abstract approach to reduction systems such as reduction, conversion, confluence,
and normalisation.
-}
-- ↘ is \dr, ↙ is \dl
_↘_↙_ : A → 𝓡 A → A → Set
_↘_↙_ a R b = (R ∘~ R) a b

_↙_↘_ : A → 𝓡 A → A → Set
_↙_↘_ a R b = (R ~∘ R) a b

-- 𝓖 is \MCG
𝓖 : 𝓡 A → 𝓟 A
𝓖 R a = Σ[ b ∈ A ] (R ⋆) a b

-- Definition 1.1.8: Notions of Confluence
module Confluence (Rα : 𝓡 A) where
    commute-weakly : 𝓡 A → Set
    -- commute-weakly Rβ = ∀ {a}{b}{c} → Rα a b → Rβ a c → ((Rβ ⋆) ∘~ (Rα ⋆)) b c
    commute-weakly Rβ =  Rα ~∘ Rβ  ⊆₂  Rβ ⋆ ∘~ Rα ⋆

    commute : 𝓡 A → Set
    -- commute Rβ = Rα ⋆ ~∘ Rβ ⋆ ⊆₂ Rβ ⋆ ∘~ Rα ⋆
    commute Rβ = ∀ {a}{b}{c} → (Rα ⋆) a b → (Rβ ⋆) a c → Σ[ d ∈ A ] ((Rβ ⋆) b d × (Rα ⋆) c d)

    self-commuting : Set
    self-commuting = commute Rα

    -- Weakly confluent also reffered to as locally confluent in Terese
    weakly-confluent : Set
    weakly-confluent =  ∀ {b}{c} → b ↙ Rα ↘ c → b ↘ Rα ⋆ ↙ c
    -- weakly-confluent = ∀ {a}{b}{c} → Rα a c → Rα a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    -- Confluent and Weakly Church-Rosser (WCR) are used interchangeably in Terese
    confluent : Set
    confluent = ∀ {b}{c} → b ↙ Rα ⋆ ↘ c → b ↘ Rα ⋆ ↙ c
    -- confluent = ∀ {a}{b}{c} → (Rα ⋆) a c → (Rα ⋆) a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    CR : Set
    CR = confluent

    WCR : Set
    WCR = weakly-confluent

    subcommutative : Set
    subcommutative = ∀ {b}{c} → b ↙ Rα ↘ c → b ↘ Rα ʳ ↙ c 
    -- subcommutative = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] ((Rα ʳ) b d × (Rα ʳ) c d)

    -- Diamond property (◆ is \di)
    ◆ : Set
    ◆ = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] (Rα b d × Rα c d)

open Confluence public

module Proposition-1-1-9 {Rα Rβ : 𝓡 A} where
    ii : commute Rα Rβ ↔ ~R (Rβ ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R  ~R (Rβ ⋆)
    pr1 ii commRαRβ c b (a ,, Rβ*ac , Rα*ab) with commRαRβ Rα*ab Rβ*ac
    ...| d ,, Rβ*bd , Rα*cd = d ,, Rα*cd , Rβ*bd
    pr2 ii f {a}{b}{c} Rα*ab Rβ⋆ac with f c b (a ,, Rβ⋆ac , Rα*ab)
    ...| d ,, Rα*cd , Rβ*bd = d ,, (Rβ*bd , Rα*cd)

    iii : weakly-confluent Rα ↔ ~R Rα ∘R Rα ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 iii WCRα c b peak@(a ,, Rαac , Rαab) with WCRα peak 
    ... | d ,, Rα*cd , Rα*cb = d ,, (Rα*cd , Rα*cb)
    pr2 iii RHS {b} {c} valley@(a ,, Rα*ab , Rα*ac) = RHS b c valley
    
    iv : subcommutative Rα ↔ ~R Rα ∘R Rα ⊆ ((Rα ʳ) ∘R ~R (Rα ʳ))
    pr1 iv subComRα c b peak@(a ,, Rαac , Rαab) = subComRα peak
    pr2 iv RHS {b}{c} valley = RHS b c valley 
    
    v : ◆ Rα ↔ ~R Rα ∘R Rα ⊆ Rα ∘R ~R Rα
    pr1 v ◆Rα b c (a ,, Rαab , Rαac) = ◆Rα Rαab Rαac
    pr2 v f {a}{b}{c} Rαab Rαac = f b c (a ,, Rαab , Rαac)

    vi : confluent Rα ↔ ~R (Rα ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 vi confRα b c (a ,, Rα*ab , Rα*ac) = confRα (a ,, Rα*ab , Rα*ac)
    pr2 vi RHS {b}{c} peak = RHS b c peak
   

module Proposition-1-1-10 {R : 𝓡 A} where
    i→ii : confluent R  → weakly-confluent (R ⋆)
    i→ii confR peak with confR peak 
    ... | d ,, R*bd , R*cd = d ,, ((ax⋆ R*bd) , (ax⋆ R*cd))

    ii→iii : weakly-confluent (R ⋆) → self-commuting (R ⋆)
    ii→iii wconfR* {a} R**ab R**ac with wconfR* (a ,, (**→* R R**ac , **→* R R**ab))  
    ... | d ,, R**cd , R**bd = d ,, (R**bd , R**cd)


    iii→iv : self-commuting (R ⋆) → subcommutative (R ⋆)
    iii→iv scR* (a ,, R*ab , R*ac) with scR* (ax⋆ R*ab) (ax⋆ R*ac)
    ... | d ,, R**bd , R**cd = d ,, **→*ʳ R R**bd , **→*ʳ R R**cd 

    iv→i : subcommutative (R ⋆) → confluent R
    iv→i subcomR* peak@(a ,, R*ac , R*ab)  with subcomR* peak
    ... | d ,, R*=cd , R*=bd = d ,, *ʳ→* R R*=cd , *ʳ→* R R*=bd

    i→v : confluent R → ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)
    i→v confR b c (a ,, Rab , R*ac) = confR (a ,, ax⋆ Rab , R*ac)

    v→vi : (~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)) → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
    v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    v→vi v a b (ax⋆ (axˢ+ Rab)) = (b ,, (ax⋆ Rab ) , ε⋆ )
    v→vi v a b (ax⋆ (axˢ- Rba)) = a ,, ε⋆ , ax⋆ Rba
    v→vi v a b (Rˢac ,⋆ EQRcb) with v→vi v _ b EQRcb
    ... | d ,, R*cd , R*bd with Rˢac
    ... | axˢ+ Ray = d ,, (Ray ,⋆ R*cd) , R*bd
    ... | axˢ- Rya with v a d (_ ,, (Rya , R*cd))
    ... | e ,, R*ae , R*de = e ,, (R*ae , ( TCisTran R R*bd R*de ))

    vi→i : R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆) → confluent R
    vi→i vi {b}{c} peak@(a ,, R*ab , R*ac)  with vi b c (EQisTran (EQisSym (*⊆EQ R*ab)) (*⊆EQ R*ac)) 
    ... | d ,, R*cd , R*bd = d ,, (R*cd , R*bd)
    
module Proposition-1-1-11  where
    lemmai : ∀ {R : 𝓡 A} → {a b c : A} → ◆ R → (R ⋆) a b → R a c → Σ[ d ∈ A ] (R b d × (R ⋆) c d)
    lemmai R◆ ε⋆ R◆ac = _ ,, R◆ac , ε⋆
    lemmai R◆ (ax⋆ Rab) Rac with R◆ Rab Rac
    ... | d ,, Rbd , Rac = d ,, Rbd , ax⋆ Rac
    lemmai R◆ (Ray ,⋆ R*yb) Rac with R◆ Ray Rac
    ... | d ,, Ryd , Rcd with lemmai R◆ R*yb Ryd
    ... | e ,, Re , R*de = e ,, (Re , (Rcd ,⋆ R*de))

    lemmaii : ∀ {R : 𝓡 A} → ◆ R → confluent R
    -- lemmaii R◆ peak@(a ,, ε⋆ , R*ac) = _ ,, R*ac , ε⋆
    -- lemmaii R◆ peak@(a ,, ax⋆ Rab , R*ac) with lemmai R◆ {!   !} {!   !}  
    -- ... | z = {!   !}
    -- lemmaii R◆ peak@(a ,, (x ,⋆ R*ab) , R*ac) = {!   !} 
    lemmaii R◆ (a ,, R*ab , ε⋆) = _ ,, ε⋆ , R*ab
    lemmaii R◆ (a ,, R*ab , ax⋆ Rac) with lemmai R◆ R*ab Rac 
    ... |  d ,, Rbd , R*cd = d ,, (ax⋆ Rbd , R*cd)
    lemmaii R◆ (a ,, R*ab , (Ray ,⋆ R*yc)) with  lemmai R◆ R*ab Ray  -- lemmai R◆ R*ab Ray 
    ... | d ,, Rbd , R*yd with lemmaii R◆ {!   !}   --  R◆ (_ ,, R*yd , R*yc)           -- something is going wrong here. 
    ... | e ,, R*de , R*ce = e ,, ((Rbd ,⋆ R*de) , R*ce)
    -- lemmaii R◆ ε⋆ R*ab = _ ,, R*ab , ε⋆
    -- lemmaii R◆ (ax⋆ Rac) R*ab with lemmai R◆ R*ab Rac
    -- ... | d ,, Rbd , R*cd = d ,, (R*cd , (ax⋆ Rbd))
    -- lemmaii R◆ (Ray ,⋆ R*yc) R*ab with lemmai R◆ R*ab Ray
    -- ... | d ,, Rbd , R*yd with lemmaii R◆ R*yc R*yd
    -- ... | e ,, R*ce , R*de = e ,, (R*ce , (Rbd ,⋆ R*de))

    lemmaiii : ∀ {R₁ R₂ : 𝓡 A} → (R₁ ⊆ R₂ ⋆) → (R₁ ⋆ ⊆ R₂ ⋆)
    lemmaiii Rab⊆R₂*ab a b R*ab = **→* _ (⊆⋆ Rab⊆R₂*ab a b R*ab)

    proposition11 : ∀ {R R⋄ : 𝓡 A} → (R ⊆ R⋄) → (R⋄ ⊆ R ⋆) → ◆ R⋄ → confluent R
    proposition11 R⊆R⋄ R⋄⊆R* ◆R⋄ {b} {c} peak@(a ,, R*ab , R*ac) with ⊆⋆ R⊆R⋄ a c R*ac 
    ... | R⋄*ac with ⊆⋆ R⊆R⋄ a b R*ab
    ... | R⋄*ab with lemmaii ◆R⋄ (a ,, (R⋄*ab , R⋄*ac))  
    ... | d ,, R⋄*bd , R⋄*cd with lemmaiii R⋄⊆R* c d R⋄*cd
    ... | R*cd with lemmaiii R⋄⊆R* b d R⋄*bd
    ... | R*bd = d ,, R*bd , R*cd

 
-- Notions related to termination in ARSs
module Termination (R : 𝓡 A)  where

  open import Relations.Wellfounded

  is_-NF_ : 𝓟 A
  is_-NF_ x = ∀ y → ¬ R x y
  -- is_-NF_ x = R x ⊆ K⊥

  is_-WN_ : 𝓟 A
  is_-WN_ x = Σ[ n ∈ A ] (R x n × is_-NF_ n)

  is_-SNacc_ : 𝓟 A
  is_-SNacc_ x = is (~R R) -accessible x

  is_-SN_ : 𝓟 A
  is_-SN_ = is_-SNacc_

  WN : Set
  WN = ∀ x → is_-WN_ x

  SN : Set
  SN = ∀ x → is_-SN_ x

  NFP : Set
  NFP = R ⁼ ⊆ R ⋆

  UN : Set
  UN = ∀ {a b : A} → a ∈ is_-NF_ → b ∈ is_-NF_ → (R ⁼) ⊆ _≡_

  UN→ : Set
  UN→ = ∀ {x a b : A} → a ∈ is_-NF_ → b ∈ is_-NF_  → (R ⋆) x a → (R ⋆) x b → a ≡ b

  -- AKA Convergent
  isComplete : Set
  isComplete = CR R × SN

  isSemicomplete : Set
  isSemicomplete = UN × WN

  -- Miscelaneous properties
  open import Lifting using (ℕ ; Fin)
  ω-bounded : Set
  ω-bounded = ∀ (f : ℕ → A) → is R -increasing f → Σ[ a ∈ A ] (∀ n → R (f n) a)

  isFinitelyBranching : Set
  isFinitelyBranching = ∀ (a : A)
    → Σ[ n ∈ ℕ ] (Σ[ f ∈ (Fin n → A) ] (∀ b → R a b → Σ[ j ∈ Fin n ] (b ≡ f j)))

  is_-cofinal_ : 𝓟 A → Set
  is_-cofinal_ B = ∀ (x : A) → Σ[ y ∈ A ] ((R ⋆) x y × y ∈ B)

  CP : Set
  CP = ∀ a → ∀ (br : 𝓖 R a) → Σ[ yr ∈ 𝓖 R a ] (R (fst br) (fst yr))

open Termination public


module Newmans-Lemma where 
  -- If R is SN and WCR then R is CR 

  -- Three proofs in Therese. 
  -- i) By SN, every a ∈ A reduces to at least one normal form. For CR it suffices to show that every a ∈ A has at most one normal form.
  -- ii) As → is SN, ← is WF, and hence ←⁺ is a well founded order... 
  -- iii) 

  -- Proof i

  SN→NFelement : ∀ {R : 𝓡 A} → SN R → (a : A) → Σ[ n ∈ A ] ((R ⋆) a n × is R -NF  n)
  SN→NFelement SNR a with SNR a 
  ... | acc H = {!   !} ,, {!   !} 

  temp : ∀ {R : 𝓡 A} → SN R → (a : A) → Σ[ n ∈ A ] ((R ⋆) a n × is R -NF  n) → UN 

  NLemmai : ∀ {R : 𝓡 A} → SN R → weakly-confluent R → confluent R 
  NLemmai SNR WCR with SN→NFelement SNR {!   !} 
  ... | n ,, R*an , NFn = {!   !}

  -- Proof ii 

  SNisWFacc : ∀ {R : 𝓡 A} {x : A} → is R -SN x → isWFacc R 
  SNisWFacc (acc H) x = {!   !}

  confluentElement : ∀ (R : 𝓡 A) → A → Set 
  confluentElement R a = ∀ {b c} → (R ⋆) a b → (R ⋆) a c → Σ[ d ∈ A ] ((R ⋆) b d × (R ⋆) c d) 

  wCR→conflInd : ∀ {R : 𝓡 A} → weakly-confluent R → (x : A) → (∀ y → R x y → confluentElement R y) → confluentElement R x 
  wCR→conflInd WCR a IND ε⋆ R*ac = _ ,, R*ac , ε⋆
  wCR→conflInd WCR a IND (ax⋆ x) R*ac = {!   !}
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) ε⋆ = _ ,, ε⋆ , (Ray ,⋆ R*yb)
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) (ax⋆ x) = {!   !}
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) (Raz ,⋆ R*zc) with WCR (a ,, (Ray , Raz)) 
  ... | d ,, R*yd , R*zd with IND _ Ray R*yb R*yd 
  ... | e ,, R*be , R*de with IND _ Raz R*zc (TCisTran _ R*zd R*de) 
  ... | f ,, R*cf , R*ef = f ,, (TCisTran _ R*be R*ef , R*cf)  

  NLemmaii : ∀ {R : 𝓡 A} → SN R → weakly-confluent R → confluent R 
  NLemmaii SNR WCR peak@(a ,, R*ab , R*ac) = wCR→conflInd WCR a (λ y Ray → {!  !}) R*ab R*ac



















   
-- The end
       