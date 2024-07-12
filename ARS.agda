module ARS where

open import Relations
open import Predicates
open import Logic-Levels

{-
What we want to do:
provide a formalisation of the proofs in Term Rewriting Systems Chapter 1: Abstract reduction systems

The chapter is focussed on an abstract approach to reduction systems such as reduction, conversion, confluence,
and normalisation. 
-}

module Confluence {A : Set} (Rα : 𝓡 A) where
    
    commute-weakly : 𝓡 A → Set 
    commute-weakly Rβ = ∀ {a}{b}{c} → Rα a b → Rβ a c → Σ[ d ∈ A ] ((Rβ ⋆) b d × (Rα ⋆) c d)

    commute : 𝓡 A → Set 
    commute Rβ = ∀ {a}{b}{c} → (Rα ⋆) a b → (Rβ ⋆) a c → Σ[ d ∈ A ] ((Rβ ⋆) b d × (Rα ⋆) c d)

    self-commuting : Set 
    self-commuting = commute Rα 

    -- Weakly confluent also reffered to as locally confluent in Terese 
    weakly-confluent : Set 
    weakly-confluent = ∀ {a}{b}{c} → Rα a c → Rα a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    -- Confluent and Weakly Church-Rosser (WCR) are used interchangeably in Terese
    confluent : Set 
    confluent = ∀ {a}{b}{c} → (Rα ⋆) a c → (Rα ⋆) a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    subcommutative : Set 
    subcommutative = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] ((Rα ⁼) b d × (Rα ⁼) c d)

    -- Diamond property (◆ is \di) 
    ◆ : Set 
    ◆ = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] (Rα b d × Rα c d)

open Confluence public  

module Proposition_one_one_nine {A : Set} {Rα Rβ : 𝓡 A} where
    ii : commute Rα Rβ ↔ ~R (Rβ ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R  ~R (Rβ ⋆)
    pr1 ii commRαRβ c b (a ,, Rβ*ac , Rα*ab) with commRαRβ Rα*ab Rβ*ac 
    ...| d ,, Rβ*bd , Rα*cd = d ,, Rα*cd , Rβ*bd
    pr2 ii f {a}{b}{c} Rα*ab Rβ⋆ac with f c b (a ,, Rβ⋆ac , Rα*ab) 
    ...| d ,, Rα*cd , Rβ*bd = d ,, (Rβ*bd , Rα*cd)

    iii : weakly-confluent Rα ↔ ~R Rα ∘R Rα ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 iii WCRα c b (a ,, Rαac , Rαab) = WCRα Rαac Rαab
    pr2 iii f {a}{b}{c} Rαac Rαab = f c b (a ,, Rαac , Rαab)

    iv : subcommutative Rα ↔ ~R Rα ∘R Rα ⊆ ((Rα ⁼) ∘R ~R (Rα ⁼))
    pr1 iv subComRα c b (a ,, Rαac , Rαab) = subComRα Rαac Rαab
    pr2 iv f {a}{b}{c} Rαab Rαac = f b c (a ,, Rαab , Rαac)
    

    v : ◆ Rα ↔ ~R Rα ∘R Rα ⊆ Rα ∘R ~R Rα 
    pr1 v ◆Rα b c (a ,, Rαab , Rαac) = ◆Rα Rαab Rαac
    pr2 v f {a}{b}{c} Rαab Rαac = f b c (a ,, Rαab , Rαac)

    vi : confluent Rα ↔ ~R (Rα ⋆) ∘R (Rα ⋆) ⊆ (Rα ⋆) ∘R ~R (Rα ⋆)
    pr1 vi confRα b c (a ,, Rα*ab , Rα*ac) = confRα Rα*ab Rα*ac
    pr2 vi f {a}{b}{c} Rα*ac Rα*ab = f c b (a ,, Rα*ac , Rα*ab)

module Proposition_one_one_ten {A : Set} {R : 𝓡 A} where 
    i→ii : confluent R  → weakly-confluent (R ⋆) 
    i→ii confR R*ac R*ab with confR R*ac R*ab 
    ... | d ,, R*cd , R*bd = d ,, ax⋆ R*cd , ax⋆ R*bd

    lemma**→* : ∀ {a b : A} →  ((R ⋆) ⋆) a b → (R ⋆) a b  -- Rename this to TCisTC in ClosureOperators? 
    lemma**→* (ax⋆ R*ab) = R*ab
    lemma**→* ε⋆ = ε⋆
    lemma**→* (R*ay ,⋆ R**yb) = TCisTran R R*ay (lemma**→* R**yb)

    ii→iii : weakly-confluent (R ⋆) → self-commuting (R ⋆)
    ii→iii wconfR R**ab R**ac with wconfR (lemma**→* R**ac) (lemma**→* R**ab) 
    ... | d ,, R**cd , R**bd = d ,, (R**bd , R**cd) 

    lemma**→*⁼ : ∀ {a b : A} → ((R ⋆)⋆) a b → ((R ⋆)⁼) a b 
    lemma**→*⁼ = ax⁼ ∘ lemma**→*
    
    iii→iv : self-commuting (R ⋆) → subcommutative (R ⋆)
    iii→iv scR R*ab R*ac with scR (ax⋆ R*ac) (ax⋆ R*ab) 
    ... | d ,, R**cd , R**bd = d ,, lemma**→*⁼ R**bd , lemma**→*⁼ R**cd

    lemma*=→* : ∀ {a b : A} → ((R ⋆)⁼) a b → (R ⋆) a b 
    lemma*=→* (ax⁼ R*ab) = R*ab
    lemma*=→* ε⁼ = ε⋆ 
    
    iv→i : subcommutative (R ⋆) → confluent R 
    iv→i subcomR R*ac R*ab with subcomR R*ab R*ac 
    ... | d ,, R*=bd , R*=cd = d ,, lemma*=→* R*=cd , lemma*=→* R*=bd
    
    i→v : confluent R → ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)
    i→v confR b c (a ,, Rab , R*ac) = confR (ax⋆ Rab) R*ac

    lemmaSymisSym : ∀ {a b : A} → (R ˢ) a b → (R ˢ) b a 
    lemmaSymisSym (axˢ+ Rab) = axˢ- Rab
    lemmaSymisSym (axˢ- Rba) = axˢ+ Rba

    v→vi : ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆) → EQ R ⊆ (R ⋆) ∘R ~R (R ⋆)
    v→vi v a b (ax⋆ Rˢab) with v a b (a ,, ({!   !} , {!   !}))
    ... | d ,, R*ad , R*ab = d ,, (R*ad , R*ab)
    v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    v→vi v a b (x ,⋆ EQRab) = {!   !}
  
   