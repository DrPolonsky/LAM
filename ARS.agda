module ARS {A : Set} where

open import Relations
open import Predicates
open import Logic-Levels

{-
What we want to do:
provide a formalisation of the proofs in Term Rewriting Systems Chapter 1: Abstract reduction systems

The chapter is focussed on an abstract approach to reduction systems such as reduction, conversion, confluence,
and normalisation.
-}
_↘_↙_ : A → 𝓡 A → A → Set
_↘_↙_ a R b = (R ∘~ R) a b

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
    -- weakly-confluent =  ∀ {a}{b}{c} → a ↘ Rα ⋆ ↙ b  
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

module Proposition-1-1-9 {Rα Rβ : 𝓡 A} where
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

module Proposition-1-1-10 {R : 𝓡 A} where
    i→ii : confluent R  → weakly-confluent (R ⋆)
    i→ii confR R*ac R*ab with confR R*ac R*ab
    ... | d ,, R*cd , R*bd = d ,, ax⋆ R*cd , ax⋆ R*bd

    ii→iii : weakly-confluent (R ⋆) → self-commuting (R ⋆)
    ii→iii wconfR R**ab R**ac with wconfR (**→* R**ac) (**→* R**ab)
    ... | d ,, R**cd , R**bd = d ,, (R**bd , R**cd)


    iii→iv : self-commuting (R ⋆) → subcommutative (R ⋆)
    iii→iv scR R*ab R*ac with scR (ax⋆ R*ac) (ax⋆ R*ab)
    ... | d ,, R**cd , R**bd = d ,, **→*⁼ R**bd , **→*⁼ R**cd

    iv→i : subcommutative (R ⋆) → confluent R
    iv→i subcomR R*ac R*ab with subcomR R*ab R*ac
    ... | d ,, R*=bd , R*=cd = d ,, *=→* R*=cd , *=→* R*=bd

    i→v : confluent R → ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)
    i→v confR b c (a ,, Rab , R*ac) = confR (ax⋆ Rab) R*ac

    v→vi : (~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)) → EQ R ⊆ (R ⋆) ∘R ~R (R ⋆)
    v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    v→vi v a b (ax⋆ Rˢab) with v→vi v {!   !} b {!   !} 
    ... | d ,, R*cd , R*bd = d ,, {!   !} , R*bd
    v→vi v a b (x ,⋆ EQRxy) = {!   !}
    -- v→vi v a b (ax⋆ Rˢab) with v→vi v _ b {!   !} 
    -- ... | z = {!   !} 
    -- -- v a b (a ,, ({!   !} , {!   !}))
    -- -- ... | d ,, R*ad , R*ab = d ,, (R*ad , R*ab)
    -- v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    -- v→vi v a b (Rˢac ,⋆ EQRcb) with v→vi v _ b EQRcb
    -- ... | d ,, R*cd , R*bd with v a d (_ ,, ({!   !} , R*cd)) 
    -- ... | e ,, R*ae , R*de = e ,, (R*ae , ( TCisTran R R*bd R*de ))

    vi→i : EQ R ⊆ (R ⋆) ∘R ~R (R ⋆) → confluent R
    vi→i vi {a} {b} {c} R*ac R*ab with vi b c (EQisTran (EQisSym (*⊆EQ R*ab)) (*⊆EQ R*ac)) 
    ... | d ,, R*bd , R*cd = d ,, (R*cd , R*bd)

module Proposition-1-1-11  where 
    lemmai : ∀ {R : 𝓡 A} → {a b c : A} → ◆ R → (R ⋆) a b → R a c → Σ[ d ∈ A ] (R b d × (R ⋆) c d)
    lemmai R◆ ε⋆ R◆ac = _ ,, R◆ac , ε⋆
    lemmai R◆ (ax⋆ Rab) Rac with R◆ Rab Rac 
    ... | d ,, Rbd , Rac = d ,, Rbd , ax⋆ Rac
    lemmai R◆ (Ray ,⋆ R*yb) Rac with R◆ Ray Rac 
    ... | d ,, Ryd , Rcd with lemmai R◆ R*yb Ryd 
    ... | e ,, Re , R*de = e ,, (Re , (Rcd ,⋆ R*de)) 

    lemmaii : ∀ {R : 𝓡 A} → ◆ R → confluent R 
    lemmaii R◆ ε⋆ R*ab = _ ,, R*ab , ε⋆
    lemmaii R◆ (ax⋆ Rac) R*ab with lemmai R◆ R*ab Rac 
    ... | d ,, Rbd , R*cd = d ,, (R*cd , (ax⋆ Rbd))
    lemmaii R◆ (Ray ,⋆ R*yc) R*ab with lemmai R◆ R*ab Ray 
    ... | d ,, Rbd , R*yd with lemmaii R◆ R*yc R*yd 
    ... | e ,, R*ce , R*de = e ,, (R*ce , (Rbd ,⋆ R*de))

    -- lemmaiii : ∀ {R₂ : 𝓡 A} → R ⊆ R₂ → R ⋆ ⊆ R₂ ⋆ 

    lemmaiii : ∀ {R₁ R₂ : 𝓡 A} → (R₁ ⊆ R₂ ⋆) → (R₁ ⋆ ⊆ R₂ ⋆)
    lemmaiii Rab⊆R₂*ab a b R*ab = **→* (⊆⋆ Rab⊆R₂*ab a b R*ab)

    proposition11 : ∀ {R R⋄ : 𝓡 A} → (R ⊆ R⋄) → (R⋄ ⊆ R ⋆) → ◆ R⋄ → confluent R 
    proposition11 R⊆R⋄ R⋄⊆R* ◆R⋄ {a}{b}{c} R*ac R*ab with ⊆⋆ R⊆R⋄ a c R*ac 
    ... | R⋄*ac with ⊆⋆ R⊆R⋄ a b R*ab 
    ... | R⋄*ab with lemmaii ◆R⋄ R⋄*ac R⋄*ab 
    ... | d ,, R⋄*cd , R⋄*bd with lemmaiii R⋄⊆R* c d R⋄*cd 
    ... | R*cd with lemmaiii R⋄⊆R* b d R⋄*bd 
    ... | R*bd = d ,, R*cd , R*bd   
    