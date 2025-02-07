{-# OPTIONS --allow-unsolved-metas #-}
module Relations.ARS {A : Set} where

open import Relations.Relations
open import Predicates
open import Logic
open import Datatypes using (ℕ ; zero; succ; Fin)

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
    -- commute Rβ = ∀ {a}{b}{c} → (Rα ⋆) a b → (Rβ ⋆) a c → Σ[ d ∈ A ] ((Rβ ⋆) b d × (Rα ⋆) c d)
    commute Rβ =  ∀ {a}{b}{c} → (Rα ⋆) a b → (Rβ ⋆) a c → (Rβ ⋆ ∘~ Rα ⋆) b c

    self-commuting : Set
    self-commuting = commute Rα

    -- Weakly confluent also reffered to as locally confluent in Terese
    weakly-confluent : Set
    weakly-confluent =  ∀ {b}{c} → b ↙ Rα ↘ c → b ↘ Rα ⋆ ↙ c
    -- weakly-confluent = ∀ {a}{b}{c} → Rα a c → Rα a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    -- Confluent and Church-Rosser (CR) are used interchangeably in Terese
    confluent : Set
    confluent = ∀ {b}{c} → b ↙ Rα ⋆ ↘ c → b ↘ Rα ⋆ ↙ c
    -- confluent = ∀ {a}{b}{c} → (Rα ⋆) a c → (Rα ⋆) a b → Σ[ d ∈ A ] ((Rα ⋆) c d × (Rα ⋆) b d)

    subcommutative : Set
    subcommutative = ∀ {b}{c} → b ↙ Rα ↘ c → b ↘ Rα ʳ ↙ c
    -- subcommutative = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] ((Rα ʳ) b d × (Rα ʳ) c d)

    -- Diamond property (◆ is \di)
    ◆ : Set
    ◆ = ∀ {a}{b}{c} → Rα a b → Rα a c → (Rα ∘~ Rα) b c
    -- ◆ = ∀ {a}{b}{c} → Rα a b → Rα a c → Σ[ d ∈ A ] (Rα b d × Rα c d)

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
    ... | d ,, R*bd , R*cd = d ,, (ax⋆ (R ⋆) R*bd , ax⋆ (R ⋆) R*cd)

    ii→iii : weakly-confluent (R ⋆) → self-commuting (R ⋆)
    ii→iii wconfR* {a} R**ab R**ac with wconfR* (a ,, (**→* R R**ac , **→* R R**ab))
    ... | d ,, R**cd , R**bd = d ,, (R**bd , R**cd)


    iii→iv : self-commuting (R ⋆) → subcommutative (R ⋆)
    iii→iv scR* (a ,, R*ab , R*ac) with scR* (ax⋆ (R ⋆) R*ab) (ax⋆ (R ⋆) R*ac)
    ... | d ,, R**bd , R**cd = d ,, **→*ʳ R R**bd , **→*ʳ R R**cd

    iv→i : subcommutative (R ⋆) → confluent R
    iv→i subcomR* peak@(a ,, R*ac , R*ab)  with subcomR* peak
    ... | d ,, R*=cd , R*=bd = d ,, *ʳ→* R R*=cd , *ʳ→* R R*=bd

    i→v : confluent R → R ~∘ (R ⋆) ⊆ (R ⋆) ∘~ (R ⋆)
    i→v confR b c (a ,, Rab , R*ac) = confR (a ,, ax⋆ R Rab , R*ac)

    v→vi : (R ~∘ R ⋆) ⊆ (R ⋆ ∘~ R ⋆) → R ⁼ ⊆ (R ⋆ ∘~ R ⋆)
    v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    v→vi v a b (Rˢac ,⋆ EQRcb) with v→vi v _ b EQRcb
    ... | d ,, R*cd , R*bd with Rˢac
    ... | axˢ+ Ray = d ,, (Ray ,⋆ R*cd) , R*bd
    ... | axˢ- Rya with v a d (_ ,, (Rya , R*cd))
    ... | e ,, R*ae , R*de = e ,, (R*ae , ( R*bd ⋆!⋆ R*de ))

    vi→i : R ⁼ ⊆ (R ⋆ ∘~ R ⋆) → confluent R
    vi→i vi {b}{c} peak@(a ,, R*ab , R*ac)  with vi b c ((~⁼ (⋆⊆⁼ R R*ab)) ⁼!⁼ (⋆⊆⁼ R R*ac))
    ... | d ,, R*cd , R*bd = d ,, (R*cd , R*bd)

    i→vi : confluent R → R ⁼ ⊆ (R ⋆ ∘~ R ⋆)
    i→vi confR = v→vi (i→v confR)

    v→i : (R ~∘ R ⋆) ⊆ (R ⋆ ∘~ R ⋆) → confluent R
    v→i v = vi→i (v→vi v)
-- open Proposition-1-1-10 public

module Proposition-1-1-11  where
    lemmai : ∀ {R : 𝓡 A} → {a b c : A} → ◆ R → (R ⋆) a b → R a c → Σ[ d ∈ A ] (R b d × (R ⋆) c d)
    lemmai R◆ ε⋆ R◆ac = _ ,, R◆ac , ε⋆
    lemmai R◆ (Ray ,⋆ R*yb) Rac with R◆ Ray Rac
    ... | d ,, Ryd , Rcd with lemmai R◆ R*yb Ryd
    ... | e ,, Re , R*de = e ,, (Re , (Rcd ,⋆ R*de))

    lemmaii : ∀ {R : 𝓡 A} → ◆ R → ∀ {b}{c} → ∀ (a : A) → (R ⋆) a b → (R ⋆) a c → b ↘ R ⋆ ↙ c
    lemmaii R◆ a R*ab ε⋆ = _ ,, ε⋆ , R*ab
    lemmaii R◆ a R*ab (Ray ,⋆ R*yc) with  lemmai R◆ R*ab Ray
    ... | d ,, Rbd , R*yd with lemmaii R◆ _ R*yd R*yc
    ... | e ,, R*de , R*ce = e ,, ((Rbd ,⋆ R*de) , R*ce)

    lemmaiii : ∀ {R₁ R₂ : 𝓡 A} → (R₁ ⊆ R₂ ⋆) → (R₁ ⋆ ⊆ R₂ ⋆)
    lemmaiii Rab⊆R₂*ab a b R*ab = **→* _ (⊆⋆ Rab⊆R₂*ab a b R*ab)

    proposition11 : ∀ {R R⋄ : 𝓡 A} → (R ⊆ R⋄) → (R⋄ ⊆ R ⋆) → ◆ R⋄ → confluent R
    proposition11 R⊆R⋄ R⋄⊆R* ◆R⋄ {b} {c} peak@(a ,, R*ab , R*ac) with ⊆⋆ R⊆R⋄ a c R*ac
    ... | R⋄*ac with ⊆⋆ R⊆R⋄ a b R*ab
    ... | R⋄*ab with lemmaii ◆R⋄ a R⋄*ab R⋄*ac
    ... | d ,, R⋄*bd , R⋄*cd with lemmaiii R⋄⊆R* c d R⋄*cd
    ... | R*cd with lemmaiii R⋄⊆R* b d R⋄*bd
    ... | R*bd = d ,, R*bd , R*cd

open ClassicalImplications using (decMin;isMinDec;isMinDec-)

module LocalProperties {R : 𝓡 A} where

  WN : 𝓟 A
  WN x = Σ[ n ∈ A ] ((R ⋆) x n × NF n)

  SN : 𝓟 A
  SN = is (~R R) -accessible x

  -- Weak normal form property (denoted NP in notes)
  NP : 𝓟 A
  NP x = ∀ {y z} → NF y → (R ⋆) x y → (R ⋆) x z → (R ⋆) z y

  UN : 𝓟 A
  UN x = ∀ {y} {z} → NF y → NF z → (R ⋆) x y → (R ⋆) x z → y ≡ z

  CR : 𝓟 A
  CR x = ∀ {b c} → (R ⋆) x b → (R ⋆) x c → b ↘ R ⋆ ↙ c

  WCR : 𝓟 A
  WCR x = ∀ {b c} → R x b → R x c → b ↘ R ⋆ ↙ c

  -- Candidate names: MF
  MF : 𝓟 A
  MF x = ∀ y → (R ⋆) x y → (R ⋆) y x

module GlobalProperties (R : 𝓡 A) where
_isCR : Set
_isCR = ∀ x → CR x

_isWCR : Set
_isWCR = ∀ x → WCR x

_isWN : Set
_isWN = ∀ x → WN x

_isSN : Set
_isSN = ∀ x → SN x

_isNP : Set
_isNP = ∀ {a b} → NF b → (R ⁼) a b → (R ⋆) a b

-- [AP.  What's the problem with getting this from local UN?]
_isUN : Set
_isUN = ∀ {a b : A} → a ∈ NF → b ∈ NF → (R ⁼) a b → a ≡ b
-- NB. This is stronger than global UN, which is UN→ below

_isUN→ : Set
_isUN→ = ∀ x → UN x

-- AKA Convergent
_isComplete : Set
_isComplete = CR × SN

_isSemicomplete : Set
_isSemicomplete = UN × WN

-- Miscelaneous properties
is_-_bound_ : (f : ℕ → A) → A → Set
is_-_bound_ f a = ∀ n → (R ⋆) (f n) a

bounded : Set
bounded = ∀ (f : ℕ → A) → is R -increasing f → Σ[ a ∈ A ] (is_-_bound_ f a )

BP : Set
BP = bounded

BP+ : Set
BP+ = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → Σ[ a ∈ A ] (is_-_bound_ f a )

-- Trivially, BP+ → BP
-- Classically, BP → BP+.  Need to decide whether a non-strictly increasing
-- sequence is in fact increasing infinitely often.

dominatedByWF : 𝓡 A → Set
dominatedByWF Q = isWFacc Q × (R ⊆ Q)

is_-cofinal_ : 𝓟 A → Set
is_-cofinal_ B = ∀ (x : A) → Σ[ y ∈ A ] ((R ⋆) x y × y ∈ B)

-- Cofinality Property
CP : Set
CP = ∀ (a : A) → Σ[ s ∈ (ℕ → A) ] ((is (R ʳ) -increasing s) ×
                  (s zero ≡ a × (∀ b → (R ⋆) a b → Σ[ n ∈ ℕ ] ((R ⋆) b (s n))) ))


-- Notions related to termination in ARSs
module Termination (R : 𝓡 A)  where

  open import Relations.Wellfounded

  -- NF x = R x ⊆ K⊥

  NF→ε : ∀ {x} → x ∈ NF → ∀ {y} → (R ⋆) x y → x ≡ y
  NF→ε {x} x∈NF {.x} ε⋆ = refl
  NF→ε {x} x∈NF {y} (Rxy₀ ,⋆ R⋆y₀y) = ∅ (x∈NF _ Rxy₀ )

  SN⊆WN→isMinDec- : ∀ x → WN x → isMinDec- (~R R) x
  SN⊆WN→isMinDec- x (.x ,, ε⋆ , n∈NF) x∉NF = ∅ (x∉NF n∈NF)
  SN⊆WN→isMinDec- x (n ,, (_,⋆_ {y = y} Rxy R*yn) , n∈NF) x∉NF = y ,, Rxy

  SN⊆∁∁WN : SN ⊆ ∁ (∁ WN)
  SN⊆∁∁WN x (acc xacc) ¬WNx = ¬WNx (x ,, ε⋆ , x∈NF ) where
    x∈NF : ∀ y → ¬ R x y
    x∈NF y Rxy = SN⊆∁∁WN y (xacc y Rxy)
           (λ { (n ,, (R*yn , n∈NF)) → ¬WNx ((n ,, (Rxy ,⋆ R*yn) , n∈NF )) } )

  -- ¬¬WN∩isMinDec-⊆WN : ∀ x → ¬¬ (WN x) → isMinDec- (~R R) x → WN x
  -- ¬¬WN∩isMinDec-⊆WN x nnWNx md = {!   !}

  SN∩isMinDec-⊆WN : ∀ x → (SN x) → (∀ y → isMinDec- (~R R) y) → WN x
  SN∩isMinDec-⊆WN x (acc xa) md = {!   !}

  SNdec→WN : decMin (~R R) → SN ⊆ WN
  SNdec→WN decR x (acc accx) with decR x
  ... | in2 y∈NF = x ,, (ε⋆ , y∈NF)
  ... | in1 (y ,, Rxy) with SNdec→WN decR y (accx y Rxy)
  ... | (n ,, R*yn , n∈NF) = (n ,, (Rxy ,⋆ R*yn) , n∈NF)

  WN⊆WN↑ : ∀ {x y} → WN y → (R ⋆) x y → WN x
  WN⊆WN↑ y∈WN ε⋆ = y∈WN
  WN⊆WN↑ y∈WN (Rxz ,⋆ R*zy) with WN⊆WN↑ y∈WN R*zy
  ... | (n ,, R*zn , n∈NF) = n ,, (Rxz ,⋆ R*zn) , n∈NF

  SN⊆WWWN : ∀ a → SN a → (∀ v → (R ⋆) a v → WN v → WN a) → WN a
  SN⊆WWWN a (acc aacc) Ha = {!   !} where
    x∈WNaF* : ∀ y → (R ⋆) a y → WN a
    x∈WNaF* y R*ay = {! H  !}
    x∈WNaF : ∀ y → R a y → WN a
    x∈WNaF y Ray with SN⊆WWWN y (aacc y Ray) (λ { v R*yv (n ,, R*vn , n∈NF) → n ,, (R*yv ⋆!⋆ R*vn) , n∈NF } )
    ... | (n ,, R*yn , n∈NF) = n ,, Ray ,⋆ R*yn , n∈NF
    -- SN⊆WWWN' : ∀ x → SN x → (R ⋆) a x → (∀ y → (R ⋆) x y → WN y → WN a) → WN a
    -- SN⊆WWWN' x (acc xacc) R*ax Hx = {! Hx   !}  where
    --   x∈WNaF : ∀ y → R x y → WN a
    --   x∈WNaF y Rxy = SN⊆WWWN' y (xacc y Rxy) (R*ax ⋆!⋆ (Rxy ,⋆ ε⋆) ) (λ z R*yz z∈WN → Hx z (Rxy ,⋆ R*yz) z∈WN )
  -- SN⊆WWWN : ∀ a → SN a → (∀ v → (R ⋆) a v → WN v → WN a) → WN a
  -- SN⊆WWWN a (acc aacc) Ha = SN⊆WWWN' a (acc aacc) ε⋆ Ha where
  --   x∈WNaF : ∀ y → R a y → WN a
  --   x∈WNaF y Rxy = SN⊆WWWN' y (xacc y Rxy) (R*ax ⋆!⋆ (Rxy ,⋆ ε⋆) ) (λ z R*yz z∈WN → Hx z (Rxy ,⋆ R*yz) z∈WN )
  --   SN⊆WWWN' : ∀ x → SN x → (R ⋆) a x → (∀ y → (R ⋆) x y → WN y → WN a) → WN a
  --   SN⊆WWWN' x (acc xacc) R*ax Hx = {! Hx   !}  where
  --     x∈WNaF : ∀ y → R x y → WN a
  --     x∈WNaF y Rxy = SN⊆WWWN' y (xacc y Rxy) (R*ax ⋆!⋆ (Rxy ,⋆ ε⋆) ) (λ z R*yz z∈WN → Hx z (Rxy ,⋆ R*yz) z∈WN )

  -- SN⊆WWWN : ∀ a → SN a → ∀ x → (R ⋆) a x → (WN x → WN a) → WN a
  -- SN⊆WWWN a (acc aacc) x R*ax WNx→WNa = {!   !}

open Termination public

module ReductionClosureProperties (R : 𝓡 A) where
  SN↓⊆SN : ∀ {x} → is R -SN x → ∀ {y} → (R ⋆) x y → is R -SN y
  SN↓⊆SN isR-SNx ε⋆ = isR-SNx
  SN↓⊆SN isR-SNx@(acc xacc) (Rxx₁ ,⋆ R*x₁y) = SN↓⊆SN (xacc _ Rxx₁) R*x₁y

  NF↓⊆NF : ∀ {x} → is R -NF x → ∀ {y} → (R ⋆) x y → is R -NF y
  NF↓⊆NF isR-NFx ε⋆ = isR-NFx
  NF↓⊆NF isR-NFx (Rxx₁ ,⋆ R*x₁y) = λ y _ → isR-NFx _ Rxx₁

  -- Not provable:
  -- WN↓⊆WN : ∀ {x} → is R -WN x → ∀ {y} → (R ⋆) x y → is R -WN y
  -- Counter: x ->> n and x ->> y (x ∈ WN). y -> z and z -> y and y and z have no other reductions.

  -- Also the assumption of UN→ is insufficient
  -- WN↓UN→⊆WN : UN→ R → ∀ {x} → is R -WN x → ∀ {y} → (R ⋆) x y → is R -WN y
  -- Same counterexample

  -- WCR∧WN↓→WN : WCR R → ∀ {x} → is R -WN x → ∀ {y} → (R ⋆) x y → is R -WN y
  -- WCR∧WN↓→WN R-WCR R- x₂ = {!   !}

  UN↓⊆UN : ∀ {x} → is R -UN x → ∀ {y} → (R ⋆) x y → is R -UN y
  UN↓⊆UN isR-UNx R*xy n∈NF z∈NF R*yn R*yz = isR-UNx n∈NF z∈NF (R*xy ⋆!⋆ R*yn) (R*xy ⋆!⋆ R*yz)

  rec↓⊆rec : ∀ {x} → is R -recurrent x → ∀ {y} → (R ⋆) x y → is R -recurrent y
  rec↓⊆rec isR-recx R*xy z R*yz with isR-recx z (R*xy ⋆!⋆ R*yz)
  ... | R*zx  = R*zx ⋆!⋆ R*xy

module Newmans-Lemma where -- SN ∧ WCR → CR

  CR-lemma : ∀ (R : 𝓡 A) → weakly-confluent R → ∀ x → is R -SN x
               → ∀ y → is R -NF y → (R ⋆) x y → ∀ z → (R ⋆) x z → (R ⋆) z y
  CR-lemma R wcR x (acc xacc) .x y∈NF ε⋆ .x ε⋆ = ε⋆
  CR-lemma R wcR x (acc xacc) .x y∈NF ε⋆ z (Rxy ,⋆ R⋆yz) = ∅ (y∈NF _ Rxy )
  CR-lemma R wcR x (acc xacc) y y∈NF (Rxy₀ ,⋆ R⋆y₀y) .x ε⋆ = Rxy₀ ,⋆ R⋆y₀y
  CR-lemma R wcR x (acc xacc) y y∈NF (Rxy₀ ,⋆ R⋆y₀y) z (Rxz₀ ,⋆ R⋆z₀z)
    with wcR (x ,, Rxy₀ , Rxz₀)
  ... | (w ,, R⋆y₀w , R⋆z₀w) with CR-lemma R wcR _ (xacc _ Rxy₀) y y∈NF R⋆y₀y w R⋆y₀w
  ... | c = CR-lemma R wcR _ (xacc _ Rxz₀) y y∈NF (R⋆z₀w ⋆!⋆ c) z R⋆z₀z

  WCR∧SN→UN : ∀ (R : 𝓡 A) → weakly-confluent R → ∀ x → is R -SN x → is R -UN x
  WCR∧SN→UN R wcR x xa y∈NF z∈NF R⋆xy R⋆xz with CR-lemma R wcR x xa _ y∈NF R⋆xy _ R⋆xz
  ... | R⋆zy = ~ (NF→ε R z∈NF R⋆zy)

  wCR→conflInd : ∀ {R : 𝓡 A} → weakly-confluent R → is (~R R) -inductive (λ x → is R -CR x)
  wCR→conflInd WCR a IND ε⋆ R*ac = _ ,, R*ac , ε⋆
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) ε⋆ = _ ,, ε⋆ , (Ray ,⋆ R*yb)
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) (Raz ,⋆ R*zc) with WCR (a ,, (Ray , Raz))
  ... | d ,, R*yd , R*zd with IND _ Ray R*yb R*yd
  ... | e ,, R*be , R*de with IND _ Raz R*zc (R*zd ⋆!⋆ R*de)
  ... | f ,, R*cf , R*ef = f ,, (R*be ⋆!⋆ R*ef , R*cf)

  wCR→conf : ∀ {R : 𝓡 A} → weakly-confluent R → ∀ (x : A) → is (~R R) -accessible x → is R -CR x
  wCR→conf {R} wcR = acc⊆ind (~R R) (λ x → is R -CR x) (wCR→conflInd wcR )

  NewmansLemma : ∀ {R : 𝓡 A} → SN R → weakly-confluent R → confluent R
  NewmansLemma RisSN RisWCR (a ,, R*ab , R*ac) = wCR→conf RisWCR a (RisSN a) R*ab R*ac

module Theorem-1-2-2 (R : 𝓡 A) where
  i-1a : confluent R → NFP R
  i-1a confR {x} {y} y∈NF R⁼xy with Proposition-1-1-10.i→vi confR x y R⁼xy
  ... | z ,, R⋆xz , ε⋆ = R⋆xz
  ... | z ,, R⋆xz , (Ryz ,⋆ R⋆yz) = ∅ (y∈NF _ Ryz)

  i-1b : NFP R → UN R
  i-1b RisNFP {a}{b} a∈NF b∈NF R=ab = NF→ε R a∈NF (RisNFP b∈NF R=ab)

  i-2 : confluent R → UN R
  i-2 confR {x} {y} x∈NF y∈NF R⁼xy with Proposition-1-1-10.i→vi confR x y R⁼xy
  ... | y ,, ε⋆ , ε⋆ = refl
  ... | y ,, (Rxw ,⋆ R⋆wy') , ε⋆ = ∅ (x∈NF _ Rxw )
  ... | z ,, R⋆xz , (Ryz ,⋆ R⋆yz) = ∅ (y∈NF _ Ryz)

  i-3 : confluent R → NFP R × UN R
  i-3 confR = (i-1a confR) , (i-2 confR)

  i-4 : confluent R → NFP R → UN R
  i-4 confR nfpR = pr2 (i-3 confR)

  lemmaii : WN R → UN R → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
  lemmaii wnR unR x y R⁼xy with wnR x
  ... | nˣ ,, R*xnˣ , nˣ∈NF with wnR y
  ... | nʸ ,, R*ynʸ , nʸ∈NF with unR nˣ∈NF nʸ∈NF (⋆~!⁼!⋆ R*xnˣ R⁼xy R*ynʸ)
  ... | refl = nʸ ,, R*xnˣ , R*ynʸ

  ii : WN R × UN R → confluent R
  ii (wnR , unR) {b}{c} peak@(a ,, R*ab , R*ac) with wnR a
  ... | n ,, R*an , n∈NF with Proposition-1-1-10.vi→i (lemmaii wnR unR) peak
  ... | d ,, R*bd , R*cd = d ,, R*bd , R*cd

  iii : subcommutative R → confluent R
  iii scR {b}{c} peak = Proposition-1-1-10.v→i (λ { b c (a ,, Rab , R*ac) → f b c a Rab R*ac } ) peak  where
      f : (x y z : A) → R z x → (R ⋆) z y → ((R ⋆) ∘R ~R (R ⋆)) x y
      f x y .y Rzx ε⋆ = x ,, ε⋆ , (Rzx ,⋆ ε⋆)
      f x y z Rzx (Rzy₁ ,⋆ R*y₁y) with scR (z ,, (Rzx , Rzy₁))
      ... | d ,, R , εʳ = y ,, R ʳ!⋆ R*y₁y , ε⋆
      ... | d ,, Rʳxd , axʳ x₁ with f d y _ x₁ R*y₁y
      ... | w ,, R*dw , R*yw = w ,, (Rʳxd ʳ!⋆ R*dw ) , R*yw

module Miscellaneous (R : 𝓡 A) where

  ¬¬NF⊆NF : ∀ x → ¬¬ (is R -NF x) → is R -NF x
  ¬¬NF⊆NF x nnNFx y Rxy = nnNFx λ x∈NF → x∈NF y Rxy

  open ReductionClosureProperties using (rec↓⊆rec)

  -- ¬¬R⊆R : ∀ x → ¬¬ (is R -recurrent x) → is R -recurrent x
  -- ¬¬R⊆R x nnRx .x ε⋆ = ε⋆
  -- ¬¬R⊆R x nnRx y (_,⋆_ {y = z} Rxz R*zy)
  --   with ¬¬R⊆R z (λ z∉R → nnRx (λ x∈R → z∉R (rec↓⊆rec R x∈R (Rxz ,⋆ ε⋆)) ) ) y R*zy
  -- ... | c = {!   !}

  -- Recurrent property
  RP : Set
  -- RP = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
  RP = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (is R - f bound a)
         → Σ[ m ∈ ℕ ] is R -recurrent (f m)

  RP- : Set
  RP- = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (is R - f bound a)
          → Σ[ i ∈ ℕ ] ((R ⋆) a (f i))

  RP→RP- : RP → RP-
  RP→RP- RisRP f f-inc b bis-bound with RisRP f f-inc b bis-bound
  ... | i ,, i∈RP = i ,, (i∈RP b (bis-bound i))

  RP-lemma : ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (is R - f bound a)
          →  ∀ i → (R ⋆) a (f i) → ∀ x → (R ⋆) (f i) x → is R - f bound x
  RP-lemma f f-inc a aisf-bound i R*afᵢ y R*fᵢy n = (aisf-bound n ⋆!⋆ R*afᵢ) ⋆!⋆ R*fᵢy

  RP-→RP : RP- → RP
  RP-→RP RP- f f-inc a aisf-bound with RP- f f-inc a aisf-bound
  ... | i ,, R*afᵢ = i ,, proof
    where   proof : (y : A) (R*fᵢy : (R ⋆) (f i) y) → (R ⋆) y (f i)
            proof y R*fᵢy with RP-lemma f f-inc a aisf-bound i R*afᵢ y R*fᵢy
            ... | yisf-bound with RP- f f-inc y yisf-bound
            ... | j ,, R*yfⱼ = R*yfⱼ ⋆!⋆ (aisf-bound j ⋆!⋆ R*afᵢ)

  CR→WCR : CR R → WCR R
  CR→WCR RisCR x Rxy Rxz = RisCR x (Rxy ,⋆ ε⋆) (Rxz ,⋆ ε⋆)

  -- Hard goal 1
  -- SN∧WNFP→CRloc : ∀ x → is R -WNFP x → is R -SN x → is R -CR x
  -- SN∧WNFP→CRloc x x∈WNFP (acc xa) {b} {c} R*xb R*xc = {!   !}

  module OldProofOfNL where
    -- This is actually an if-and-only-if...
    CR→CRelem : ∀ (R : 𝓡 A) → (confluent R) → CR R
    CR→CRelem R RisCR x =  λ z z₁ → RisCR (x ,, z , z₁)

    -- This should be easy.
    -- Question: what if WN is global?      [***]
    WNg∧UN→CRelem : ∀ (R : 𝓡 A) → WN R → ∀ x → is R -UN x → is R -CR x
    WNg∧UN→CRelem R wnR x x∈UN = {!   !}

    -- Looks true, perhaps messy
    -- Question: WN ∧ (∀ x → UN(x)) → UN(R) ?

    -- SN∩UN⊆NP, also need to prove: UN↓⊆UN
    UN-lemma : ∀ (R : 𝓡 A) → decMin (~R R) → ∀ x → is R -SN x → is R -UN x
                  → ∀ y → is R -NF y → (R ⋆) x y → ∀ z → (R ⋆) x z → (R ⋆) z y
    UN-lemma R decNF x x∈SN x∈UN y y∈NF R*xy .x ε⋆ = R*xy
    UN-lemma R decNF x (acc xacc) x∈UN y y∈NF R*xy z (Rxz₀ ,⋆ R*z₀z)
      with SNdec→WN R decNF _ (xacc _ Rxz₀)
    ... | z' ,, R*z₀z' , z'∈NF with x∈UN y∈NF z'∈NF R*xy (Rxz₀ ,⋆ R*z₀z')
    ... | refl = UN-lemma R decNF _ (xacc _ Rxz₀) (λ {a} {b} → z₀∈UN {a} {b}) y y∈NF R*z₀z' z R*z₀z
      where z₀∈UN = λ {a} {b} a∈NF b∈NF R*z₀a R*z₀b → x∈UN a∈NF b∈NF (Rxz₀ ,⋆ R*z₀a) (Rxz₀ ,⋆ R*z₀b)

    -- SN∩UN⊆CR, try to do this by induction on accessibility, without relying on SN⊆WN
    SN∧UN→CRelem : ∀ (R : 𝓡 A) → decMin (~R R) → ∀ x → is R -SN x → is R -UN x → is R -CR x
    SN∧UN→CRelem R decNF x x∈SN x∈UN {b} {c} R*xb R*xc with SNdec→WN R decNF x x∈SN
    ... | (z ,, R*xz , z∈NF) = (z ,, UN-lemma R decNF x x∈SN x∈UN z z∈NF R*xz b R*xb
                                   , UN-lemma R decNF x x∈SN x∈UN z z∈NF R*xz c R*xc )

open Miscellaneous public

module Theorem-1-2-3 (R : 𝓡 A) where

  seq-lemma : ∀ (f : ℕ → A) → is R -increasing f → ∀ n → (R ⋆) (f zero) (f n)
  seq-lemma f f-inc zero = ε⋆
  seq-lemma f f-inc (succ n) = f-inc zero ,⋆ seq-lemma (f ∘ succ) (λ k → f-inc (succ k)) n

  seq-lemma2 : ∀ (f : ℕ → A) → is R -increasing f → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
  seq-lemma2 f f-inc zero m = in1 (seq-lemma f f-inc m)
  seq-lemma2 f f-inc (succ n) zero = in2 (seq-lemma f f-inc (succ n))
  seq-lemma2 f f-inc (succ n) (succ m) = seq-lemma2 (f ∘ succ) (λ k → f-inc (succ k) ) n m


  refl-closure-lemma : ∀ (Φ : (∀ x y → (R ʳ) x y → Set))
                         (Φax  : ∀ x y (ρ : R x y) → Φ x y (axʳ ρ))
                         (Φeps : ∀ x y (p : x ≡ y) → Φ x y (transp ((R ʳ) x) p εʳ) )
                         → ∀ x y (ρ : (R ʳ) x y) → Φ x y ρ
  refl-closure-lemma Φ Φax Φeps x y (axʳ ρ) = Φax x y ρ
  refl-closure-lemma Φ Φax Φeps x .x εʳ = Φeps x x refl

  wseq-lemma : ∀ (f : ℕ → A) → is (R ʳ) -increasing f → ∀ n → (R ⋆) (f zero) (f n)
  wseq-lemma f f-winc zero = ε⋆
  wseq-lemma f f-winc (succ n) =
    let Φ = λ x y Rʳxy → (R ⋆) y (f (succ n)) → (R ⋆) x (f (succ n))
        Φax = λ x y → _,⋆_
        Φeps = λ { x .x refl → I }
        rcl = refl-closure-lemma Φ Φax Φeps (f zero) (f (succ zero)) (f-winc zero)
      in rcl (wseq-lemma (f ∘ succ) (λ k → f-winc (succ k)) n)

  wseq-lemma2 : ∀ (f : ℕ → A) → is (R ʳ) -increasing f → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
  wseq-lemma2 f f-winc zero m = in1 (wseq-lemma f f-winc m)
  wseq-lemma2 f f-winc (succ n) zero = in2 (wseq-lemma f f-winc (succ n))
  wseq-lemma2 f f-winc (succ n) (succ m) = wseq-lemma2 (f ∘ succ) (λ k → f-winc (succ k) ) n m

  i : WN R → UN R → bounded R
  i RisWN RisUN f f-inc with RisWN (f zero)
  ... | (n ,, R*f0n , n∈NF) = n ,, g where
    g : ∀ k → (R ⋆) (f k) n
    g k with Theorem-1-2-2.ii R (RisWN , RisUN) (f 0 ,, R*f0n , (seq-lemma f f-inc k) )
    ... | .n ,, ε⋆ , R*fkn = R*fkn
    ... | n' ,, (Rnn₀ ,⋆ R*n₀n') , R*fkn = ∅ (n∈NF _ Rnn₀ )

  -- Strengthening i
  i+ : WN R → UN→ R → bounded R
  i+ RisWN RisUN→ f f-inc  with RisWN (f zero)
  ... | (a ,, R*f0a , a∈NF) = a ,, g where
    g : ∀ k → (R ⋆) (f k) a
    g k with RisWN (f k)
    ... | b ,, R*fkb , b∈NF with RisUN→ (f zero) a∈NF b∈NF R*f0a ((seq-lemma f f-inc k) ⋆!⋆ R*fkb)
    ... | refl = R*fkb

  ii3- :  WN R → UN R → RP R → isWFseq- (~R R)
  ii3- wnR unR rp s sIsRdec with i wnR unR
  ... | bdR with wnR (s 0)
  ... | a ,, R*s₀a , a∈NF with bdR s sIsRdec
  ... | b ,, bisωLimit with bisωLimit 0
  ... | R*s₀b with rp s sIsRdec b bisωLimit
  ... | c ,, ScisRecurrent with Theorem-1-2-2.ii R (wnR , unR)
  ... | RisCR with RisCR ((s 0) ,, R*s₀a , seq-lemma s sIsRdec c)
  ... | d ,, (Raa₁ ,⋆ R*a₁d) , R*bd = a∈NF _ Raa₁
  ... | .a ,, ε⋆ , R*sca with ScisRecurrent a (R*sca)
  ... | Raa₃ ,⋆ R*as_c = a∈NF _ Raa₃
  ... | ε⋆ = a∈NF (s (succ c)) (sIsRdec c) -- if a and S c are the same, then a has the recurrent property which leads to contradiction




  -- A classical proof of iii (subbing RP for Inc)
  open import Classical
  -- open ClassicalImplications

  -- A classical assumption which nonetheless may be necessary to assume
  ¬NFx→Rxy : ∀ {x} → isMinDec (~R R) x → ¬ (is R -NF x) →  Σ[ y ∈ A ] (R x y)
  ¬NFx→Rxy {x} xdec x∉NF with xdec
  ... | in1 yRxy = yRxy
  ... | in2 x∈NF = ∅ (x∉NF x∈NF)

  -- Stronger version of the above
  -- This reminds me of deMorgan from early WF file
  x∉SN→∃y∉SN : ∀ {x} → ¬(is R -SN x) → Σ[ y ∈ A ] (¬(is R -SN y) × R x y)
  x∉SN→∃y∉SN {x} x∉SN = {!   !}  -- Can't think how to progress this

  ¬SN∧NF→⊥ : ∀ {x} → ¬ (is R -SN x) → is R -NF x → ⊥
  ¬SN∧NF→⊥ x∉SN x∈NF = x∉SN (acc (λ y Rxy → ∅ (x∈NF _ Rxy)))

  -- -- Classical proof in the report
  -- iii :  WN R → WCR R → RP R → isWFseq- (~R R)

  acc∧WN→NF : ∀ {x} → is R -accessible x → is R -WN x →  Σ[ y ∈ A ] (is R -NF y) -- This is obvious, just coming from the fact that we are WN, not using accessible at all!
  acc∧WN→NF (acc xacc) (n ,, R*xn , n∈NF) = n ,, n∈NF

  record preSN (n x : A) : Set where
    constructor pSN
    field
      n∈NF : is R -NF n
      x∉SN : ¬ (is R -SN x)
      s : A
      x→s : R x s
      s→n : (R ⋆) s n
      s∈SN : is R -SN s

  preSNlemma1 : dec (SN R) → ∀ {x n} → (R ⋆) x n → is R -NF n → ¬ is R -SN x →
                                  Σ[ y ∈ A ] ((R ⋆) x y × preSN n y)
  preSNlemma1 decSN {x} {.x} ε⋆ n∈NF x∉SN = ∅ (¬SN∧NF→⊥ x∉SN n∈NF )
  preSNlemma1 decSN {x} {n} (_,⋆_ {y = y} Rxy R*yn) n∈NF x∉SN
    with decSN y
  ... | in1 y∈SN = x ,, (ε⋆ , pSN n∈NF x∉SN y Rxy R*yn y∈SN)
  ... | in2 y∉SN
    with preSNlemma1 decSN R*yn n∈NF y∉SN
  ... | (z ,, R*yz , p) = (z ,, (Rxy ,⋆ R*yz , p ))

  open Newmans-Lemma

  WCR→SN⊆NP : WCR R → ∀ x → is R -SN x → is R -WNFP x
  WCR→SN⊆NP RisWCR x x∈SN y∈NF R*xy R*xz
    with wCR→conf (λ (a ,, Rab , Rac) → RisWCR a Rab Rac) x x∈SN R*xy R*xz
  ... | w ,, ε⋆ , R*zw = R*zw
  ... | w ,, (Ry- ,⋆ _) , R*zw = ∅ (y∈NF _ Ry-)

  preSNlemma2 : WCR R → dec (SN R) →
                ∀ n x → preSN n x → Σ[ y ∈ A ] ((R ⁺) x y × preSN n y)
  preSNlemma2 RisWCR decSN n x (pSN n∈NF x∉SN s x→s s→n s∈SN)
    with x∉SN→∃y∉SN x∉SN
  ... | (y ,, y∉SN , Rxy)
    with RisWCR x x→s Rxy
  ... | (z ,, R*sz , R*yz)
    with preSNlemma1 decSN (R*yz ⋆!⋆ WCR→SN⊆NP RisWCR s s∈SN n∈NF s→n R*sz )  n∈NF y∉SN
  ... | (v ,, R*yv , p) = (v ,, RR⋆⊆R⁺ R Rxy R*yv , p)

  preSNlemma3 : WCR R → dec (SN R) → ∀ n x → preSN n x →
                  Σ[ f ∈ (ℕ → A) ] ((∀ k → preSN n (f k)) × is (R ⁺) -increasing f)
  preSNlemma3 RisWCR decSN n x p = f ,, pf , finc where
    f : ℕ → A
    pf : ∀ (k : ℕ) → preSN n (f k)
    f zero = x
    f (succ k) = fst (preSNlemma2 RisWCR decSN n (f k) (pf k))
    pf zero = p
    pf (succ k) = pr2 (snd (preSNlemma2 RisWCR decSN n (f k) (pf k)))
    finc : is R ⁺ -increasing f
    finc k = pr1 (snd (preSNlemma2 RisWCR decSN n (f k) (pf k)))

  seq→sseq : ∀ (f : ℕ → A) → is (R ⁺) -increasing f → ∀ (k : ℕ) → Σ[ a ∈ A ] (R ⋆) a (f k)
  seq→sseq f finc zero = f zero ,, ε⋆
  seq→sseq f finc (succ k)
    with seq→sseq f finc k
  ... | x ,, (_,⋆_ {y = y} h r) = y ,, (r ⋆!⋆ ⁺→⋆ R (finc k) )
  ... | .(f k) ,, ε⋆ with finc k
  ... | (_,⁺_ {y = y} h r) = (y ,, ⁺→⋆ R  r )
  ... | ε⁺ = f (succ k) ,, ε⋆

  seq→sseq-inc :  ∀ (f : ℕ → A) (finc : is (R ⁺) -increasing f)
                   → is R -increasing (λ k → fst (seq→sseq f finc k))
  seq→sseq-inc f finc zero with seq→sseq f finc zero | finc zero
  ... | x ,, (x₁ ,⋆ R*xf0) | ax⁺ f0f1 = f0f1
  ... | x ,, (x₁ ,⋆ R*xf0) | h ,⁺ t = h
  ... | .(f 0) ,, ε⋆ | ax⁺ f0f1 = f0f1
  ... | .(f 0) ,, ε⋆ | h ,⁺ t = h
  seq→sseq-inc f finc (succ k) with seq→sseq f finc (succ k)
  ... | x ,, (h ,⋆ x→fsk) = h
  ... | .(f (succ k)) ,, ε⋆ with finc (succ k)
  ... | ax⁺ h = h
  ... | h ,⁺ c = h

  seq→sseq-bnd : ∀ (f : ℕ → A) (finc : is (R ⁺) -increasing f) (b : A) →
               is R - f bound b → is R - (λ k → fst (seq→sseq f finc k)) bound b
  seq→sseq-bnd f finc b fbnd k = snd (seq→sseq f finc k) ⋆!⋆ (fbnd k)

  Theorem123Lemma : WCR R → dec (SN R) → ∀ n x → preSN n x →
                    Σ[ f ∈ (ℕ → A) ] (is R -increasing f × is R - f bound n)
  Theorem123Lemma RisWCR decSN n x p
    with preSNlemma3 RisWCR decSN n x p
  ... | (f ,, pf , fisR+inc) =
        (λ k → fst (seq→sseq f fisR+inc k))
        ,,  seq→sseq-inc f fisR+inc
          , seq→sseq-bnd f fisR+inc n (λ k → x→s (pf k) ,⋆ s→n (pf k) ) where open preSN


  Theorem123_iii : WN R → WCR R → RP- R → dec (is_-SN_ R) → SN R
  Theorem123_iii RisWN RisWCR RisRP decSN x with decSN x
  ... | in1 x∈SN = x∈SN
  ... | in2 x∉SN with RisWN x
  ... | n ,, R*xn , n∈NF with preSNlemma1 decSN R*xn n∈NF x∉SN
  ... | b₀ ,, R*xb₀ , nb₀∈preSN with Theorem123Lemma RisWCR decSN n b₀ nb₀∈preSN
  ... | s ,, s-inc , n∈s-bound with RisRP s s-inc n n∈s-bound
  ... | i ,, ε⋆ = ∅ (n∈NF _ (s-inc i))
  ... | i ,, (Rnz ,⋆ R*zsᵢ) = ∅ (n∈NF _ Rnz)



  iv : CP R → confluent R
  iv RhasCP (a ,, R*ab , R*ac) with RhasCP a
  ... | f ,, f-winc , (refl , fisCof) with fisCof _ R*ab | fisCof _ R*ac
  ... | bₙ ,, R*bfbₙ | cₙ ,, R*cfcₙ
    with wseq-lemma2 f f-winc bₙ cₙ
  ... | in1 R*fbₙfcₙ = (f cₙ) ,, ((R*bfbₙ ⋆!⋆ R*fbₙfcₙ) , R*cfcₙ)
  ... | in2 R*fcₙfbₙ = (f bₙ) ,, R*bfbₙ , (R*cfcₙ ⋆!⋆ R*fcₙfbₙ)

-- Useful dead-ends



  -- Comp : Set
  -- Comp = ∀ (f : ℕ → A) → is (R ⋆) -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
  --           → Σ[ m ∈ ℕ ] ∀ k → f (add k m) ≡ f m
