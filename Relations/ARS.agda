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
    commute Rβ = ∀ {a}{b}{c} → (Rα ⋆) a b → (Rβ ⋆) a c → Σ[ d ∈ A ] ((Rβ ⋆) b d × (Rα ⋆) c d)

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

    i→v : confluent R → ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)
    i→v confR b c (a ,, Rab , R*ac) = confR (a ,, ax⋆ R Rab , R*ac)

    v→vi : (~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆)) → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
    v→vi v a .a ε⋆ = a ,, ε⋆ , ε⋆
    v→vi v a b (Rˢac ,⋆ EQRcb) with v→vi v _ b EQRcb
    ... | d ,, R*cd , R*bd with Rˢac
    ... | axˢ+ Ray = d ,, (Ray ,⋆ R*cd) , R*bd
    ... | axˢ- Rya with v a d (_ ,, (Rya , R*cd))
    ... | e ,, R*ae , R*de = e ,, (R*ae , ( R*bd ⋆!⋆ R*de ))

    vi→i : R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆) → confluent R
    vi→i vi {b}{c} peak@(a ,, R*ab , R*ac)  with vi b c ((~⁼ (⋆⊆⁼ R R*ab)) ⁼!⁼ (⋆⊆⁼ R R*ac))
    ... | d ,, R*cd , R*bd = d ,, (R*cd , R*bd)

    i→vi : confluent R → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
    i→vi confR = v→vi (i→v confR)

    v→i : ~R R ∘R (R ⋆) ⊆ (R ⋆) ∘R ~R (R ⋆) → confluent R
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

open ClassicalImplications using (decMin)

-- Notions related to termination in ARSs
module Termination (R : 𝓡 A)  where

  open import Relations.Wellfounded

  is_-NF_ : 𝓟 A
  is_-NF_ x = ∀ y → ¬ R x y
  -- is_-NF_ x = R x ⊆ K⊥

  is_-WN_ : 𝓟 A
  is_-WN_ x = Σ[ n ∈ A ] ((R ⋆) x n × is_-NF_ n)

  is_-SNacc_ : 𝓟 A
  is_-SNacc_ x = is (~R R) -accessible x

  is_-SN_ : 𝓟 A
  is_-SN_ = is_-SNacc_

  is_-UN_ : 𝓟 A
  is_-UN_ x = ∀ y → is_-NF_ y → (R ⋆) x y → ∀ z → is_-NF_ z → (R ⋆) x z → y ≡ z

  is_-recurrent_ : 𝓟 A
  is_-recurrent_ x = ∀ y → (R ⋆) x y → (R ⋆) y x

  CR : Set
  CR = confluent R

  WCR : Set
  WCR = weakly-confluent R

  WN : Set
  WN = ∀ x → is_-WN_ x

  SN : Set
  SN = ∀ x → is_-SN_ x

  NFP : Set
  NFP = ∀ {a b} → is_-NF_ b → (R ⁼) a b → (R ⋆) a b

  UN : Set
  UN = ∀ {a b : A} → a ∈ is_-NF_ → b ∈ is_-NF_ → (R ⁼) a b → a ≡ b

  UN→ : Set
  UN→ = ∀ {x a b : A} → a ∈ is_-NF_ → b ∈ is_-NF_  → (R ⋆) x a → (R ⋆) x b → a ≡ b

  -- AKA Convergent
  isComplete : Set
  isComplete = CR × SN

  isSemicomplete : Set
  isSemicomplete = UN × WN

  -- Miscelaneous properties
  ω-bounded : Set
  ω-bounded = ∀ (f : ℕ → A) → is R -increasing f → Σ[ a ∈ A ] (∀ n → (R ⋆) (f n) a)

  dominatedByWF : 𝓡 A → Set
  dominatedByWF Q = isWFacc Q × (R ⊆ Q)

  isFinitelyBranching : Set
  isFinitelyBranching = ∀ (a : A)
    → Σ[ n ∈ ℕ ] (Σ[ f ∈ (Fin n → A) ] (∀ b → R a b → Σ[ j ∈ Fin n ] (b ≡ f j)))

  is_-cofinal_ : 𝓟 A → Set
  is_-cofinal_ B = ∀ (x : A) → Σ[ y ∈ A ] ((R ⋆) x y × y ∈ B)

  -- Cofinality Property
  CP : Set
  CP = ∀ (a : A) → Σ[ s ∈ (ℕ → A) ] ((is (R ʳ) -increasing s) ×
                    (s zero ≡ a × (∀ b → (R ⋆) a b → Σ[ n ∈ ℕ ] ((R ⋆) b (s n))) ))

  NF→ε : ∀ {x} → x ∈ is_-NF_ → ∀ {y} → (R ⋆) x y → x ≡ y
  NF→ε {x} x∈NF {.x} ε⋆ = refl
  NF→ε {x} x∈NF {y} (Rxy₀ ,⋆ R⋆y₀y) = ∅ (x∈NF _ Rxy₀ )


  SNdec→WN : decMin (~R R) → is_-SN_ ⊆ is_-WN_
  SNdec→WN decR x (acc accx) with decR x
  ... | in2 y∈NF = x ,, (ε⋆ , y∈NF)
  ... | in1 (y ,, Rxy) with SNdec→WN decR y (accx y Rxy)
  ... | (n ,, R*yn , n∈NF) = (n ,, (Rxy ,⋆ R*yn) , n∈NF)

  confluentElement : 𝓟 A
  confluentElement a = ∀ {b c} → (R ⋆) a b → (R ⋆) a c → Σ[ d ∈ A ] ((R ⋆) b d × (R ⋆) c d)

  unormElement : 𝓟 A
  unormElement a = Σ[ n ∈ A ] ((is_-NF_ n) × (∀ y → (R ⋆) a y → (R ⋆) y n))


open Termination public

module ReductionClosureProperties (R : 𝓡 A) where
  SN↓⊆SN : ∀ {x} → is R -SN x → ∀ {y} → (R ⋆) x y → is R -SN y
  SN↓⊆SN isR-SNx ε⋆ = isR-SNx
  SN↓⊆SN isR-SNx@(acc xacc) (Rxx₁ ,⋆ R*x₁y) = SN↓⊆SN (xacc _ Rxx₁) R*x₁y

  NF↓⊆NF : ∀ {x} → is R -NF x → ∀ {y} → (R ⋆) x y → is R -NF y
  NF↓⊆NF isR-NFx ε⋆ = isR-NFx
  NF↓⊆NF isR-NFx (Rxx₁ ,⋆ R*x₁y) = λ y _ → isR-NFx _ Rxx₁

  -- SA: This shouldn't be true. Counter: x ->> n and x ->> y (x ∈ WN). y -> z and z -> y and y and z have no other reductions.
  -- should follow with the assumption of UN→
  WN↓⊆WN : ∀ {x} → is R -WN x → ∀ {y} → (R ⋆) x y → is R -WN y
  WN↓⊆WN isR-WNx ε⋆ = isR-WNx
  WN↓⊆WN (x ,, R*xn , n∈NF) (Rxx₁ ,⋆ R*x₁y) = WN↓⊆WN ({!   !} ,, {!   !}) R*x₁y

  WN↓UN→⊆WN : UN→ R → ∀ {x} → is R -WN x → ∀ {y} → (R ⋆) x y → is R -WN y
  WN↓UN→⊆WN RisUN→ isR-WNx ε⋆ = isR-WNx
  WN↓UN→⊆WN RisUN→ (n ,, R*xn , n∈NF) (Rxx₁ ,⋆ R*x₁y) = {!   !}  
  
  UN↓⊆UN : ∀ {x} → is R -UN x → ∀ {y} → (R ⋆) x y → is R -UN y
  UN↓⊆UN isR-UNx R*xy y n∈NF R*yn z z∈NF R*yz = isR-UNx _ n∈NF (R*xy ⋆!⋆ R*yn) z z∈NF (R*xy ⋆!⋆ R*yz)

  rec↓⊆rec : ∀ {x} → is R -recurrent x → ∀ {y} → (R ⋆) x y → is R -recurrent y
  rec↓⊆rec isR-recx R*xy z R*yz with isR-recx z (R*xy ⋆!⋆ R*yz)
  ... | R*zx  = R*zx ⋆!⋆ R*xy

module Newmans-Lemma where
  -- If R is SN and WCR then R is CR

  -- Three proofs in Therese.
  -- i) By SN, every a ∈ A reduces to at least one normal form. For CR it suffices to show that every a ∈ A has at most one normal form.
  -- ii) As → is SN, ← is WF, and hence ←⁺ is a well founded order...
  -- iii)

  -- Proof i
  -- Requires being able to decide whether a given element is already a NF.


  CR-lemma : ∀ (R : 𝓡 A) → WCR R → ∀ x → is R -SN x
               → ∀ y → is R -NF y → (R ⋆) x y → ∀ z → (R ⋆) x z → (R ⋆) z y
  CR-lemma R wcR x (acc xacc) .x y∈NF ε⋆ .x ε⋆ = ε⋆
  CR-lemma R wcR x (acc xacc) .x y∈NF ε⋆ z (Rxy ,⋆ R⋆yz) = ∅ (y∈NF _ Rxy )
  CR-lemma R wcR x (acc xacc) y y∈NF (Rxy₀ ,⋆ R⋆y₀y) .x ε⋆ = Rxy₀ ,⋆ R⋆y₀y
  CR-lemma R wcR x (acc xacc) y y∈NF (Rxy₀ ,⋆ R⋆y₀y) z (Rxz₀ ,⋆ R⋆z₀z)
    with wcR (x ,, Rxy₀ , Rxz₀)
  ... | (w ,, R⋆y₀w , R⋆z₀w) with CR-lemma R wcR _ (xacc _ Rxy₀) y y∈NF R⋆y₀y w R⋆y₀w
  ... | c = CR-lemma R wcR _ (xacc _ Rxz₀) y y∈NF (R⋆z₀w ⋆!⋆ c) z R⋆z₀z

  WCR∧SN→UN : ∀ (R : 𝓡 A) → WCR R → ∀ x → is R -SN x → is R -UN x
  WCR∧SN→UN R wcR x xa y y∈NF R⋆xy z z∈NF R⋆xz with CR-lemma R wcR x xa y y∈NF R⋆xy z R⋆xz
  ... | R⋆zy = ~ (NF→ε R z∈NF R⋆zy)

  -- ***

  CR→CRelem : ∀ (R : 𝓡 A) → (CR R) → (∀ x → confluentElement R x)
  CR→CRelem R RisCR x =  λ z z₁ → RisCR (x ,, z , z₁)


  -- Not provable, unless WN is global. [***]
  -- FIND a counterexample and delete?
  -- Derive it from (ii) below??
  WN∧UN→CRelem : ∀ (R : 𝓡 A) → ∀ x → is R -WN x → is R -UN x → confluentElement R x
  WN∧UN→CRelem R x (z ,, R*xz , z∈NF) x∈UN {b} {c} R*xb R*xc = {!   !}

  UN-lemma : ∀ (R : 𝓡 A) → decMin (~R R) → ∀ x → is R -SN x → is R -UN x
                → ∀ y → is R -NF y → (R ⋆) x y → ∀ z → (R ⋆) x z → (R ⋆) z y
  UN-lemma R decNF x x∈SN x∈UN y y∈NF R*xy .x ε⋆ = R*xy
  UN-lemma R decNF x (acc xacc) x∈UN y y∈NF R*xy z (Rxz₀ ,⋆ R*z₀z)
    with SNdec→WN R decNF _ (xacc _ Rxz₀)
  ... | z' ,, R*z₀z' , z'∈NF with x∈UN y y∈NF R*xy z' z'∈NF (Rxz₀ ,⋆ R*z₀z')
  ... | refl = UN-lemma R decNF _ (xacc _ Rxz₀) z₀∈UN y y∈NF R*z₀z' z R*z₀z
    where z₀∈UN = λ a a∈NF R*z₀a b b∈NF R*z₀b → x∈UN a a∈NF (Rxz₀ ,⋆ R*z₀a) b b∈NF (Rxz₀ ,⋆ R*z₀b)

  SN∧UN→CRelem : ∀ (R : 𝓡 A) → decMin (~R R) → ∀ x → is R -SN x → is R -UN x → confluentElement R x
  SN∧UN→CRelem R decNF x x∈SN x∈UN {b} {c} R*xb R*xc with SNdec→WN R decNF x x∈SN
  ... | (z ,, R*xz , z∈NF) = (z ,, UN-lemma R decNF x x∈SN x∈UN z z∈NF R*xz b R*xb
                                 , UN-lemma R decNF x x∈SN x∈UN z z∈NF R*xz c R*xc )

  {- First proof of NL
  is-ambiguous_-WN_ : ∀ (R : 𝓡 A) → 𝓟 A
  is-ambiguous R -WN  x = Σ[ n₁ ∈ A ] Σ[ n₂ ∈ A ] ((((R ⋆) x n₁ × is R -NF n₁) × ((R ⋆) x n₂ × is R -NF n₂)) × (n₁ ≡ n₂ → ⊥) )

  ambiguous-reduces-ambiguous : ∀ {R : 𝓡 A} {a b : A} → is-ambiguous R -WN a → R a b → is-ambiguous R -WN b
  ambiguous-reduces-ambiguous (n₁ ,, n₂ ,, ((R*an₁ , n₁∈NF) , (R*an₂ , n₂∈NF)) , n₁≢₂) Rab
            =  n₁ ,, n₂ ,, ((({!   !} , n₁∈NF) , ({!   !} , n₂∈NF)) , n₁≢₂)

  lemmanorm : ∀ {R : 𝓡 A} → ∀ (a : A) → ∀ (b : A) → R a b → is R -WN b →
                              Σ A (λ n → ((y : A) → R n y → ⊥) ×
                                ((y : A) → (R ⋆) a y → (R ⋆) y n))
  lemmanorm a b Rab (n ,, R*bn , n∈NF) = n ,, (n∈NF , (λ y R*ay → {!   !}))

  lemmaWN : ∀ {R : 𝓡 A} → weakly-confluent R → ∀ (a : A) → (∀ b → R a b → is R -WN b) → is R -WN a
  lemmaWN wcR a IH = {!   !}

  NFPel : ∀ {R : 𝓡 A} → decMin (~R R) → weakly-confluent R
            → ∀ a → is (~R R) -accessible a → unormElement R a
  NFPel {R} Rdec wcR a (acc IH) with Rdec a
  ... | in2 a∈NF = a ,, (a∈NF , λ { y ε⋆ → ε⋆ ; y (Raz ,⋆ R*zy) → ∅ (a∈NF _ Raz)})
  ... | in1 (b ,, Rab) with NFPel Rdec wcR b (IH b Rab)
  ... | n ,, n∈NF , n∈cofb = -- lemmanorm a b Rab (n ,, ((n∈cofb b ε⋆) , n∈NF))
                            n ,, n∈NF , λ y R*ay → {!   !}  where
    f : ∀ (y : A) → (R ⋆) a y → (R ⋆) y n
    f y ε⋆ = Rab ,⋆ n∈cofb b ε⋆
    f y (Raz ,⋆ R*zy) = {!   !}

  -- NLemmai : ∀ {R : 𝓡 A} → SN R → weakly-confluent R → confluent R
  -- NLemmai SNR WCR with SN→NFelement SNR {!   !}
  -- ... | n ,, R*an , NFn = {!   !}
  -}

  -- Proof ii

  -- SNisWFacc : ∀ {R : 𝓡 A} {x : A} → is R -SN x → is (~R R) -accessible x
  -- SNisWFacc = I

  wCR→conflInd : ∀ {R : 𝓡 A} → weakly-confluent R → (x : A) → (∀ y → R x y → confluentElement R y) → confluentElement R x
  wCR→conflInd WCR a IND ε⋆ R*ac = _ ,, R*ac , ε⋆
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) ε⋆ = _ ,, ε⋆ , (Ray ,⋆ R*yb)
  wCR→conflInd WCR a IND (Ray ,⋆ R*yb) (Raz ,⋆ R*zc) with WCR (a ,, (Ray , Raz))
  ... | d ,, R*yd , R*zd with IND _ Ray R*yb R*yd
  ... | e ,, R*be , R*de with IND _ Raz R*zc (R*zd ⋆!⋆ R*de)
  ... | f ,, R*cf , R*ef = f ,, (R*be ⋆!⋆ R*ef , R*cf)

  NLemmaii : ∀ {R : 𝓡 A} → SN R → weakly-confluent R → confluent R
  NLemmaii {R} RisSN RisWCR (a ,, R*ab , R*ac) =
    isWFacc→isWFind (~R R) RisSN (confluentElement R) (wCR→conflInd RisWCR) a R*ab R*ac

  -- wCR→conf : ∀ {R : 𝓡 A} → weakly-confluent R
  --              → ∀ (x : A) → is (~R R) -accessible x → confluentElement R x
  -- wCR→conf {R} wcR x (acc IH) R⋆xb R⋆xc = {!   !}


module Theorem-1-2-2 (R : 𝓡 A) where
  i-1 : confluent R → NFP R
  i-1 confR {x} {y} y∈NF R⁼xy with Proposition-1-1-10.i→vi confR x y R⁼xy
  ... | z ,, R⋆xz , ε⋆ = R⋆xz
  ... | z ,, R⋆xz , (Ryz ,⋆ R⋆yz) = ∅ (y∈NF _ Ryz)

  i-2 : confluent R → UN R
  i-2 confR {x} {y} x∈NF y∈NF R⁼xy with Proposition-1-1-10.i→vi confR x y R⁼xy
  ... | y ,, ε⋆ , ε⋆ = refl
  ... | y ,, (Rxw ,⋆ R⋆wy') , ε⋆ = ∅ (x∈NF _ Rxw )
  ... | z ,, R⋆xz , (Ryz ,⋆ R⋆yz) = ∅ (y∈NF _ Ryz)

  i-3 : confluent R → NFP R × UN R
  i-3 confR = (i-1 confR) , (i-2 confR)

  i-4 : confluent R → NFP R → UN R
  i-4 confR nfpR = pr2 (i-3 confR)

  ⋆~!⁼!⋆ : ∀ {a b c d} → (R ⋆) a c → (R ⁼) a b → (R ⋆) b d → (R ⁼) c d
  ⋆~!⁼!⋆ R*ac R⁼ab R*bd = (~⁼ (⋆⊆⁼ R R*ac)) ⁼!⁼ (R⁼ab ⁼!⁼ ⋆⊆⁼ R R*bd)

  lemmaii : WN R → UN R → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
  lemmaii wnR unR x y R⁼xy with wnR x
  ... | nˣ ,, R*xnˣ , nˣ∈NF with wnR y
  ... | nʸ ,, R*ynʸ , nʸ∈NF with unR nˣ∈NF nʸ∈NF (⋆~!⁼!⋆ R*xnˣ R⁼xy R*ynʸ)
  ... | refl = nʸ ,, R*xnˣ , R*ynʸ

  ii : WN R × UN R → CR R
  ii (wnR , unR) {b}{c} peak@(a ,, R*ab , R*ac) with wnR a
  ... | n ,, R*an , n∈NF with Proposition-1-1-10.vi→i (lemmaii wnR unR) peak
  ... | d ,, R*bd , R*cd = d ,, R*bd , R*cd

  -- Not provable: n <- x -> z
  -- WN∧UN→CRelem : ∀ x → is R -WN x → is R -UN x → confluentElement R x
  -- WN∧UN→CRelem x x∈WN x∈UN  = Newmans-Lemma.CR→CRelem R (ii ({! x∈WN  !} , {!   !})) x -- Can we do this or am I being too bullheaded in comparing x∈UN and UN etc?

  iii : subcommutative R → confluent R
  iii scR {b}{c} peak = Proposition-1-1-10.v→i (λ { b c (a ,, Rab , R*ac) → f b c a Rab R*ac } ) peak  where
      f : (x y z : A) → R z x → (R ⋆) z y → ((R ⋆) ∘R ~R (R ⋆)) x y
      f x y .y Rzx ε⋆ = x ,, ε⋆ , (Rzx ,⋆ ε⋆)
      f x y z Rzx (Rzy₁ ,⋆ R*y₁y) with scR (z ,, (Rzx , Rzy₁))
      ... | d ,, R , εʳ = y ,, R ʳ!⋆ R*y₁y , ε⋆
      ... | d ,, Rʳxd , axʳ x₁ with f d y _ x₁ R*y₁y
      ... | w ,, R*dw , R*yw = w ,, (Rʳxd ʳ!⋆ R*dw ) , R*yw

module Miscellaneous (R : 𝓡 A) where
  -- Recurrent property
  RP : Set
  -- RP = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
  RP = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
         → Σ[ m ∈ ℕ ] is R -recurrent (f m)

  RP- : Set
  RP- = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
          → Σ[ i ∈ ℕ ] ((R ⋆) a (f i))

  RP→RP- : RP → RP-
  RP→RP- RisRP f f-inc b bisω-bound with RisRP f f-inc b bisω-bound
  ... | i ,, i∈RP = i ,, (i∈RP b (bisω-bound i))

  RP-∧WCR→RP : RP- → WCR R → RP
  RP-∧WCR→RP RisRP- RisWCR f f-inc a aisω-bound with RisRP- f f-inc a aisω-bound
  ... | i ,, R*afᵢ with aisω-bound i
  ... | R*fᵢa = {!   !} -- i ,, (λ y R*fᵢy → {!  !}) -- probably not the right step. Y isn't in sequence and so can't force it back to fᵢ via a

open Miscellaneous public

module Theorem-1-2-3 (R : 𝓡 A) where

  seq-lemma : ∀ (f : ℕ → A) → is R -increasing f → ∀ n → (R ⋆) (f zero) (f n)
  seq-lemma f f-inc zero = ε⋆
  seq-lemma f f-inc (succ n) = f-inc zero ,⋆ seq-lemma (f ∘ succ) (λ k → f-inc (succ k)) n

  seq-lemma2 : ∀ (f : ℕ → A) → is R -increasing f → ∀ n m → (R ⋆) (f n) (f m) ⊔ (R ⋆) (f m) (f n)
  seq-lemma2 f f-inc zero m = in1 (seq-lemma f f-inc m)
  seq-lemma2 f f-inc (succ n) zero = in2 (seq-lemma f f-inc (succ n))
  seq-lemma2 f f-inc (succ n) (succ m) = seq-lemma2 (f ∘ succ) (λ k → f-inc (succ k) ) n m

  -- data _ʳ (R : 𝓡 U) : 𝓡 U where
  --   axʳ : ∀ {x y : U} → R x y → (R ʳ) x y
  --   εʳ  : ∀ {x} → (R ʳ) x x

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

  i : WN R → UN R → ω-bounded R
  i RisWN RisUN f f-inc with RisWN (f zero)
  ... | (n ,, R*f0n , n∈NF) = n ,, g where
    g : ∀ k → (R ⋆) (f k) n
    g k with Theorem-1-2-2.ii R (RisWN , RisUN) (f 0 ,, R*f0n , (seq-lemma f f-inc k) )
    ... | .n ,, ε⋆ , R*fkn = R*fkn
    ... | n' ,, (Rnn₀ ,⋆ R*n₀n') , R*fkn = ∅ (n∈NF _ Rnn₀ )

  -- Strengthening i
  i+ : WN R → UN→ R → ω-bounded R
  i+ RisWN RisUN→ f f-inc  with RisWN (f zero)
  ... | (a ,, R*f0a , a∈NF) = a ,, g where
    g : ∀ k → (R ⋆) (f k) a
    g k with RisWN (f k)
    ... | b ,, R*fkb , b∈NF with RisUN→ a∈NF b∈NF R*f0a ((seq-lemma f f-inc k) ⋆!⋆ R*fkb)
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


  iii :  WN R → WCR R → RP R → isWFseq- (~R R)
  iii wnR wcrR rp s sIsRdec = {!  !}

  ii- : WN R → UN R → ω-bounded R → SN R
  ii- RisWN RisUN Risωbdd x with Theorem-1-2-2.ii R (RisWN , RisUN)
  ... | RisCR = {!   !}

  -- iii : ∀ Q → dominatedByWF R Q → WCR R → WN R → SN R
  -- iii Q domRQ RisWCR RisWN = {!   !}

  -- A classical proof of iii (subbing RP for Inc)
  open import Classical
  preSN : 𝓟 A
  preSN x = ¬ (is R -SN x) × Σ[ n ∈ A ] (is R -SN n × R x n)

  -- preSN has replaced this we think
  -- lemma-lastNonSN : ∀ {a n} → is R -NF n → (R ⋆) a n →  Σ[ b ∈ A ] ((¬ (is R -SN b)) × ((R ⋆) a b × (R ⋆) b n) )
  -- lemma-lastNonSN {a}{n} n∈NF R*an = {!   !}

  ¬SN∧NF→¬ : ∀ {x} → ¬ (is R -SN x) → is R -NF x → ⊥ 
  ¬SN∧NF→¬ x∉SN x∈NF = x∉SN (acc (λ y Rxy → ∅ (x∈NF _ Rxy))) 

  Rxy→y : ∀ {x y} → R x y → Σ[ z ∈ A ] (y ≡ z)  -- This is such a horrible botch. 
  Rxy→y {x} {y} Rxy = y ,, refl 

  preSNlemma1 : dec (is_-SN_ R) → ∀ {x} {n} → ¬ (is R -SN x) → is R -NF n → (R ⋆) x n
                          → Σ[ y ∈ A ] (preSN y × ((R ⋆) x y × (R ⋆) y n))
  preSNlemma1 SNdec {x} {.x} x∉SN x∈NF ε⋆ = ∅ (¬SN∧NF→¬ x∉SN x∈NF)
  preSNlemma1 SNdec {x} {n} x∉SN n∈NF (Rxx₁ ,⋆ R⋆x₁n) with Rxy→y Rxx₁
  ... | x₁ ,, x₁≡x₁ with SNdec x₁ 
  ... | in1 x₁∈SN = x ,, ((x∉SN , (x₁ ,, (x₁∈SN , {!   !}))) , (ε⋆ , (Rxx₁ ,⋆ R⋆x₁n)))   -- Why isn't Rxx₁ the solution here?
  ... | in2 x₁∉SN = preSNlemma1 SNdec {!   !} n∈NF {!   !} -- Why can't we take the recursive call from x₁ here?

  x∉SN→∃y∉SN : ∀ {x} → ¬(is R -SN x) → Σ[ y ∈ A ] (¬(is R -SN y) × R x y)
  x∉SN→∃y∉SN {x} x∉SN = {!   !}  -- Can't think how to progress this
  
  SN→WFacc : SN R → isWFacc (~R R) 
  SN→WFacc RisSN x with RisSN x 
  ... | acc accx = acc accx

  acc∧WN→NF : ∀ {x} → is R -accessible x → is R -WN x →  Σ[ y ∈ A ] (is R -NF y)
  acc∧WN→NF (acc xacc) (n ,, R*xn , n∈NF) = n ,, n∈NF

  WFacc→WFSeq : isWFacc (~R R) → isWFseq (~R R)
  WFacc→WFSeq RisWFacc s with RisWFacc (s 0) 
  ... | acc accs₀ = {!   !}
  
  SN∧WN→WFseq : SN R → WN R → isWFseq (~R R)
  SN∧WN→WFseq RisSN RisWN s  with RisSN (s 0)
  ... | acc xacc with RisWN (s 0) 
  ... | n ,, R*s₀n , n∈NF = {!   !}


  iii-EMSN : WN R → WCR R → RP- R → dec (is_-SN_ R) → SN R 
  iii-EMSN RisWN RisWCR rp- decSN x with decSN x 
  ... | in1 x∈SN = x∈SN
  ... | in2 x∉SN with RisWN x
  ... | n ,, R*xn , n∈NF with preSNlemma1 decSN x∉SN n∈NF R*xn 
  ... | b₀ ,, (b₀∉SN , (m₀ ,, m₀∈SN , Rb₀m₀)) , (R*xb₀ , R*b₀n) with x∉SN→∃y∉SN b₀∉SN 
  ... | c₀ ,, c₀∉SN , Rb₀c₀ with RisWCR (b₀ ,, Rb₀m₀ , Rb₀c₀) 
  ... | d₀ ,, R*m₀d₀ , R*c₀d₀ with ReductionClosureProperties.SN↓⊆SN R m₀∈SN R*m₀d₀
  ... | d₀∈SN = {!   !} -- Need to capture the sequence we have formed, the fact it is infinite, the fact it is ω-bounded by n, the fact n is normal form common to all elements in the sequence. 

  iii-EM :  WN R → WCR R → RP- R → dec (is_-SN_ R) → isWFseq (~R R)
  iii-EM RisWN RisWCR rp- decSN s with decSN (s 0)
  ... | in1 RisSNs₀@(acc s₀acc) with Newmans-Lemma.WCR∧SN→UN R RisWCR (fst (RisWN (s zero)))
  ... | RisUNs₀ with ReductionClosureProperties.SN↓⊆SN R RisSNs₀ 
  ... | z with RisWN (s 0) 
  ... | n ,, R*s₀n , n∈NF = {!   !}
  iii-EM RisWN RisWCR rp decSN s | in2 s₀∉SN = {!   !}
  -- iii-EM RisWN RisWCR rp (in1 R∈SN) x = R∈SN x
  -- iii-EM RisWN RisWCR rp (in2 R∉SN) a with RisWN a
  -- ... | n ,, R*an , n∈NF with lemma-lastNonSN n∈NF R*an
  -- ... | b₀ ,, b∉SN , (R*ab₀ , R*b₀n) = {!   !}



  iv : CP R → CR R
  iv RhasCP (a ,, R*ab , R*ac) with RhasCP a
  ... | f ,, f-winc , (refl , fisCof) with fisCof _ R*ab | fisCof _ R*ac
  ... | bₙ ,, R*bfbₙ | cₙ ,, R*cfcₙ
    with wseq-lemma2 f f-winc bₙ cₙ
  ... | in1 R*fbₙfcₙ = (f cₙ) ,, ((R*bfbₙ ⋆!⋆ R*fbₙfcₙ) , R*cfcₙ)
  ... | in2 R*fcₙfbₙ = (f bₙ) ,, R*bfbₙ , (R*cfcₙ ⋆!⋆ R*fcₙfbₙ)

-- Useful dead-ends

  NFisωBnd : WCR R → ∀ (f : ℕ → A) → is R -increasing f → ∀ a → is R -NF a
               → (R ⋆) (f 0) a → ∀ n → (R ⋆) (f n) a
  NFisωBnd RisWCR f f-inc a a∈NF R*f0a zero = R*f0a
  NFisωBnd RisWCR f f-inc a a∈NF R*f0a (succ n)
    with NFisωBnd RisWCR f f-inc a a∈NF R*f0a n
  ... | ε⋆ = ∅ (a∈NF (f (succ n)) (f-inc n) )
  ... | Rfny ,⋆ R*ya = {!   !}

-- False; see the usual counterexample to WCR→CR
  iii-lemma1 : WCR R → ∀ a b → is R -NF b → (R ⋆) a b → ∀ c → (R ⋆) a c → (R ⋆) c b
  iii-lemma1 wcrR a .a b∈NF ε⋆ .a ε⋆ = ε⋆
  iii-lemma1 wcrR a .a b∈NF ε⋆ c (Ray ,⋆ R*yc) = ∅ (b∈NF _ Ray )
  iii-lemma1 wcrR a b b∈NF R*ab@(Ray ,⋆ R*yb) .a ε⋆ = R*ab
  iii-lemma1 wcrR a b b∈NF (Ray ,⋆ R*yb) c (_,⋆_ {y = z} Raz R*zc)
    with wcrR (a ,, Ray , Raz)
  ... | (d ,, R*yd , R*zd) = {!    !}


  iii-lemma2 : WCR R → ∀ a b → is R -NF b → (R ⋆) a b → ∀ c → R a c → (R ⋆) c b
  iii-lemma2 wcrR a .a b∈NF ε⋆ c Rac = ∅ (b∈NF c Rac)
  iii-lemma2 wcrR a b b∈NF (Ray ,⋆ R*yb) c Rac with wcrR (a ,, Ray , Rac)
  ... | (d ,, R*yd , R*cd) = {! iii-lemma2 wcrR _ b b∈NF R*yb    !}
  -- with iii-lemma2 wcrR y b b∈NF R*yb
  -- ... | z = {!   !}

  iii-lemma :  WN R → WCR R → ω-bounded R
  iii-lemma wnR wcrR f f-inc with wnR (f 0)
  ... | nf ,, R*f0n , n∈NF = nf ,, ρ where
          ρ : ∀ (n : ℕ) → (R ⋆) (f n) nf
          ρ zero = R*f0n
          ρ (succ n) = iii-lemma2 wcrR (f n) nf n∈NF (ρ n) (f (succ n)) (f-inc n ) -- note iii-lemma2 is not yet proven


 -- To be deleted?
 -- This seems very classical
  {- 2024.08.09
     Actually, it's false.
     Counter-example: ℕ∞
        AKA "the one-point compactification of ℕ"
        AKA "Natural numbers with infinity added"
     Define R : 𝓡 ℕ∞
            R x y = x < y
     Then R is well-founded, hence dominated by a a well-founded Q := R.
     Also, R is ω-bounded: Every element of every sequence reduces to a := ∞.
     But R is not SN, for it admits the infinite reduction 0 → 1 → 2 → ⋯
  ---
  ii : ∀ Q → dominatedByWF R Q → ω-bounded R → SN R -- isWFacc (~R R)
  ii Q domRQ bddR = {!   !}

  -- The same example shows the weaker version below to be unprovable
  -- (Which is not surprising, since it's classicaly equivalent to the one above.)
  ii-seq : ∀ Q → dominatedByWF R Q → ω-bounded R → isWFseq- (~R R) -- isWFacc (~R R)
  ii-seq Q (QisWFacc , R⊆Q) bddR f f-inc =
    let QisWFseq- : isWFseq- (~R Q)
        QisWFseq- = isWFmin-→isWFseq- (~R Q) (isWFacc-→isWFmin- (~R Q) (¬¬isWFacc→isWFacc- (~R Q) λ z → z {!   !} ) )
     in QisWFseq- f (λ n → R⊆Q (f n) (f (succ n)) (f-inc n) )
  -- ii-seq : ∀ Q → dominatedByWF R Q → ω-bounded R → isWFseq (~R R) -- isWFacc (~R R)
  -- ii-seq Q domRQ bddR f with bddR f {!   !}
  -- ... | c = {!   !}

  The problem with the above goals is the hypothesis "dominatedByWF R Q".
  It's not useful for proving strong normalization.
  Intead, we need something that is nearly dual to "ω-bounded".
  ω-continuous?
  -}
  -- ind + inc → no infinite sequence

  -- Comp : Set
  -- Comp = ∀ (f : ℕ → A) → is (R ⋆) -increasing f → ∀ a → (∀ n → (R ⋆) (f n) a)
  --           → Σ[ m ∈ ℕ ] ∀ k → f (add k m) ≡ f m

  ------------------------

  -- inf→⊥ : ∀ (f : ℕ → A)  → ω-bounded R → ∀ Q →  dominatedByWF R Q →  is R -increasing f → ⊥
  -- inf→⊥ f RisWb Q (isWFaccQ , R⊆Q) FisRinc =
  --                                 let
  --                                 a = f 0
  --                                 (b ,, fnb) = RisWb f FisRinc
  --                                   in {!   !}

  -- CR∧ω∧dom→SN : ∀ Q →  CR R → ω-bounded R → dominatedByWF R Q  → SN R
  -- CR∧ω∧dom→SN Q RisCR Riswb (isWFaccQ , R⊆Q) x = let
  --                                                 inf→⊥ : ∀ (f :  ℕ → A) → is R -increasing f → ⊥
  --                                                 inf→⊥ f fInc = let
  --                                                             (a ,, fna) = Riswb f fInc
  --                                                             yada : is Q -accessible fst (Riswb f fInc)
  --                                                             yada = isWFaccQ a
  --                                                             in {!  !}
  --                                                 in {!   !}

  -- CR∧ω→SN : CR R → ω-bounded R → SN R
  -- CR∧ω→SN RisCR Riswb x = {!   !}
  --------------------------------------------------------
-- The end
 