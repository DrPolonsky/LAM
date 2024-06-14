-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --allow-unsolved-metas #-}

module Relations where

open import Logic
open import Predicates
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- Identity, Converse, and Composition
≡R : ∀ {A} → Rel A A
≡R = _≡_

~R : ∀ {A B} → Rel A B → Rel B A
~R R = λ x y → R y x

_∘R_ : ∀ {A B C} → Rel A B → Rel B C → Rel A C
_∘R_ {B = B} R S = λ x z → Σ[ y ∈ B ] (R x y × S y z)

_R∘_ : ∀ {A B C} → Rel B C → Rel A B → Rel A C
S R∘ R = R ∘R S

Graph : ∀ {A B} → (A → B) → Rel A B
Graph f = λ a b → f a ≡ b

-- isTotal : ∀ {A B} → Rel A B → Set
-- isTotal {A} {B} R = ∀ x → Σ[ y ∈ B ] R x y
--
-- total→Fun : ∀ {A B} (R : Rel A B) → isTotal R → (A → B)
-- total→Fun R totR x with totR x
-- ... | t1 ,, t2 = t1
--
-- data Graph {A B : Set} (f : A → B) : Rel A B where
--   gra : ∀ x → Graph f x (f x)

module LogicOps₂ {A B : Set} where

  -- The empty relation ∅ ⊆ 𝓟 A×B.
  K⊥₂ : Rel A B
  K⊥₂ _ _ = ⊥

  -- The maximal relation A×B ⊆ 𝓟 A×B.
  K⊤₂ : Rel A B
  K⊤₂ _ _ = ⊤

  _∩₂_ : Rel A B → Rel A B → Rel A B
  R ∩₂ S = λ x y → R x y  ×  S x y
  infix 17 _∩₂_

  _∪₂_ : Rel A B → Rel A B → Rel A B
  R ∪₂ S = λ x y →  R x y  ⊔  S x y
  infix 17 _∪₂_

  ∁₂_ : Rel A B → Rel A B
  ∁₂ R = λ x y → ¬ R x y
  infix 19 ∁₂_

  -- Inclusion of relations.
  _⊆₂_ : Rel A B → Rel A B → Set
  R ⊆₂ S = ∀ x y → R x y → S x y
  infix 16 _⊆₂_

  -- Extensional equivalence of relations.
  _⇔₂_ : Rel A B → Rel A B → Set
  R ⇔₂ S = R ⊆₂ S × S ⊆₂ R
  infix 15 _⇔₂_

  relEq : ∀ {R S : Rel A B} →   R ⇔₂ S   ↔   ∀ x y → R x y ↔ S x y
  relEq = (λ RS x y → pr1 RS x y , pr2 RS x y )
        , λ H → (λ x y → pr1 (H x y)) , (λ x y → pr2 (H x y))

open LogicOps₂ public


check : ∀ {A : Set} (R Q : Rel A A) → (_⇔_ R Q) ↔ (R ⇔₂ Q)
check R Q = (λ x → x ) , (λ x → x )

law1 : ∀ {A B : Set} (R : Rel A B) → ≡R ∘R R ⇔₂ R
law2 : ∀ {A B : Set} (R : Rel A B) → R ∘R ≡R ⇔₂ R
law3 : ∀ {A : Set} → ~R (≡R {A}) ⇔ ≡R
law4 : ∀ {A B C : Set} (R : Rel A B) (S : Rel B C) → ~R (R ∘R S) ⇔₂ (~R S) ∘R (~R R)

pr1 (law1 R) x y (.x ,, refl , Rxy) = Rxy
pr2 (law1 R) x y Rxy = x ,, (refl , Rxy)

pr1 (law2 R) x y (.y ,, Rxy , refl) = Rxy
pr2 (law2 R) x y Rxy = y ,, Rxy , refl

pr1 law3 x .x refl = refl
pr2 law3 x .x refl = refl

pr1 (law4 R S) x y (z ,, Ryx , Szx) = z ,, Szx , Ryx
pr2 (law4 R S) x y (z ,, Szx , Ryz) = z ,, Ryz , Szx

module ClosureOperators {U : Set} where
  --reflexive closure
  data _⁼ (R : 𝓡 U) : 𝓡 U where
    ax⁼ : ∀ {x y : U} → R x y → (R ⁼) x y
    ε⁼  : ∀ {x} → (R ⁼) x x

  -- Transitive closure
  data _⁺ (R : 𝓡 U) : 𝓡 U   where
    ax⁺  : ∀ {x y : U}   → R x y → (R ⁺) x y
    _,⁺_ : ∀ {x y z : U} → R x y → (R ⁺) y z → (R ⁺) x z

  -- symmetric closure
  data _ˢ (R : 𝓡 U) : 𝓡 U where
    axˢ+ : ∀ {x y} → R x y → (R ˢ) x y
    axˢ- : ∀ {x y} → R y x → (R ˢ) x y

  -- reflexive transitive closure
  -- ⋆ is \*
  data _⋆ (R : 𝓡 U) : 𝓡 U where
    ax⋆ : ∀ {x y : U} → R x y → (R ⋆) x y
    ε⋆  :  ∀ {x} → (R ⋆) x x
    _,⋆_ : ∀ {x y z} → R x y → (R ⋆) y z → (R ⋆) x z

  infix 19 _⁼
  infix 19 _ˢ
  infix 19 _⁺
  infix 19 _⋆

  TCisTran : ∀ (R : 𝓡 U) {x y z : U} → (R ⋆) x y → (R ⋆) y z → (R ⋆) x z
  TCisTran R (ax⋆ x) R*yz = x ,⋆ R*yz
  TCisTran R ε⋆ R*yz = R*yz
  TCisTran R (x ,⋆ R*xy) R*yz = x ,⋆ (TCisTran R R*xy R*yz)

  TCisSym : ∀ (R : 𝓡 U) {x y : U} → ((R ˢ) ⋆) x y → ((R ˢ) ⋆) y x
  TCisSym R (ax⋆ (axˢ+ x)) = ax⋆ ((axˢ- x))
  TCisSym R (ax⋆ (axˢ- x)) = ax⋆ ((axˢ+ x))
  TCisSym R ε⋆ = ε⋆
  TCisSym R (axˢ+ x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym R rxy) (axˢ- x ,⋆ ε⋆ )
  TCisSym R (axˢ- x ,⋆ rxy) = TCisTran (R ˢ) (TCisSym R rxy) (axˢ+ x ,⋆ ε⋆ )

  EQ : 𝓡 U → 𝓡 U
  EQ R = (R ˢ) ⋆

open ClosureOperators public

-- Properties of relations
module RelationProperties {U : Set} (R : 𝓡 U) where
  reflR   : Set
  irreflR : Set
  symmR   : Set
  asymmR  : Set
  tranR   : Set
  reflR   = ∀ x → R x x
  irreflR = ∀ x → ¬ R x x
  symmR   = ∀ x y → R x y → R y x
  asymmR  = ∀ x y → R x y → R y x → x ≡ y
  tranR   = ∀ x y z → R x y → R y z → R x z

  record isEquivalence : Set where
    field
      isRefl : reflR
      isSymm : symmR
      isTran : tranR

  record isPartialOrder : Set where
    field
      isRefl : reflR
      isAsym : asymmR
      isTran : tranR

  record isStrictOrder : Set where
    field
      isIrrefl : irreflR
      isTran   : tranR

  record isPreorder : Set where
    field
      isRefl : reflR
      isTran : tranR

open RelationProperties public

acyclic : ∀ {U} (R : 𝓡 U) → Set
acyclic R = irreflR (R ⁺)

  -- data WF {A : Set} (R : Rel A) : A → Set where -- written to provide strongly normal
  --   isNF : ∀ {x : A} → normal x R → WF R x -- is normal form
  --   indF : ∀ {x : A} → (∀ y → R x y → WF R y) → WF R x


is_-inductive_ : ∀ {A : Set} → 𝓡 A → 𝓟 A → Set
is R -inductive φ = ∀ x → (∀ y → R y x → φ y) → φ x

isWF : ∀ {A} → 𝓡 A → Set₁
isWF {A} R = ∀ (φ : 𝓟 A) → is R -inductive φ → ∀ x → φ x

isInhabited : Set → Set
isInhabited A = A

¬WF⁼ : ∀ {A : Set} (R : 𝓡 A) → isInhabited A → ¬ (isWF (R ⁼))
¬WF⁼ {A} R a WFR⁼ = WFR⁼ K⊥ isR=indK⊥ (WFR⁼ (K A) (λ x _ → x) a) where
                            isR=indK⊥ : is (R ⁼) -inductive K⊥
                            isR=indK⊥ x h = h x ε⁼

lemmaReverseTransitivity : ∀ {A} {R : 𝓡 A} {x y z : A} → (R ⁺) x y → R y z → (R ⁺) x z
lemmaReverseTransitivity (ax⁺ Rxy) Ryz = Rxy ,⁺ ax⁺ Ryz
lemmaReverseTransitivity (Rxy₁ ,⁺ R⁺y₁z) Ryz = Rxy₁ ,⁺ lemmaReverseTransitivity R⁺y₁z Ryz

WF⁺+ : ∀ {A} (R : 𝓡 A) → isWF R → isWF (R ⁺)
WF⁺+ {A} R iswfR φ φisR⁺ind x = {!   !} -- Try to directly use iswfR,
  -- by providing it with a proof that φ is R -inductive.
-- WF⁺+ {A} R iswfR φ φisR⁺ind x = φisR⁺ind x g where
--   g : (y : A) → (R ⁺) y x → φ y
--   g y (ax⁺ Ryx) = φisR⁺ind y λ z R⁺zy → g z {!   !} -- φisR⁺ind y (λ z R⁺zy → g z (lemmaReverseTransitivity R⁺zy Ryx))
--   g y (Ryy₁ ,⁺ R⁺y₁x) = {!   !} -- WF⁺+ R iswfR {!   !} {!   !} {!   !}


-- WF⁺+ R iswfR φ φisR⁺ind x = iswfR φ (λ y h → φisR⁺ind y λ {z (ax⁺ Rzy) → h z Rzy
--                                                          ; z (Rzy₁ ,⁺ R⁺y₁y) → h z {!   !}}) x

WF⁺- : ∀ {A} (R : 𝓡 A) → isWF (R ⁺) → isWF R
WF⁺- R isWFR⁺ φ φisRind x = isWFR⁺ φ (λ y h → φisRind y λ z Rzy → h z (ax⁺ Rzy)) x

lemma⁺→⋆ :  ∀ {A : Set} {x y : A} (R : 𝓡 A) → (R ⁺) x y →  (R ⋆) x y
lemma⁺→⋆ R (ax⁺ Rxy) = ax⋆ Rxy
lemma⁺→⋆ R (Rxy₁ ,⁺ R⁺yy₁) = Rxy₁ ,⋆ lemma⁺→⋆ R R⁺yy₁


TransitiveClosure : ∀ {A : Set} (R : 𝓡 A) → R ⋆ ⇔ (R ⁺ ∪ R ⁼)
TransitiveClosure R = TC+ , TC- where
  TC+ : (R ⋆) ⊆ (R ⁺) ∪ (R ⁼)
  TC+ a b (ax⋆ Rab) = in1 (ax⁺ Rab )
  TC+ a .a ε⋆ = in2 ε⁼
  TC+ a b (Ray ,⋆ R⋆yb) = in1 (case (_,⁺_ Ray) -- (λ R⁺yb → (Ray ,⁺ R⁺yb))
                                    (λ { (ax⁼ Ryb) → (Ray ,⁺ (ax⁺ Ryb)) ; ε⁼ → ax⁺ Ray})
                                    (TC+ _ _ R⋆yb))
  TC- : (R ⁺) ∪ (R ⁼) ⊆ (R ⋆)
  TC- x y (in1 (ax⁺ Rxy)) = ax⋆ Rxy
  TC- x y (in1 (Rxy₁ ,⁺ R⁺y₁y)) = Rxy₁ ,⋆ lemma⁺→⋆ R R⁺y₁y
  TC- x y (in2 (ax⁼ Rxy)) = ax⋆ Rxy
  TC- x .x (in2 ε⁼) = ε⋆

open import Agda.Builtin.Sigma renaming (_,_ to _,,_)
open import Lifting using (ℕ; zero; succ)

is_-decreasing_ : ∀ {A : Set} → 𝓡 A → 𝓟 (ℕ → A)
is R -decreasing s = ∀ n → ~R R (s n) (s (succ n)) -- xₙ > xₙ₊₁

isWFseq : ∀ {A} → 𝓡 A → Set
isWFseq {A} R = ∀ (s : ℕ → A) → ¬ (is R -decreasing s)

WFisWFseq+ : ∀ {A} (R : 𝓡 A) → isWF R → isWFseq R
WFisWFseq+ {A} R RisWF s sIsR-Dec =
  let φ : 𝓟 A
      φ a = ∀ n → ¬ a ≡ s n -- a ∉ Im [ s ]
      φ-ind : is R -inductive φ
      φ-ind x IH m x≡sm = IH (s (succ m))
            (transp (R (s (succ m))) (~ x≡sm) (sIsR-Dec m)) (succ m) refl
   in RisWF φ φ-ind (s zero) zero refl


--  Proving that isWFseq → isWF
DeMorgan∀∃ : Set → Set₁
DeMorgan∀∃ A = ∀ (P : 𝓟 A) → ¬ (∀ x → P x) → Σ[ x ∈ A ] (¬ P x)

-- Question: Does DeMorgan∀∃ A imply that every predicate on A is decidable?
-- Question: Do we need it to be this general?

DeMorgan∀∃rel : ∀ {A} (B : 𝓟 A) → 𝓟 A → Set
DeMorgan∀∃rel {A} B P = ¬ (B ⊆ P) → Σ[ x ∈ A ] (B x × ¬ P x)

DM∀∃ : ∀ {A} (R : 𝓡 A) → Set₁
DM∀∃ {A} R = ∀ x → ∀ (φ : 𝓟 A) → DeMorgan∀∃rel (~R R x) φ

¬¬∃→¬∀¬ : ∀ {A} (P : 𝓟 A) → ¬¬ (Σ[ x ∈ A ] P x) → ¬ (∀ x → ¬ P x)
¬¬∃→¬∀¬ P h x→¬Px = h λ { (y ,, yP) → x→¬Px y yP }

¬∀¬→¬¬∃ : ∀ {A} (P : 𝓟 A) → ¬ (∀ x → ¬ P x) → ¬¬ (Σ[ x ∈ A ] P x)
¬∀¬→¬¬∃ P ¬∀¬ ¬∃ = ¬∀¬ λ x Px → ¬∃ (x ,, Px)

MP : ∀ {A} (P : 𝓟 A) → Set
MP {A} P = (∀ x → P x ⊔ ¬ P x) → ¬ (∀ x → ¬ P x) → Σ[ x ∈ A ] P x

MPrel : ∀ {A} (B P : 𝓟 A) → Set
MPrel {A} B P = (∀ x → B x → P x ⊔ ¬ P x) → ¬ (∀ x → B x → ¬ P x) → Σ[ x ∈ A ] (B x × P x)

-- Not provable unless an assumption is added, find the assumption!
open import Classical

MPrel→DMrel : ∀ {A} (B P : 𝓟 A) → MPrel B P → EM A →  DeMorgan∀∃rel B P
MPrel→DMrel {A} B P MPBP EM ¬B⊆P = {!   !}
-- MPrel→DMrel B P MPBP WEM ¬B⊆P with MPBP (λ x Bx → in2 λ Px → ¬B⊆P (λ x₁ x₂ → {!   !})) {!   !}
-- ... | y ,, By , Py = y ,, By , λ Py → ¬B⊆P λ x Bx → {!   !}


-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
DeMorgan∀∃→DeMorgan∀∃rel : {A : Set} → (B P : 𝓟 A) → DeMorgan∀∃ A → DeMorgan∀∃rel B P
DeMorgan∀∃→DeMorgan∀∃rel {A} B P DeMorg ¬B⊆P with DeMorg {!   !} (λ x→Px → ¬B⊆P (λ x x∈B → x→Px x))
... | x ,, ¬Px = x ,, ( {!   !} , ¬Px) -- (∅ (¬B⊆P {!   !}) , ¬Px)

¬ind→step : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ
             → (∀ x → DeMorgan∀∃rel (~R R x) φ)
             → ∀ x → ¬ φ x → Σ[ y ∈ A ] (~R R x y × ¬ φ y)
¬ind→step R φ φ-ind DeMorg x ¬φx = DeMorg x (λ ↓x⊆φ → ¬φx (φ-ind x ↓x⊆φ ) )

¬ind→seq1 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → ¬ φ x
              → ℕ → A
¬ind→seq2 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → (∀ n → ¬ φ (¬ind→seq1 {A} R φ φ-ind DeMorg x ¬φx n))
¬ind→seq3 : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) (φ-ind : is R -inductive φ) (DeMorg : ∀ x → DeMorgan∀∃rel (~R R x) φ) x (¬φx : ¬ φ x)
              → is R -decreasing (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)

¬ind→seq1 R φ φ-ind DeMorg x ¬φx zero = x
¬ind→seq1 R φ φ-ind DeMorg x ¬φx (succ n) = fst (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n))

¬ind→seq2 R φ φ-ind DeMorg x ¬φx  zero = ¬φx
¬ind→seq2 R φ φ-ind DeMorg x ¬φx (succ n) = pr2 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

-- Not mutually recursive with seq1 and seq2
¬ind→seq3 R φ φ-ind DeMorg x ¬φx n = pr1 (snd (¬ind→step R φ φ-ind DeMorg (¬ind→seq1 R φ φ-ind DeMorg x ¬φx n) (¬ind→seq2 R φ φ-ind DeMorg x ¬φx n)))

¬¬Closed : ∀ {A} → 𝓟 A → Set
¬¬Closed P = ∀ x → ¬¬ P x → P x

-- ¬ind→seq = ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → is R -inductive φ → (∀ x → DeMorgan∀∃rel (~R R x) φ) →

WFisWFseq- : ∀ {A} (R : 𝓡 A) (φ : 𝓟 A) → isWFseq R → is R -inductive φ → (¬¬Closed φ)
                → (∀ x → DeMorgan∀∃rel (~R R x) φ) → ∀ x → φ x
WFisWFseq- R φ RisWFseq φ-ind DNEφ DeMorg x = DNEφ x
  (λ ¬φx → RisWFseq (¬ind→seq1 R φ φ-ind DeMorg x ¬φx)
                    (¬ind→seq3 R φ φ-ind DeMorg x ¬φx) )

-- Question: Does DeMorgan∀∃ → DeMorgan∀∃rel (or vice versa?)
-- Question: Does either of them imply ¬¬Closed φ (possibly using φ is R-inductive)
-- NOT PROVABLE!
DeMorgan∀∃rel→¬¬Closed : ∀ {A} → (B P : 𝓟 A) → DeMorgan∀∃rel B P → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed B P DeMorgRel x ¬¬Bx with DeMorgRel (λ B⊆P →  ¬¬Bx λ Bx → {!   !})
... | y ,, By , ¬Py = {!   !}

DeMorgan∀∃rel→¬¬Closed2 : ∀ {A} → (B : 𝓟 A) → (H : ∀ (P : 𝓟 A) → DeMorgan∀∃rel B P) → ¬¬Closed B
DeMorgan∀∃rel→¬¬Closed2 = {!   !}

¬¬Lemma : ∀ X → ¬¬ (¬¬ X → X)
¬¬Lemma X = λ ¬¬X→X → ¬¬X→X (λ ¬¬X → ∅ (¬¬X λ x → ¬¬X→X (K x)))

DeMorg→¬¬Closed : ∀ {A} {B : 𝓟 A} → DeMorgan∀∃ A → ¬ (¬¬Closed B) → ⊥
DeMorg→¬¬Closed {A}{B} DeMorg ¬nnC with DeMorg (λ x → ¬¬ (B x) → B x) ¬nnC
... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg (λ x → ¬¬ (B x) → B x) (λ H → ¬¬Bx (λ Bx → {!   !} ))
-- ... | y ,, yP = ∅ (¬¬Lemma (B y) yP)

-- DeMorg→¬¬Closed {A}{B} DeMorg x ¬¬Bx with DeMorg B (λ x→Bx → ¬¬Bx (λ Bx → {!   !}))

-- Question: If φ is decidable, does the implication WF→WFseq follow automatically.

-- is_-minimal_ : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S
-- -- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
-- is R -minimal {S} x = ∀ y → R y x → ⊥

-- weaklyBounded : ∀ {S : Set} (R : 𝓡 S) → 𝓟 S → Set
-- weaklyBounded R A = Σ[ a ∈ A ] → is R -minimal a

is_-_-minimal_ : ∀ {S : Set} (R : 𝓡 S) (A : 𝓟 S) → 𝓟 S
-- is R - A -minimal {S} R A x = x ∈ A × ¬ Σ[ y ∈ S ] (y ∈ A × R y x)
is R - A -minimal x = x ∈ A × (∀ y → y ∈ A → R y x → ⊥)

module A18Constructive where

  lemmaA18φ : ∀ (S : Set) → 𝓡 S → 𝓟 S → 𝓟 S
  lemmaA18φ S R A x = (x ∈ A) → Σ[ y ∈ S ] (is R - A -minimal y)

  -- lemmaA18φ S R A x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)

  A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
           → ¬¬ Σ[ y ∈ S ] is R - A -minimal y
  A18→ {S} R WFR A x x∈A ¬miny =
    let φ    = λ y → y ∈ A → ∀ z → z ∈ A → ¬¬ R z y
        WFRφ : is R -inductive φ
        WFRφ y H y∈A z z∈A ¬Rzy = ¬miny (y ,, y∈A , λ y1 y1∈A Ry1y → H y1 Ry1y y1∈A z z∈A (λ Rzy1 → H y1 Ry1y y1∈A z z∈A {!   !} ) )
     in  WFR φ WFRφ x x∈A x x∈A (WFR (λ z → (x : R z z) → ⊥) (λ x z x₁ → z x x₁ x₁) x)

-- ↓R-dec : ∀ (S : Set) (R : 𝓡 S) → 𝓟 S
-- ↓R-dec S R x = ¬ (∀ y → ¬ R y x) → Σ[ y ∈ S ] R y x

-- lemmaA18 : ∀ S R A → (∀ a → ↓R-dec S R a) → is R -inductive (lemmaA18φ S R A) -- (λ _ → Σ S (is R - A -minimal_)) -- this is quite messy. don't really understand what I have
-- lemmaA18 S R A ↓Rdec x H x∈A with ↓Rdec x {!   !}
-- ... | y ,, Ryx = {!   !}
-- lemmaA18 {S} R {A} x H with H x {!   !}
-- ... | y ,, Ay , H2 = y ,, Ay , H2

-- A.1.8
-- A18→ : ∀ {S : Set} (R : 𝓡 S) → isWF R → ∀ (A : 𝓟 S) (x : S) → x ∈ A
--          → Σ[ y ∈ S ] is R - A -minimal y
-- A18→ {S} R WFR A x x∈A =
--   let WFRφ = WFR (lemmaA18φ S R A) (lemmaA18 S R A ?) x
--    in WFRφ x∈A -- pr2 WFRφ
-- A18→ {S} R WFR A a a∈A = pr2 (WFR φ {!   !} a ) where
--               φ : S → Set
--               φ x = (x ∈ A) × Σ[ y ∈ S ] (is R - A -minimal y)


-- A18→ {S} R WFR A a a∈A = WFR φ (lemmaA18 R) a where   -- (λ _ → Σ S (is_-_-minimal_ R A))
--                         φ : (x : S) → Set
--                         φ = λ _ → Σ S (is R - A -minimal_ )
  -- Hint. Use WFR with φ x := x ∈ A → Σ[ y ∈ A ] (is R - A -minimal y)
  -- Try to prove this φ is R-inductive.
  -- Otherwise, try φ x := x ∈ A × Σ[ y ∈ A ] (is R - A -minimal y)
-- A18→ R WFR x y Ryx = WFR (λ x₁ → ⊥) (λ x₁ h → h y {!   !}) x

-- For the converse, try to prove "Every non-empty A contains a R-minimal element" → "isWFseq R"

-- The End
