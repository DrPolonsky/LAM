module RelationsPractice where

open import Logic
open import Predicates

Rel : Set → Set → Set₁
Rel A B = A → B → Set

-- Identity, Converse, and Composition
≡R : ∀ {A} → Rel A A
≡R = _≡_

~R : ∀ {A B} → Rel A B → Rel B A
~R R = λ x y → R y x

_∘R_ : ∀ {A B C} → Rel A B → Rel B C → Rel A C
_∘R_ {B = B} R S = λ x z → Σ[ y ∈ B ] (R x y × S y z )

_R∘_ : ∀ {A B C} → Rel B C → Rel A B → Rel A C
S R∘ R = R ∘R S

-- ~≡is≡ : ∀ {A} → ~

-- Logical operators on relations.
module LogicOps₂ {A B : Set} where

  -- The empty relation ∅ ⊆ 𝒫 A×B.
  K⊥₂ : Rel A B
  K⊥₂ _ _ = ⊥

  -- The maximal relation A×B ⊆ 𝒫 A×B.
  K⊤₂ : Rel A B
  K⊤₂ _ _ = ⊤

  _∩₂_ : Rel A B → Rel A B → Rel A B
  R ∩₂ S = λ x y → R x y × S x y
  infix 17 _∩₂_

  _∪₂_ : Rel A B → Rel A B → Rel A B
  R ∪₂ S = λ x y → R x y ⊔ S x y
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
  relEq = (λ RS x y → pr1 RS x y , pr2 RS x y) 
      , λ H → (λ x y → pr1 (H x y)) , (λ x y → pr2 (H x y))

  -- (λ RS x y → pr1 RS x y , pr2 RS x y )
open LogicOps₂ public

ℛ : Set → Set₁
ℛ A = Rel A A

-- Properties of relations

module RelationProperties {U : Set} (R : ℛ U) where
  reflR   : Set
  irreflR : Set
  symmR   : Set
  asymmR  : Set
  tranR   : Set
  reflR   = ∀ x → R x x
  irreflR = ∀ x → ¬ R x x
  symmR   = ∀ x y → R x y → R y x
  asymmR  = ∀ x y →  R x y → R y x → x ≡ y
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

  -- data WF {A : Set} (R : Rel A) : A → Set where -- written to provide strongly normal
  --   isNF : ∀ {x : A} → normal x R → WF R x -- is normal form
  --   indF : ∀ {x : A} → (∀ y → R x y → WF R y) → WF R x


is_-inductive_ : ∀ {A : Set} → ℛ A → 𝒫 A → Set 
is R -inductive φ = ∀ x → (∀ y → R y x → φ y) → φ x

isWF : ∀ {A} → ℛ A → Set₁
isWF {A} R = ∀ (φ : 𝒫 A) → is R -inductive φ → ∀ x → φ x 


open import Agda.Builtin.Sigma renaming (_,_ to _,,_)
open import Lifting using (ℕ; zero; succ)

is_-decreasing_ : ∀ {A : Set} → ℛ A → 𝒫 (ℕ → A)
is R -decreasing s = ∀ n → ~R R (s n) (s (succ n)) -- xₙ > xₙ₊₁

isWFseq : ∀ {A} → ℛ A → Set
isWFseq {A} R = ∀ (s : ℕ → A) → ¬ (is R -decreasing s)

DeMorgan∀∃ : Set → Set₁
DeMorgan∀∃ A = ∀ (P : 𝒫 A) → ¬ (∀ x → P x) → Σ[ x ∈ A ] (¬ P x)

¬ind→step : ∀ {A} (R : ℛ A) (φ : 𝒫 A) → is R -inductive φ → DeMorgan∀∃ A
             → ∀ x → ¬ φ x → Σ[ y ∈ A ] (¬ φ y × R y x)
¬ind→step R φ φ-ind DeMorg x ¬φx with DeMorg (λ y → φ y × R y x) {!   !} --  (λ ∀φ → ¬φx (∀φ x))
... | y ,, p = {!   !}

¬ind→seq : ∀ {A} (R : ℛ A) (φ : 𝒫 A) → is R -inductive φ → DeMorgan∀∃ A → ∀ x → ¬ φ x → ℕ → A
¬ind→seq R φ φ-ind DeMorg x ¬φx zero = x
¬ind→seq R φ φ-ind DeMorg x ¬φx (succ n) with ¬ind→step R φ φ-ind DeMorg x ¬φx
... | y ,, p = y

¬ind→seqWF : ∀ {A} (R : ℛ A) (φ : 𝒫 A) (φ-ind : is R -inductive φ) (DeMorg : DeMorgan∀∃ A)
             → ∀ x (¬φx : ¬ φ x) → is R -decreasing (¬ind→seq R φ φ-ind DeMorg x ¬φx)
¬ind→seqWF R φ φ-ind DeMorg x ¬φx zero = {!   !}
¬ind→seqWF R φ φ-ind DeMorg x ¬φx (succ n) = {!   !}

¬ind→seqΣ : ∀ {A} (R : ℛ A) (φ : 𝒫 A) → is R -inductive φ → DeMorgan∀∃ A → ∀ x → ¬ φ x
              → Σ[ s ∈ (ℕ → A) ] (is R -decreasing s)
¬ind→seqΣ {A} R φ φ-ind DeMorg x ¬φx = (s ,, s<) where
  s : ℕ → A
  s< : is R -decreasing s
  s zero = x
  s (succ n) = Σ.fst (¬ind→step R φ φ-ind DeMorg (s n) λ φsn → {!   !} )
  s< n = {!   !}


WFisWFseq+ : ∀ {A} (R : ℛ A) → isWF R → isWFseq R
WFisWFseq+ {A} R RisWF s sIsR-Dec =
  let φ : 𝒫 A
      φ a = ∀ n → ¬ a ≡ s n -- a ∉ Im [ s ]
      φ-ind : is R -inductive φ
      φ-ind x IH m x≡sm = IH (s (succ m))
            (transp (R (s (succ m))) (~ x≡sm) (sIsR-Dec m)) (succ m) refl
   in RisWF φ φ-ind (s zero) zero refl

¬¬Closed : ∀ {A} → 𝒫 A → Set
¬¬Closed P = ∀ x → ¬¬ P x → P x

WFisWFseq- : ∀ {A} (R : ℛ A) → isWFseq R →
                 ∀ (φ : 𝒫 A) → is R -inductive φ → ¬¬Closed φ → ∀ x → φ x
WFisWFseq- R RisWFseq φ φIsR-Ind DNEφ x = DNEφ x (λ ¬φx → {!   !} )











-- The End
