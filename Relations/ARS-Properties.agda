module Relations.ARS-Properties {A : Set} where

open import Relations.Relations
open import Predicates
open import Logic
open import Relations.ARS-Base
open import Datatypes using (ℕ; zero)


{- Local and global properties for ARS -}

module LocalProperties {R : 𝓡 A} where

    WCR : 𝓟 A
    WCR x = ∀ {b c} → R x b → R x c → b ↘ R ⋆ ↙ c

    CR : 𝓟 A
    CR x = ∀ {b c} → (R ⋆) x b → (R ⋆) x c → b ↘ R ⋆ ↙ c

    NF : 𝓟 A
    NF x = ∀ {y} → ¬ R x y

    WN : 𝓟 A
    WN x = Σ[ n ∈ A ] ((R ⋆) x n × NF n)

    SN : 𝓟 A
    SN x = is (~R R) -accessible x

    -- Minimal form: Recurrent or Normal form
    MF : 𝓟 A
    MF x = ∀ y → (R ⋆) x y → (R ⋆) y x

    -- Weak normal form property
    WNFP : 𝓟 A
    WNFP x = ∀ {y z} → NF y → (R ⋆) x y → (R ⋆) x z → (R ⋆) z y

    -- Unique normal form property
    UN : 𝓟 A
    UN x = ∀ {y} {z} → NF y → NF z → (R ⋆) x y → (R ⋆) x z → y ≡ z

    -- Weakly minimal form
    WM : 𝓟 A
    WM x = Σ[ r ∈ A ] ((R ⋆) x r × MF r)

    -- Strongly minimal form
    data SM : 𝓟 A where
      SMrec : ∀ x → MF x → SM x
      SMacc : ∀ x → (∀ y → R x y → SM y) → SM x

    -- Weakly minimal form property
    WMFP : 𝓟 A
    WMFP x = ∀ {y z} → MF y → (R ⋆) x y → (R ⋆) x z → (R ⋆) z y

module GlobalProperties (R : 𝓡 A) where

    open LocalProperties {R}

    _isCR : Set
    _isCR = ∀ x → CR x

    _isWCR : Set
    _isWCR = ∀ x → WCR x

    _isWN : Set
    _isWN = ∀ x → WN x

    _isSN : Set
    _isSN = ∀ x → SN x

    _isSM : Set
    _isSM = ∀ x → SM x

    _isWNFP : Set 
    _isWNFP = ∀ x → WNFP x

    _isNP : Set
    _isNP = ∀ {x y} → NF y → (R ⁼) x y → (R ⋆) x y

    -- [AP.  What's the problem with getting this from local UN?]
    _isUN : Set
    _isUN = ∀ {x y : A} → x ∈ NF → y ∈ NF → (R ⁼) x y → x ≡ y
    -- NB. This is stronger than global UN, which is UN→ below

    _isUN→ : Set
    _isUN→ = ∀ x → UN x

    is_-_bound_ : (f : ℕ → A) → A → Set
    is_-_bound_ f x = ∀ n → (R ⋆) (f n) x

    _isBP : Set
    _isBP = ∀ (f : ℕ → A) → is R -increasing f → Σ[ x ∈ A ] ( is_-_bound_ f x )

    _isBP+ : Set
    _isBP+ = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → Σ[ a ∈ A ] (is_-_bound_ f a )

    _isRP : Set
    _isRP = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (is_-_bound_ f a)
         → Σ[ m ∈ ℕ ] MF (f m)

    _isRP- : Set 
    _isRP- = ∀ (f : ℕ → A) → is R -increasing f → ∀ a → (is_-_bound_ f a)
          → Σ[ i ∈ ℕ ] ((R ⋆) a (f i))

    -- AKA Convergent
    _isComplete : Set
    _isComplete = _isCR × _isSN

    _isSemicomplete : Set
    _isSemicomplete = _isUN × _isWN

    _isDominatedByWF : 𝓡 A → Set
    _isDominatedByWF Q = isWFacc Q × (R ⊆ Q)

    is_-cofinal_ : 𝓟 A → Set
    is_-cofinal_ B = ∀ (x : A) → Σ[ y ∈ A ] ((R ⋆) x y × y ∈ B)

    -- Cofinality Property
    _isCP : Set
    _isCP = ∀ (a : A) → Σ[ s ∈ (ℕ → A) ] ((is (R ʳ) -increasing s) ×
                   (s zero ≡ a × (∀ b → (R ⋆) a b → Σ[ n ∈ ℕ ] ((R ⋆) b (s n))) ))

open GlobalProperties public

module MiscProperties (R : 𝓡 A) where 
  -- These properties are variations on the above properties 
  open LocalProperties {R}
  SMseq : 𝓟 A   
  SMseq x = ∀ (f : ℕ → A) → f zero ≡ x → is R -increasing f → Σ[ i ∈ ℕ ] (MF (f i))

  SRv2 : 𝓟 A 
  SRv2 x = ∀ (f : ℕ → A) → is (R ʳ) -increasing f → Σ[ i ∈ ℕ ] (MF (f i))

  
