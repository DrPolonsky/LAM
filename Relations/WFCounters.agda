open import Logic
open import Datatypes
open import Predicates
open import Classical
open import Relations.Core
open import Relations.Wellfounded

module Relations.WFCounters where

data _<_ : ℕ → ℕ → Set where
  base< : ∀ {n} → n < succ n
  succ< : ∀ {n m} → n < m → n < succ m

mono< : ∀ {m n} → m < n → succ m < succ n
mono< base< = base<
mono< (succ< mn) = succ< (mono< mn)

zero< : ∀ {m} → zero < succ m
zero< {zero} = base<
zero< {succ m} = succ< zero<

module LTnotWFmin (P : 𝓟 ℕ) where

  data Psat (n : ℕ) : 𝓟 ℕ where
    Psat0 : ∀ k → P (add k n) → Psat n k
    PsatS : ∀ k → Psat n (succ k)

  lemma1 : ∀ n k → (is_-_-minimal_ _<_ (Psat n)) k → k < 2
  lemma1 n zero kmin = succ< base<
  lemma1 n (succ zero) kmin = base<
  lemma1 n (succ (succ k)) (_ , H) = ∅ (H (succ zero) (PsatS zero) (mono< zero< ))

  lemma2 : ∀ n k → (is_-_-minimal_ _<_ (Psat n)) k → EM (P n)
  lemma2 n k kmin with lemma1 n k kmin
  lemma2 n .1 (Ps1 , ¬Ps0) | base< = in2 (λ pn → ¬Ps0 zero (Psat0 zero pn ) base< )
  lemma2 n .0 (Psat0 .0 p , _) | succ< base< = in1 p

  lemma3 : isWFmin _<_ → dec P
  lemma3 wfmin n with wfmin (Psat n) (PsatS zero)
  ... | (k ,, kmin) = lemma2 n k kmin

  lemma4 : isWFmin₀ _<_ → ¬¬Closed P → dec P
  lemma4 wfmin₀ ¬¬CP n with wfmin₀ (Psat n) nnCPs (PsatS zero)
    where nnCPs : ¬¬Closed (Psat n)
          nnCPs  zero nnp0 = Psat0 0 (¬¬CP n λ pn → nnp0 λ {(Psat0 .0 p) → pn p})
          nnCPs (succ k) _ = PsatS k
  ... | (k ,, kmin) = lemma2 n k kmin

module isWFminImpliesDec {A : Set} (R : 𝓡 A) (wfMin : isWFmin R) (P : 𝓟 A) where

  open ClassicalImplications

  data cP (a₀ : A) : 𝓟 A where
    cPmin : P a₀ → ∀ {x} → (∀ y → ¬ R y x) → cP a₀ x
    cPsuc : ∀ {x y} → R y x → cP a₀ x

  cPlemma : ∀ {b c} → R b c → decMin R → dec P
  cPlemma Rbc dmR a with wfMin (cP a) (cPsuc Rbc)
  ... | m ,, cPmin pa _ , mIsMin = in1 pa
  ... | m ,, cPsuc {.m} {y} Rym , mIsMin with dmR y
  ... | in1 (z ,, Rzy) = ∅ (mIsMin y (cPsuc Rzy) Rym )
  ... | in2 yMin = in2 (λ pa → mIsMin y (cPmin pa yMin) Rym )



















-- the end
