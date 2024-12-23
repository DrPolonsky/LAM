open import Logic
open import Datatypes
open import Predicates
open import Classical
open import Relations.Core
open import Relations.Wellfounded

module Relations.WFCounters where

-- data Next : ℕ → ℕ → Set where
--   next : ∀ n → Next n (succ n)
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
