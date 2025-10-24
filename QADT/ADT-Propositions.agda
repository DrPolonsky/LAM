module QADT.ADT-Propositions where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import Environment
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Functor

module X=nPX+X {V : Set} (a : ADT (↑ V)) (ρ₀ : SetEnv V) where

  f : ADT (↑ V)
  f = a ⊔ 𝕧₀

  g : ℕ → ADT (↑ V)
  g k = (Num k × a) ⊔ 𝕧₀

  F : ADT V
  F = μ f
  G : ℕ → ADT V
  G k = μ (g k)

  _≃!≃_ = _iso∘_

  FisG : ∀ (X : Set) (k : ℕ) → (⟦ f ⟧ (ρ₀ ⅋o:= X)) ≃ X → ((⟦ g k ⟧ (ρ₀ ⅋o:= X)) ≃ X)
  FisG X zero fX=X = iso∨ (comm∧ ≃!≃ annih∧ ) (id≃ X ) ≃!≃ iso~ id∨
  FisG X (succ k) fX=X =
    let reccall = FisG X k fX=X
     in ((iso∨ isodistrR (id≃ _) iso∘ iso∨ (iso∨ (iso~ id∧) (id≃ _) ) (id≃ _)  ) iso∘ (iso~ assoc∨  ≃!≃ (iso∨ (id≃ _ ) comm∨ ≃!≃ (assoc∨ ≃!≃ (iso∨ fX=X (id≃ _) ≃!≃ comm∨ ) )) ) ) ≃!≃ reccall

lemma1 : (n : ℕ) → (X Y : Set) → (Γ : SetEnv X) → (Ρ : SetEnv Y) → ⟦ Num n ⟧ Γ ≃ ⟦ Num n ⟧ Ρ
lemma1 zero X Y Γ Ρ = refl2iso refl
lemma1 (succ n) X Y Γ Ρ = iso f+ f- f-+ f+- where
  f+ : ⊤ ∨ (⟦ Num n ⟧ Γ) → ⊤ ∨ (⟦ Num n ⟧ Ρ)
  f+ (in1 x) = in1 x
  f+ (in2 x) = in2 (_≃_.f+ (lemma1 n X Y Γ Ρ) x)
  f- : ⊤ ∨ (⟦ Num n ⟧ Ρ) → ⊤ ∨ (⟦ Num n ⟧ Γ)
  f- (in1 x) = in1 x
  f- (in2 x) = in2 (_≃_.f- (lemma1 n X Y Γ Ρ) x )
  f-+ : (x : ⊤ ∨ (⟦ Num n ⟧ Γ)) → f- (f+ x) ≡ x
  f-+ (in1 x) = refl
  f-+ (in2 x) = cong in2 (_≃_.f-+ (lemma1 n X Y Γ Ρ) x)
  f+- : (y : ⊤ ∨ (⟦ Num n ⟧ Ρ)) → f+ (f- y) ≡ y
  f+- (in1 x) = refl
  f+- (in2 x) = cong in2 (_≃_.f+- (lemma1 n X Y Γ Ρ) x)

murule1 : ∀ (n m : ℕ) → (Y : ADT ⊥) → ⟦ (μ ((Num n) ⊔ (Num m) × 𝕧₀) × Y) ⟧ Γ₀ ≃ ⟦ μ ((Num n) × wk₀ Y ⊔ (Num m) × 𝕧₀) ⟧ Γ₀
murule1 n m Y = iso f+ f- {! f-+  !} {!   !} where
  f+ : LFP
      (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)
      ∧ (⟦ Y ⟧ Γ₀) →
       LFP
      (λ X →
         (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨
         (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)
  f+ (lfp (in1 terminal) , y) = lfp (in1
      (_≃_.f-
        (lemma1 n (↑ ⊥) (↑ ⊥) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)))) terminal ,
      _≃_.f-
        (weakLemma≃ Y (LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)) Γ₀) y ))
  f+ (lfp (in2 (elem , list)) , y) = lfp (in2
      (_≃_.f-
        (lemma1 m (↑ ⊥) (↑ ⊥) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)))) elem ,
      f+ (list , y )))
  f- : LFP
      (λ X →
         (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨
         (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X) →
      LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X) ∧
      (⟦ Y ⟧ Γ₀)
  f- (lfp (in1 (terminal , y))) =
    lfp (in1 (_≃_.f+ (lemma1 n (↑ ⊥) (↑ ⊥) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)))) terminal) ) ,
    (_≃_.f+ (weakLemma≃ Y (LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)) Γ₀) y)
  f- (lfp (in2 (elem , list))) with f- list
  ... | r , y = lfp (in2 (_≃_.f+ (lemma1 m (↑ ⊥) (↑ ⊥) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ wk₀ Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) ((Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)))) elem , r ) ) , y
  f-+ : (x
       : LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)
         ∧ (⟦ Y ⟧ Γ₀)) →
      f- (f+ x) ≡ x
  f-+ (lfp (in1 terminal) , y) rewrite _≃_.f+- (lemma1 n (↑ ⊥) (↑ ⊥) (Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ ADT→ i Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X)) (Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) terminal
                               rewrite _≃_.f+- (mapLemma≃ Y i (Γ₀ ⅋o:= LFP (λ X → (⟦ Num n ⟧ (Γ₀ ⅋o:= X)) ∧ (⟦ ADT→ i Y ⟧ (Γ₀ ⅋o:= X)) ∨ (⟦ Num m ⟧ (Γ₀ ⅋o:= X)) ∧ X))) y = refl
  f-+ (lfp (in2 (elem , list)) , y) = {!   !}

murule1' : ∀ (X Y Z : ADT ⊥) → Iso (μ (wk₀ X ⊔ 𝕧₀ × wk₀ Z) × Y) (μ (wk₀ Y × wk₀ X ⊔ 𝕧₀ × wk₀ Z))
murule1' X Y Z = (=× (fix≃ (wk₀ X ⊔ 𝕍 o × wk₀ Z) =!= {!   !} ) ) =!= {!   !}
