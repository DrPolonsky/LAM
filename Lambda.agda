module Lambda where

open import Logic
open import Lifting

-- Lambda terms as a type constructor
-- For a set X, Λ X = terms whose free variables come from the set X
-- Λ is \GL
data Λ (V : Set) : Set where
  var : V → Λ V
  app : Λ V → Λ V → Λ V
  abs : Λ (↑ V) → Λ V

-- Terms over a finite set of variables, Λₙ n = Λ {x1, ..., xn}
-- ₙ is \_n
Λₙ : ℕ → Set
Λₙ n = Λ (Fin n)

-- The set of closed terms, whose set of free variables is empty
-- ₀ is \_0
Λ₀ : Set
Λ₀ = Λₙ zero -- Λ ⊥

-- Functorial action on morphisms
Λ→ : ∀ {A B : Set} (f : A → B) → Λ A → Λ B
Λ→ f (var x)   = var (f x)
Λ→ f (app s t) = app (Λ→ f s) (Λ→ f t)
Λ→ f (abs r)   = abs (Λ→ (↑→ f) r)

-- A very common special case
Λ→i : ∀ {A : Set} → Λ A → Λ (↑ A)
Λ→i = Λ→ i

-- Preservation of identity
Λ→≅I : ∀ {A} {f : A → A} → f ≅ I → Λ→ f ≅ I
Λ→≅I f≅I (var x)   = cong  var (f≅I x)
Λ→≅I f≅I (app s t) = cong2 app (Λ→≅I f≅I s) (Λ→≅I f≅I t)
Λ→≅I f≅I (abs r)   = cong  abs (Λ→≅I (↑→≅I f≅I) r)

-- Preservation of pointwise equality
Λ→≅ : ∀ {A B : Set} {f g : A → B} → f ≅ g → Λ→ f ≅ Λ→ g
Λ→≅ fg (var x)   = cong  var (fg x)
Λ→≅ fg (app s t) = cong2 app (Λ→≅ fg s) (Λ→≅ fg t)
Λ→≅ fg (abs r)   = cong  abs (Λ→≅ (↑→≅ fg) r)

-- Preservation of composition
Λ→∘ : ∀ {A B C} (f : A → B) (g : B → C) → Λ→ (g ∘ f) ≅ Λ→ g ∘ Λ→ f
Λ→∘ f g (var x)   = refl
Λ→∘ f g (app s t) = cong2 app (Λ→∘ f g s) (Λ→∘ f g t)
Λ→∘ f g (abs r)   = cong  abs (Λ→≅ (↑→∘ f g) r ! Λ→∘ (↑→ f) (↑→ g) r)

-- Preservation of composition modulo pointwise equality
-- (This lemma looks more complicated, but its proof is simpler than the above)
Λ→≅∘ : ∀ {A B C} (f : A → B) (g : B → C) {h} → h ≅ g ∘ f → Λ→ h ≅ Λ→ g ∘ Λ→ f
Λ→≅∘ f g h≅g∘f (var x)   = cong  var (h≅g∘f x)
Λ→≅∘ f g h≅g∘f (app s t) = cong2 app (Λ→≅∘ f g h≅g∘f s) (Λ→≅∘ f g h≅g∘f t)
Λ→≅∘ f g h≅g∘f (abs r)   = cong  abs (Λ→≅∘ (↑→ f) (↑→ g) (↑→≅∘ f g h≅g∘f) r )

-- Lifting a function over the type of terms
lift : ∀ {A B : Set} → (A → Λ B) → ↑ A → Λ (↑ B)
lift f = io (Λ→i ∘ f) (var o)

-- Substitution is the monadic bind for Λ (Haskell's >>=)
_[_] : ∀ {A B : Set} → Λ A → (A → Λ B) → Λ B
var x   [ f ] = f x
app s t [ f ] = app (s [ f ]) (t [ f ])
abs r   [ f ] = abs (r [ lift f ])

-- A special case of the above for finitely many variables
_[_]ₙ : ∀ {m n : ℕ} → Λₙ m → (Fin m → Λₙ n) → Λₙ n
_[_]ₙ = _[_]




-- The End
