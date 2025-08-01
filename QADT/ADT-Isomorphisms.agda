module QADT.ADT-Isomorphisms where

open import QADT.ADTs
open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
-- open import QADT.BasicDatatypes
open import QADT.Functions
open import QADT.Isomorphisms
open import Environment
open import QADT.EnvIsomorphisms
open import QADT.Functor

-- A syntax of proof terms for isomorphisms between ADTs
data Iso {V} : ADT V → ADT V → Set where
  -- Equivalence relation
  refl≃ : ∀ e → Iso e e
  symm≃ : ∀ {a b} → Iso a b → Iso b a
  tran≃ : ∀ {a b c} → Iso a b → Iso b c → Iso a c
  -- Congruence rules
  ∧≃ : ∀ {A1 A2 B1 B2 : ADT V} → Iso A1 A2 → Iso B1 B2 → Iso (A1 × B1) (A2 × B2)
  ∨≃ : ∀ {A1 A2 B1 B2 : ADT V} → Iso A1 A2 → Iso B1 B2 → Iso (A1 ⊔ B1) (A2 ⊔ B2)
  μ≃ : ∀ {A B : ADT (↑ V)} → Iso A B → Iso (μ A) (μ B)
  -- Semiring axioms
  assoc×≃ : ∀ a b c → Iso (a × (b × c)) ((a × b) × c)
  assoc⊔≃ : ∀ a b c → Iso (a ⊔ (b ⊔ c)) ((a ⊔ b) ⊔ c)
  comm⊔≃ : ∀ a b → Iso (a ⊔ b) (b ⊔ a)
  comm×≃ : ∀ a b → Iso (a × b) (b × a)
  id⊔≃ : ∀ a → Iso a (𝟎 ⊔ a)
  id×≃ : ∀ a → Iso a (𝟏 × a)
  distrL≃ : ∀ {A B C} → Iso (A × (B ⊔ C)) ((A × B) ⊔ (A × C))
  distrR≃ : ∀ {A B C} → Iso ((A ⊔ B) × C) ((A × C) ⊔ (B × C))
  annih×≃ : ∀ a → Iso (a × 𝟎) 𝟎
  -- Mu reduction rules
  fix≃ : ∀ (e : ADT (↑ V)) → Iso (μ e) (subst e (μ e))
  subst≃ : ∀ {e1 e2 : ADT (↑ V)} {d1 d2 : ADT V} → Iso e1 e2 → Iso d1 d2 → Iso (subst e1 d1) (subst e2 d2)

  -- subst : ∀ {V} (e : ADT (↑ V)) → (e' : ADT V) → ADT V
  -- subst e e' = subst-level e e' (o)
substIso : ∀ {V} → (e : ADT (↑ V)) → {a b : ADT V} → Iso a b → Iso (subst e a) (subst e b)
substIso e j = subst≃ (refl≃ e ) j

-- Groupoid operations
!! : ∀ {V} {a : ADT V}   → Iso a a
!! = refl≃ _
~~ : ∀ {V} {a b : ADT V} → Iso a b → Iso b a
~~ = symm≃
_=!=_ : ∀ {V} {a b c : ADT V} → Iso a b → Iso b c → Iso a c
ab =!= bc = tran≃ ab bc
_~!~_ : ∀ {V} {a b c : ADT V} → Iso b a → Iso c b → Iso a c
ba ~!~ cb = (~~ ba) =!= (~~ cb)
_~!=_ : ∀ {V} {a b c : ADT V} → Iso b a → Iso b c → Iso a c
ba ~!= bc = ~~ ba =!= bc
-- _~!=_ = _=!=_ ∘ ~~
_=!~_ : ∀ {V} {a b c : ADT V} → Iso a b → Iso c b → Iso a c
ab =!~ cb = ab =!= (~~ cb)
-- _=!~_ = _~!~_ ∘ ~~

--- Congruence laws
cong+ :  ∀ {V} {a b c d : ADT V} → Iso a b → Iso c d → Iso (a ⊔ c) (b ⊔ d)
cong+ ab cd = ∨≃ ab cd
cong× :  ∀ {V} {a b c d : ADT V} → Iso a b → Iso c d → Iso (a × c) (b × d)
cong× ab cd = ∧≃ ab cd

cong+= :  ∀ {V} {a b c d e : ADT V} → Iso a b → Iso c d → Iso (b ⊔ d) e → Iso (a ⊔ c) e
cong+= ab cd bde = cong+ ab cd =!= bde
cong×= :  ∀ {V} {a b c d e : ADT V} → Iso a b → Iso c d → Iso (b × d) e → Iso (a × c) e
cong×= ab cd bde = cong× ab cd =!= bde

!+ :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
!+ j = cong+ !! j
+! :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
+! j = cong+ j !!
!× :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (a × b) (a × c)
!× j = cong× !! j
×! :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (b × a) (c × a)
×! j = cong× j !!

!+= :  ∀ {V} {a b c d : ADT V} → Iso b c → Iso (a ⊔ c) d → Iso (a ⊔ b) d
!+= bc acd = !+ bc =!= acd
+!= :  ∀ {V} {a b c d : ADT V} → Iso b c → Iso (c ⊔ a) d → Iso (b ⊔ a) d
+!= bc cad = +! bc =!= cad
×!= :  ∀ {V} {a b c d : ADT V} → Iso b c → Iso (a × c) d → Iso (a × b) d
×!= bc acd = !× bc =!= acd
!×= :  ∀ {V} {a b c d : ADT V} → Iso b c → Iso (c × a) d → Iso (b × a) d
!×= bc cad = ×! bc =!= cad

-- Semiring Axioms
-- Associativity, commutativity, and identity
a× : ∀ {V} {a b c : ADT V} → Iso ((a × b) × c) (a × (b × c))
a× {V} {a} {b} {c} = ~~ (assoc×≃ a b c)
a+ : ∀ {V} {a b c : ADT V} → Iso ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))
a+ {V} {a} {b} {c} = ~~ (assoc⊔≃ a b c)
c× : ∀ {V} {a b : ADT V} → Iso (a × b) (b × a)
c× {V} {a} {b} = comm×≃ a b
c+ : ∀ {V} {a b : ADT V} → Iso (a ⊔ b) (b ⊔ a)
c+ {V} {a} {b} = comm⊔≃ a b
i+l : ∀ {V} {a : ADT V} → Iso (𝟎 ⊔ a) a
i+l = ~~ (id⊔≃ _)
i+r : ∀ {V} {a : ADT V} → Iso (a ⊔ 𝟎) a
i+r = c+ =!~ id⊔≃ _
i×l : ∀ {V} {a : ADT V} → Iso (𝟏 × a) a
i×l {V} {a} = ~~ (id×≃ a)
i×r : ∀ {V} {a : ADT V} → Iso (a × 𝟏) a
i×r {V} {a} = c× =!~ id×≃ a
-- distributivity and annihilation
dl : ∀ {V} {a b c : ADT V} → Iso (a × (b ⊔ c)) (a × b ⊔ a × c)
dl {V} {a} {b} {c} = distrL≃
dr : ∀ {V} {a b c : ADT V} → Iso((a ⊔ b) × c)  (a × c ⊔ b × c)
dr {V} {a} {b} {c} = distrR≃
ar : ∀ {V} {a : ADT V} → Iso (a × 𝟎) 𝟎
ar {V} {a} = annih×≃ a
al : ∀ {V} {a : ADT V} → Iso (𝟎 × a) 𝟎
al {V} {a} = c× =!= (annih×≃ a)

a×= : ∀ {V} {a b c d : ADT V} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
a×= {V} {a} {b} {c} {d} j = assoc×≃ a b c ~!= j
a+= : ∀ {V} {a b c d : ADT V} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
a+= {V} {a} {b} {c} {d} j = assoc⊔≃ a b c ~!= j
c×= : ∀ {V} {a b c : ADT V} → Iso (b × a) c → Iso (a × b) c
c×= {V} {a} {b} {c} j = comm×≃ b a ~!= j
c+= : ∀ {V} {a b c : ADT V} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
c+= {V} {a} {b} {c} j = comm⊔≃ b a ~!= j
i+l= : ∀ {V} {a b : ADT V} → Iso a b → Iso (𝟎 ⊔ a) b
i+l= {V} {a} {b} j = i+l =!= j
i+r= : ∀ {V} {a b : ADT V} → Iso a b → Iso (a ⊔ 𝟎) b
i+r= {V} {a} {b} j = i+r =!= j
i×l= : ∀ {V} {a b : ADT V} → Iso a b → Iso (𝟏 × a) b
i×l= {V} {a} {b} j = i×l =!= j
i×r= : ∀ {V} {a b : ADT V} → Iso a b → Iso (a × 𝟏) b
i×r= {V} {a} {b} j = i×r =!= j

dl= : ∀ {V} {a b c d : ADT V} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
dl= {V} {a} {b} {c} {d} j = distrL≃ =!= j
dr= : ∀ {V} {a b c d : ADT V} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
dr= {V} {a} {b} {c} {d} j = distrR≃ =!= j
ar= : ∀ {V} {a b : ADT V} → Iso 𝟎 b → Iso (a × 𝟎) b
ar= {V} {a} {b} j = annih×≃ a =!= j
al= : ∀ {V} {a b : ADT V} → Iso 𝟎 b → Iso (𝟎 × a) b
al= {V} {a} {b} j = c×= (annih×≃ a =!= j)

-- END RULES LIST

r= : ∀ {V} {e : ADT V} → Iso e e
r= {V} {e} = refl≃ e
s= : ∀ {V} {a b : ADT V} → Iso a b → Iso b a
s= {V} {a} {b} j = symm≃ j
t= : ∀ {V} {a b c : ADT V} → Iso a b → Iso b c → Iso a c
t= = tran≃
_t~_ : ∀ {V} {a b c : ADT V} → Iso a b → Iso c b → Iso a c
_t~_ {V} {a} {b} {c} i1 i2 = t= i1 (s= i2)
_~t_ : ∀ {V} {a b c : ADT V} → Iso b a → Iso b c → Iso a c
_~t_ {V} {a} {b} {c} i1 i2 = t= (s= i1) i2

+= :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
+= = !+
=+ :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
=+ = +!
×= :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (a × b) (a × c)
×= = !×
=× :  ∀ {V} {a b c : ADT V} → Iso b c → Iso (b × a) (c × a)
=× = ×!

-- a×= : ∀ {V} {a b c d : ADT V} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
-- a+= : ∀ {V} {a b c d : ADT V} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
-- c+= : ∀ {V} {a b c : ADT V} → Iso (b × a) c → Iso (a × b) c
-- c×= : ∀ {V} {a b c : ADT V} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
-- 0L= : ∀ {V} {a b : ADT V} → Iso a b → Iso (𝟎 ⊔ a) b
-- 0R= : ∀ {V} {a b : ADT V} → Iso a b → Iso (a ⊔ 𝟎) b
-- 1×L= : ∀ {V} {a b : ADT V} → Iso a b → Iso (𝟏 × a) b
-- 1×R= : ∀ {V} {a b : ADT V} → Iso a b → Iso (a × 𝟏) b
-- dL= : ∀ {V} {a b c d : ADT V} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
-- dR= : ∀ {V} {a b c d : ADT V} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
-- dR= {V} {a} {b} {c} {d} j = tran≃ (symm≃ distrR≃ ) j
-- ah : ∀ {V} {a b : ADT V} → Iso 𝟎 b → Iso (a × 𝟎) b
-- ah {V} {a} {b} j = (annih×≃ a) ~t j


-- Helpful lemmas
+1× : ∀ {V} {A B : ADT V} (c : ℕ)  → Iso ((Num c × A) ⊔ A) B → Iso (Num (succ c) × A) B
+1× {V} {A} {B} c toB = tran≃ e1 toB where
  e1 = tran≃ distrR≃ (tran≃ (comm⊔≃ _ _ ) (∨≃ (refl≃ _) (symm≃ (id×≃ _ ) ) ) )

cycle+ : ∀ {V} {A B C : ADT V} → Iso (A ⊔ B ⊔ C) (B ⊔ C ⊔ A)
cycle+ = c+= (a+= !! )

cycle×3 : ∀ {V} {A B C : ADT V} → Iso (A × B × C) (B × C × A)
cycle×3 = c×= a×

dist3 : ∀ {V} {A B C D : ADT V} → Iso (A × (B ⊔ C ⊔ D)) (A × B ⊔ A × C ⊔ A × D)
dist3 = dl= (!+ dl)

foil : ∀ {V} {A B : ADT V} → Iso ((A ⊔ B) ²) (A ² ⊔ (Num 2 × A × B) ⊔ B ²)
foil {V} {A} {B} = dl= (cong+= dr dr (a+= (+= (a+ ~!= =+ (=+ c× =!= (=+ (~~ i×l) =!~ (+1× 1 (=+ (=× i+r))) ) ) ) ) ))

X+X=2X : ∀ {V} (X : ADT V) → Iso (X ⊔ X) (Num 2 × X)
X+X=2X A = ~~ (dr= (cong+ i×l (dr= (+! i×l =!= (!+ al =!= i+r) ) ) ) )

μ+ : ∀ {V} (e : ADT (↑ V)) → Iso (μ e) (subst e (μ e))
μ+ = fix≃

μ- : ∀ {V} (e : ADT (↑ V)) → Iso (subst e (μ e)) (μ e)
μ- e = ~~ (fix≃ e)

-- μiso : ∀ {V} (e : ADT (↑ V)) → Iso (μ e) (subst e (μ e))
μiso : ∀ {V} (e : ADT (↑ V)) (ρ : SetEnv V) → ⟦ μ e ⟧ ρ ≃ ⟦ subst e (μ e) ⟧ ρ
μiso {V} e ρ with iso~ (Lambek (λ x → ⟦ e ⟧ (ρ ⅋o:= x)  )) | substlemma e (io 𝕍 (μ e)) ρ
... | li | sl = li iso∘ iso~ (sl iso∘ (⟦ e ⟧≃ f ) ) where
  f = io𝓟 _ (λ x → refl2iso refl ) (refl2iso refl )

≃⟦_⟧ : ∀ {V} {A B : ADT V} → Iso A B → ( ρ : SetEnv V) → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ
≃⟦_⟧≃ : ∀ {V} {A B : ADT V} → Iso A B → {ρ ρ' : SetEnv V} → SetEnv≃ ρ ρ' → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ'

≃⟦ refl≃ e ⟧ ρ = ⟦ e ⟧≃ reflSetEnv≃ ρ
≃⟦ symm≃ e ⟧ ρ with ≃⟦ e ⟧ ρ
... | r = iso~ r
≃⟦ tran≃ e1 e2 ⟧ ρ with ≃⟦ e1 ⟧ ρ | ≃⟦ e2 ⟧ ρ
... | r | r2 = r iso∘ r2
≃⟦ ∧≃ e e₁ ⟧ ρ = iso∧ (≃⟦ e ⟧ ρ ) (≃⟦ e₁ ⟧ ρ)
≃⟦ ∨≃ e e₁ ⟧ ρ = iso∨ (≃⟦ e ⟧ ρ) (≃⟦ e₁ ⟧ ρ)
≃⟦ μ≃ {e1} {e2} e12 ⟧ ρ = LFP≃ (λ X → ⟦ e1 ⟧ (ρ ⅋o:= X)) ((λ X → ⟦ e2 ⟧ (ρ ⅋o:= X)))
                          λ X Y XY → ≃⟦ e12 ⟧≃ (coskipSetEnv≃Set≃ XY (reflSetEnv≃ ρ ) )
-- ≃⟦ ×≃ A x ⟧ ρ = iso∧ (⟦ refl≃ A ⟧iso ρ ) (≃⟦ x ⟧ ρ)
-- ≃⟦ ⊔≃ A x ⟧ ρ = iso∨ (⟦ refl≃ A ⟧iso ρ) (≃⟦ x ⟧ ρ)
≃⟦ distrL≃ ⟧ ρ = isodistrL
≃⟦ distrR≃ ⟧ ρ = isodistrR
≃⟦ fix≃ e ⟧ ρ = μiso e ρ
-- ≃⟦_⟧ {V} (subst≃ {e1} {e2} {d1} {d2} j1 j2) ρ with substlemma e1 (io 𝕍 d1) ρ | substlemma e2 (io 𝕍 d2) ρ
-- ... | sl1 | sl2 = sl1 iso∘ iso~ (sl2 iso∘ iso~ (≃⟦ j1 ⟧≃ (coskipSet≃ ρ (≃⟦ j2 ⟧ ρ)) ) )
≃⟦_⟧ {V} (subst≃ {e1} {e2} {d1} {d2} j1 j2) ρ
  with substlemma e1 (io 𝕍 d1) ρ | substlemma e2 (io 𝕍 d2) ρ
... | sl1 | sl2 = sl1 iso∘ (≃⟦ j1 ⟧≃ (io𝓟 _ (λ x → refl2iso refl) (≃⟦ j2 ⟧ ρ) ) iso∘ iso~ sl2 )
≃⟦ assoc×≃ a b c ⟧ ρ = assoc∧
≃⟦ assoc⊔≃ a b c ⟧ ρ = assoc∨
≃⟦ comm⊔≃ a b ⟧ ρ = comm∨
≃⟦ comm×≃ a b ⟧ ρ = comm∧
≃⟦ id⊔≃ _ ⟧ ρ = id∨
≃⟦ id×≃ _ ⟧ ρ = id∧
≃⟦ annih×≃ a ⟧ ρ = annih∧

≃⟦_⟧≃ {A = A} {B = B} e {ρ} {ρ'} ρρ' = ≃⟦ e ⟧ ρ iso∘ (⟦ B ⟧≃ ρρ')

RigFold : ∀ (A : ADT (↑ ⊥)) → (B : ADT ⊥) → Iso (subst A B) B → ⟦ μ A ⟧ Γ₀ → ⟦ B ⟧ Γ₀
RigFold A B rigiso with substlemma A (io 𝕍 B) Γ₀
... | sl = foldADT {⊥} A Γ₀ (⟦ B ⟧ Γ₀) (_≃_.f+ (iso~ (sl iso∘ (⟦ A ⟧≃ io𝓟 _ (λ x → refl2iso refl) (refl2iso refl) ) ) iso∘ (≃⟦ rigiso ⟧ Γ₀) ) )

module IsoLemmas where
  c×³ : ∀ {V} {X : ADT V} → List (Iso (X ³) (X ³))
  c×³ {X = X} = !! ∷ cycle×3 ∷ (cycle×3 =!= cycle×3) ∷ ×= c× ∷ (cycle×3 =!= ×= c× ) ∷ (cycle×3 =!= (cycle×3 =!= ×= c× ) ) ∷ []


open IsoLemmas public
