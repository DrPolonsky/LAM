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
data Iso {n} : ADT n → ADT n → Set where
  -- Equivalence relation
  refl≃ : ∀ e → Iso e e
  symm≃ : ∀ {a b} → Iso a b → Iso b a
  tran≃ : ∀ {a b c} → Iso a b → Iso b c → Iso a c
  -- Congruence rules
  ∧≃ : ∀ {A1 A2 B1 B2 : ADT n} → Iso A1 A2 → Iso B1 B2 → Iso (A1 × B1) (A2 × B2)
  ∨≃ : ∀ {A1 A2 B1 B2 : ADT n} → Iso A1 A2 → Iso B1 B2 → Iso (A1 ⊔ B1) (A2 ⊔ B2)
  μ≃ : ∀ {A B : ADT (succ n)} → Iso A B → Iso (μ A) (μ B)
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
  fix≃ : ∀ (e : ADT (succ n)) → Iso (μ e) (e [ (μ e) ])
  subst≃ : ∀ {e1 e2 : ADT (succ n)} {d1 d2 : ADT n} → Iso e1 e2 → Iso d1 d2 → Iso (e1 [ d1 ]) (e2 [ d2 ])

-- Groupoid operations
!! : ∀ {n} {a : ADT n}   → Iso a a
!! = refl≃ _
~~ : ∀ {n} {a b : ADT n} → Iso a b → Iso b a
~~ = symm≃
_=!=_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso b c → Iso a c
ab =!= bc = tran≃ ab bc
_~!~_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso c b → Iso a c
ba ~!~ cb = (~~ ba) =!= (~~ cb)
_~!=_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso b c → Iso a c
ba ~!= bc = ~~ ba =!= bc
-- _~!=_ = _=!=_ ∘ ~~
_=!~_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso c b → Iso a c
ab =!~ cb = ab =!= (~~ cb)
-- _=!~_ = _~!~_ ∘ ~~

--- Congruence laws
cong+ :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a ⊔ c) (b ⊔ d)
cong+ ab cd = ∨≃ ab cd
cong× :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a × c) (b × d)
cong× ab cd = ∧≃ ab cd

cong+= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b ⊔ d) e → Iso (a ⊔ c) e
cong+= ab cd bde = cong+ ab cd =!= bde
cong×= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b × d) e → Iso (a × c) e
cong×= ab cd bde = cong× ab cd =!= bde

!+ :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
!+ j = cong+ !! j
+! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
+! j = cong+ j !!
!× :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a × b) (a × c)
!× j = cong× !! j
×! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b × a) (c × a)
×! j = cong× j !!

!+= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a ⊔ c) d → Iso (a ⊔ b) d
!+= bc acd = !+ bc =!= acd
+!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c ⊔ a) d → Iso (b ⊔ a) d
+!= bc cad = +! bc =!= cad
×!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a × c) d → Iso (a × b) d
×!= bc acd = !× bc =!= acd
!×= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c × a) d → Iso (b × a) d
!×= bc cad = ×! bc =!= cad

-- Semiring Axioms
-- Associativity, commutativity, and identity
a× : ∀ {n} {a b c : ADT n} → Iso ((a × b) × c) (a × (b × c))
a× {n} {a} {b} {c} = ~~ (assoc×≃ a b c)
a+ : ∀ {n} {a b c : ADT n} → Iso ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))
a+ {n} {a} {b} {c} = ~~ (assoc⊔≃ a b c)
c× : ∀ {n} {a b : ADT n} → Iso (a × b) (b × a)
c× {n} {a} {b} = comm×≃ a b
c+ : ∀ {n} {a b : ADT n} → Iso (a ⊔ b) (b ⊔ a)
c+ {n} {a} {b} = comm⊔≃ a b
i+l : ∀ {n} {a : ADT n} → Iso (𝟎 ⊔ a) a
i+l = ~~ (id⊔≃ _)
i+r : ∀ {n} {a : ADT n} → Iso (a ⊔ 𝟎) a
i+r = c+ =!~ id⊔≃ _
i×l : ∀ {n} {a : ADT n} → Iso (𝟏 × a) a
i×l {n} {a} = ~~ (id×≃ a)
i×r : ∀ {n} {a : ADT n} → Iso (a × 𝟏) a
i×r {n} {a} = c× =!~ id×≃ a
-- distributivity and annihilation
dl : ∀ {n} {a b c : ADT n} → Iso (a × (b ⊔ c)) (a × b ⊔ a × c)
dl {n} {a} {b} {c} = distrL≃
dr : ∀ {n} {a b c : ADT n} → Iso((a ⊔ b) × c)  (a × c ⊔ b × c)
dr {n} {a} {b} {c} = distrR≃
ar : ∀ {n} {a : ADT n} → Iso (a × 𝟎) 𝟎
ar {n} {a} = annih×≃ a
al : ∀ {n} {a : ADT n} → Iso (𝟎 × a) 𝟎
al {n} {a} = c× =!= (annih×≃ a)

a×= : ∀ {n} {a b c d : ADT n} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
a×= {n} {a} {b} {c} {d} j = assoc×≃ a b c ~!= j
a+= : ∀ {n} {a b c d : ADT n} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
a+= {n} {a} {b} {c} {d} j = assoc⊔≃ a b c ~!= j
c×= : ∀ {n} {a b c : ADT n} → Iso (b × a) c → Iso (a × b) c
c×= {n} {a} {b} {c} j = comm×≃ b a ~!= j
c+= : ∀ {n} {a b c : ADT n} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
c+= {n} {a} {b} {c} j = comm⊔≃ b a ~!= j
i+l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟎 ⊔ a) b
i+l= {n} {a} {b} j = i+l =!= j
i+r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a ⊔ 𝟎) b
i+r= {n} {a} {b} j = i+r =!= j
i×l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟏 × a) b
i×l= {n} {a} {b} j = i×l =!= j
i×r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a × 𝟏) b
i×r= {n} {a} {b} j = i×r =!= j

dl= : ∀ {n} {a b c d : ADT n} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
dl= {n} {a} {b} {c} {d} j = distrL≃ =!= j
dr= : ∀ {n} {a b c d : ADT n} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
dr= {n} {a} {b} {c} {d} j = distrR≃ =!= j
ar= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (a × 𝟎) b
ar= {n} {a} {b} j = annih×≃ a =!= j
al= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (𝟎 × a) b
al= {n} {a} {b} j = c×= (annih×≃ a =!= j)

-- END RULES LIST

r= : ∀ {n} {e : ADT n} → Iso e e
r= {n} {e} = refl≃ e
s= : ∀ {n} {a b : ADT n} → Iso a b → Iso b a
s= {n} {a} {b} j = symm≃ j
t= : ∀ {n} {a b c : ADT n} → Iso a b → Iso b c → Iso a c
t= = tran≃
_t~_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso c b → Iso a c
_t~_ {n} {a} {b} {c} i1 i2 = t= i1 (s= i2)
_~t_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso b c → Iso a c
_~t_ {n} {a} {b} {c} i1 i2 = t= (s= i1) i2

+= :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
+= = !+
=+ :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
=+ = +!
×= :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a × b) (a × c)
×= = !×
=× :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b × a) (c × a)
=× = ×!

-- a×= : ∀ {n} {a b c d : ADT n} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
-- a+= : ∀ {n} {a b c d : ADT n} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
-- c+= : ∀ {n} {a b c : ADT n} → Iso (b × a) c → Iso (a × b) c
-- c×= : ∀ {n} {a b c : ADT n} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
-- 0L= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟎 ⊔ a) b
-- 0R= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a ⊔ 𝟎) b
-- 1×L= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟏 × a) b
-- 1×R= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a × 𝟏) b
-- dL= : ∀ {n} {a b c d : ADT n} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
-- dR= : ∀ {n} {a b c d : ADT n} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
-- dR= {n} {a} {b} {c} {d} j = tran≃ (symm≃ distrR≃ ) j
-- ah : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (a × 𝟎) b
-- ah {n} {a} {b} j = (annih×≃ a) ~t j


-- Helpful lemmas
+1× : ∀ {n} {A B : ADT n} (c : ℕ)  → Iso ((Num c × A) ⊔ A) B → Iso (Num (succ c) × A) B
+1× {n} {A} {B} c toB = tran≃ e1 toB where
  e1 = tran≃ distrR≃ (tran≃ (comm⊔≃ _ _ ) (∨≃ (refl≃ _) (symm≃ (id×≃ _ ) ) ) )

cycle+ : ∀ {n} {A B C : ADT n} → Iso (A ⊔ B ⊔ C) (B ⊔ C ⊔ A)
cycle+ = c+= (a+= !! )

dist3 : ∀ {n} {A B C D : ADT n} → Iso (A × (B ⊔ C ⊔ D)) (A × B ⊔ A × C ⊔ A × D)
dist3 = dl= (!+ dl)

foil : ∀ {n} {A B : ADT n} → Iso ((A ⊔ B) ²) (A ² ⊔ (Num 2 × A × B) ⊔ B ²)
foil {n} {A} {B} = dl= (cong+= dr dr (a+= (+= (a+ ~!= =+ (=+ c× =!= (=+ (~~ i×l) =!~ (+1× 1 (=+ (=× i+r))) ) ) ) ) ))

-- μiso : ∀ {n} (e : ADT (succ n)) → Iso (μ e) (e [ (μ e) ])
μiso : ∀ {n} (e : ADT (succ n)) (ρ : SetEnv n) → ⟦ μ e ⟧ ρ ≃ ⟦ e [ (μ e) ] ⟧ ρ
μiso {n} e ρ with iso~ (Lambek (λ x → ⟦ e ⟧ (ρ ⅋o:= x)  )) | substlemmagen e (μ e) ρ o
... | li | sl = li iso∘ iso~ sl

≃⟦_⟧ : ∀ {n} {A B : ADT n} → Iso A B → ( ρ : SetEnv n) → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ
≃⟦_⟧≃ : ∀ {n} {A B : ADT n} → Iso A B → {ρ ρ' : SetEnv n} → SetEnv≃ ρ ρ' → ⟦ A ⟧ ρ ≃ ⟦ B ⟧ ρ'

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
≃⟦_⟧ {n} (subst≃ {e1} {e2} {d1} {d2} j1 j2) ρ with substlemmagen e1 d1 ρ (o) | substlemmagen e2 d2 ρ (o)
... | sl1 | sl2 = sl1 iso∘ iso~ (sl2 iso∘ iso~ (≃⟦ j1 ⟧≃ (coskipSet≃ ρ (o) (≃⟦ j2 ⟧ ρ)) ) )
≃⟦ assoc×≃ a b c ⟧ ρ = assoc∧
≃⟦ assoc⊔≃ a b c ⟧ ρ = assoc∨
≃⟦ comm⊔≃ a b ⟧ ρ = comm∨
≃⟦ comm×≃ a b ⟧ ρ = comm∧
≃⟦ id⊔≃ _ ⟧ ρ = id∨
≃⟦ id×≃ _ ⟧ ρ = id∧
≃⟦ annih×≃ a ⟧ ρ = annih∧

≃⟦_⟧≃ {A = A} {B = B} e {ρ} {ρ'} ρρ' = ≃⟦ e ⟧ ρ iso∘ (⟦ B ⟧≃ ρρ')
