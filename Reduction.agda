-- {-# OPTIONS --allow-unsolved-metas #-}
module Reduction where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Relations.Core
open import Relations.ClosureOperators

𝓡Λ : Set₁
𝓡Λ = ∀ {X} → Λ X → Λ X → Set

-- The axiom of beta reduction
-- s ⟶ₒ t  if t results from s by contracting a beta redex
--             AT THE ROOT of the syntax tree
-- ⟶ₒ is \-->\_o
data _⟶ₒ_ {X : Set} : Λ X → Λ X → Set where
  redex : ∀ {r s t}  →  (e : s [ t ]ₒ ≡ r)  →  app (abs s) t ⟶ₒ r

-- One-step beta reduction is the contextual closure of ⟶ₒ
data _⟶β_ {X : Set} : Λ X → Λ X → Set where
  red⟶β  : ∀ {s t}     →  s ⟶ₒ t       →  s ⟶β t
  appL⟶β : ∀ {s1 s2 t} → s1 ⟶β s2      → app s1 t ⟶β app s2 t
  appR⟶β : ∀ {s t1 t2} → t1 ⟶β t2      → app s t1 ⟶β app s t2
  abs⟶β  : ∀ {r1 r2}   → r1 ⟶β r2      → abs r1   ⟶β abs r2

-- Weak head reduction is weaker: it's the closure of ⟶ₒ under applicative contexts only
data _⟶w_ {X} : Λ X → Λ X → Set where
  red⟶w : ∀ {s t}     →  s ⟶ₒ t  →  s ⟶w t
  appL⟶w : ∀ {s t r}  →  s ⟶w t  →  app s r ⟶w app t r

-- Standard reduction is the least congruence closed under weak head expansion
-- (AKA "outside-in" reduction)
data _⟶s_ {X} : Λ X → Λ X → Set where
  red⟶s : ∀ {r s t}       → r ⟶w s   →  s ⟶s t   →  r ⟶s t
  var⟶s : ∀ {x}           → var x ⟶s var x
  app⟶s : ∀ {s1 s2 t1 t2} → s1 ⟶s s2 → t1 ⟶s t2 → app s1 t1 ⟶s app s2 t2
  abs⟶s : ∀ {r1 r2}       → r1 ⟶s r2 → abs r1 ⟶s abs r2

map⟶ₒ : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶ₒ t2 → Λ→ f t1 ⟶ₒ Λ→ f t2
map⟶ₒ f (redex {_} {r} {t} refl) = redex (e1 ~! e2) where
  e0 = λ {  (i x) → refl ; o → refl }
  e1 = bind-nat₁ {f = ↑→ f} {io var (Λ→ f t)} e0 r
  e2 = bind-nat₂ {f = io var t} {f} !≅! r

map⟶β : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶β t2 → Λ→ f t1 ⟶β Λ→ f t2
map⟶β f (red⟶β x) = red⟶β (map⟶ₒ f x )
map⟶β f (appL⟶β t12) = appL⟶β (map⟶β f t12)
map⟶β f (appR⟶β t12) = appR⟶β (map⟶β f t12)
map⟶β f (abs⟶β t12) = abs⟶β (map⟶β (↑→ f) t12)

map⟶w : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶w t2 → Λ→ f t1 ⟶w Λ→ f t2
map⟶w f {t1} {t2} (red⟶w Δ) = red⟶w (map⟶ₒ f Δ)
map⟶w f (appL⟶w t12) = appL⟶w (map⟶w f t12)

_⟶β[_] : ∀ {X Y : Set} {s t : Λ X} → s ⟶β t → ∀ (f : X → Λ Y) → s [ f ] ⟶β t [ f ]
red⟶β {s = app (abs s) t} (redex refl) ⟶β[ f ] = red⟶β (redex (~ (subst-lemma s t f)) )
appL⟶β st ⟶β[ f ] = appL⟶β (st ⟶β[ f ])
appR⟶β st ⟶β[ f ] = appR⟶β (st ⟶β[ f ])
abs⟶β st ⟶β[ f ] = abs⟶β (st ⟶β[ lift f ])

-- Multistep reduction is the reflexive-transitive closure of one-step reduction
_⟶β⋆_ : ∀ {X} → Λ X → Λ X → Set
_⟶β⋆_ = (_⟶β_) ⋆

_≡!⟶s_ : ∀ {X} {r s t : Λ X} → (r ≡ s) → (s ⟶s t) → (r ⟶s t)
refl ≡!⟶s st = st

refl⟶s : ∀ {X} {t : Λ X} → t ⟶s t
refl⟶s {X} {var x} = var⟶s
refl⟶s {X} {app t t₁} = app⟶s refl⟶s refl⟶s
refl⟶s {X} {abs t} = abs⟶s refl⟶s

map⟶s : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶s t2 → Λ→ f t1 ⟶s Λ→ f t2
map⟶s f (red⟶s W t12) = red⟶s (map⟶w f W ) (map⟶s f t12)
map⟶s f var⟶s = var⟶s
map⟶s f (app⟶s t12 t13) = app⟶s (map⟶s f t12) (map⟶s f t13)
map⟶s f (abs⟶s t12) = abs⟶s (map⟶s (↑→ f) t12)

lift⟶s : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⟶s g x) → (∀ y → lift f y ⟶s lift g y)
lift⟶s f g f→g (i x) = map⟶s i (f→g x)
lift⟶s f g f→g o = var⟶s

bind⟶ₒ : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶ₒ t) → (s [ f ]) ⟶ₒ (t [ f ])
bind⟶ₒ f (redex {_} {s} {t} refl) = redex ((bind-assoc s ~! (e ! bind-assoc s))) where
  e1 = λ { (i x) → bind-lift2 (t [ f ]) (f x) ; o → refl }
  e = bind≅ e1 s

bind⟶w : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶w t) → (s [ f ]) ⟶w (t [ f ])
bind⟶w f (red⟶w rd) = red⟶w (bind⟶ₒ f rd)
bind⟶w f (appL⟶w st) = appL⟶w (bind⟶w f st)

bind⟶s : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶s t) → (s [ f ]) ⟶s (t [ f ])
bind⟶s f (red⟶s w s→t) = red⟶s (bind⟶w f w) (bind⟶s f s→t)
bind⟶s f var⟶s = refl⟶s
bind⟶s f (app⟶s s→t1 s→t2) = app⟶s (bind⟶s f s→t1) (bind⟶s f s→t2)
bind⟶s f (abs⟶s s→t) = abs⟶s (bind⟶s (lift f) s→t)

sred-subst : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⟶s g x) → (∀ t → (t [ f ]) ⟶s (t [ g ]))
sred-subst f g f→g (var x) = f→g x
sred-subst f g f→g (app s t) = app⟶s (sred-subst f g f→g s) (sred-subst f g f→g t)
sred-subst f g f→g (abs t) = abs⟶s (sred-subst (lift f) (lift g) (lift⟶s f g f→g) t )

bind⟶β⋆ : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶β⋆ t) → (s [ f ]) ⟶β⋆ (t [ f ])
bind⟶β⋆ f ε⋆ = ε⋆
bind⟶β⋆ f (R0 ,⋆ R+) = (R0 ⟶β[ f ]) ,⋆ bind⟶β⋆ f R+

⟶ₒ[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶ₒ t →   (s [ f ])  ⟶s  (t [ g ])
⟶ₒ[⟶s] f g f→g (redex {s = s} {t} refl) = red⟶s (red⟶w (redex refl) ) (E ≡!⟶s R) where
  E1 = bind-assoc≅ {f = lift f} {io var (t [ f ])} {io f (t [ f ])}
                   (io𝓟 _ (λ x → ~ (bind-lift2 (t [ f ]) (f x) ) ) refl ) s
  E2 = bind-assoc≅ (io𝓟 _ (λ x → refl) refl) s
  E = E1 ~! E2 -- E1 ! E2
  R = sred-subst f g f→g (s [ io var t ])

⟶w[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶w t →   (s [ f ])  ⟶s  (t [ g ])
⟶w[⟶s] f g f→g (red⟶w Δ) = ⟶ₒ[⟶s] f g f→g Δ
⟶w[⟶s] f g f→g (appL⟶w {r = r} s→t) = app⟶s (⟶w[⟶s] f g f→g s→t ) (sred-subst f g f→g r )

⟶s[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶s t →   (s [ f ])  ⟶s  (t [ g ])
⟶s[⟶s] f g f→g (red⟶s s→t t→u) = red⟶s (bind⟶w f s→t ) (⟶s[⟶s] f g f→g  t→u)
⟶s[⟶s] f g f→g var⟶s = f→g _
⟶s[⟶s] f g f→g (app⟶s R1 R2) = app⟶s (⟶s[⟶s] f g f→g R1) (⟶s[⟶s] f g f→g R2)
⟶s[⟶s] f g f→g (abs⟶s R0) = abs⟶s (⟶s[⟶s] (lift f) (lift g) (lift⟶s f g f→g) R0 )

⟶s[⟶s]ₒ : ∀ {X} → {s1 s2 : Λ (↑ X)} → {t1 t2 : Λ X} → s1 ⟶s s2 → t1 ⟶s t2 → (s1 [ t1 ]ₒ) ⟶s (s2 [ t2 ]ₒ)
⟶s[⟶s]ₒ {X} {s1} {s2} {t1} {t2} s12 t12 =
  ⟶s[⟶s] (io var t1) (io var t2) (io𝓟 _ (λ x → var⟶s) t12) s12

⟶s!⟶ₒ : ∀ {X} {t1 t2 t3 : Λ X} → (t1 ⟶s t2) → (t2 ⟶ₒ t3) → (t1 ⟶s t3)
⟶s!⟶ₒ (red⟶s W t12) r@(redex refl) = red⟶s W (⟶s!⟶ₒ t12 r)
⟶s!⟶ₒ (app⟶s {s1 = s1} {s2} {t1} {t2} s1s2 t1t2) r@(redex {s = s} refl) = wredLemma s1 s1s2 where
  wredLemma : ∀ u → (u ⟶s abs s) → app u t1 ⟶s (s [ t2 ]ₒ)
  wredLemma u (red⟶s {s = v} u→v u→λs) = red⟶s (appL⟶w u→v ) (wredLemma v u→λs )
  wredLemma (abs w) (abs⟶s u→λs) = red⟶s (red⟶w (redex refl) ) R
    where R = ⟶s[⟶s] (io var _) (io var _) (io𝓟 _ (λ x → var⟶s) t1t2 ) u→λs

⟶s!⟶w : ∀ {X} {t1 t2 t3 : Λ X} → (t1 ⟶s t2) → (t2 ⟶w t3) → (t1 ⟶s t3)
⟶s!⟶w (red⟶s W t12) (red⟶w (redex {r0} {r1} {r2} re)) rewrite ~ re =
        red⟶s W (⟶s!⟶w t12 (red⟶w (redex refl)) )
⟶s!⟶w (app⟶s {s1} {s2} {t1} {t2} s1r1 t12) (red⟶w (redex {r0} {r1} {t2} re)) rewrite ~ re = sr _ s1r1
  where sr : ∀ u → u ⟶s abs r1 → app u t1 ⟶s (r1 [ t2 ]ₒ)
        sr u (red⟶s u→s u→λr1) = red⟶s (appL⟶w u→s ) (sr _ u→λr1)
        sr (abs w) (abs⟶s u→λr1) = red⟶s (red⟶w (redex refl))
          (⟶s[⟶s] (io var t1 ) (io var t2)  (io𝓟 _ (λ x → var⟶s) t12 ) u→λr1)
⟶s!⟶w (red⟶s W t12) (appL⟶w t23) = red⟶s W (⟶s!⟶w t12 (appL⟶w t23))
⟶s!⟶w (app⟶s t12 t13) (appL⟶w t23) = app⟶s (⟶s!⟶w t12 t23) t13

⟶s!⟶s : ∀ {X} {r s t : Λ X} → (r ⟶s s) → (s ⟶s t) → (r ⟶s t)
⟶s!⟶s rs               (red⟶s W st)    = ⟶s!⟶s (⟶s!⟶w rs W ) st
⟶s!⟶s (red⟶s W rs)    st               = red⟶s W (⟶s!⟶s rs st)
⟶s!⟶s rs               var⟶s           = rs
⟶s!⟶s (app⟶s rs1 rs2) (app⟶s st1 st2) = app⟶s (⟶s!⟶s rs1 st1) (⟶s!⟶s rs2 st2)
⟶s!⟶s (abs⟶s rs)      (abs⟶s st)      = abs⟶s (⟶s!⟶s rs st)

-- Parallel reduction
-- AKA "inside-out" reduction strategy
-- ­⇉ is \r-2
data _⇉_ {X : Set} : Λ X → Λ X → Set where
  red⇉ : ∀ {s1 s2 : Λ (↑ X)} {t1 t2 t3 : Λ X}
           → s1 ⇉ s2 → t1 ⇉ t2 → s2 [ t2 ]ₒ ≡ t3 → (app (abs s1) t1) ⇉ t3
  var⇉ : ∀ {x}           → var x ⇉ var x
  app⇉ : ∀ {s1 s2 t1 t2} → s1 ⇉ s2 → t1 ⇉ t2 → app s1 t1 ⇉ app s2 t2
  abs⇉ : ∀ {r1 r2}       → r1 ⇉ r2 → abs r1 ⇉ abs r2

-- Relations between reduction relations
⟶w⊆⟶β : ∀ {X} {s t : Λ X} → s ⟶w t  →  s ⟶β t
⟶w⊆⟶β (red⟶w st) = red⟶β st
⟶w⊆⟶β (appL⟶w  s12) = appL⟶β (⟶w⊆⟶β s12)

⟶w!red : ∀ {X} {s t1 t2 : Λ X} {r} (sr : s ⟶s abs r) (t12 : t1 ⟶s t2)
          → app s t1 ⟶s (r [ t2 ]ₒ)
⟶w!red (red⟶s W sr) t12 = red⟶s (appL⟶w W ) (⟶w!red sr t12 )
⟶w!red {t1 = t1} {t2} (abs⟶s sr) t12 = red⟶s (red⟶w (redex refl ) ) (⟶s[⟶s] (io var t1) (io var t2) f=g sr )
  where f=g = λ {  (i x) → var⟶s ; o → t12 }

⟶s!⟶β : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β t → r ⟶s t
⟶s!⟶β (red⟶s r0 rs) st = red⟶s r0 (⟶s!⟶β rs st)
⟶s!⟶β var⟶s (red⟶β ())
⟶s!⟶β (abs⟶s rs) (abs⟶β st) = abs⟶s (⟶s!⟶β rs st)
⟶s!⟶β (app⟶s (red⟶s W rs) t12) br@(red⟶β (redex s[t2]=t)) rewrite ~ s[t2]=t
  = ⟶w!red (red⟶s W rs ) t12
⟶s!⟶β (app⟶s (abs⟶s rs) t12) (red⟶β (redex s[t2]=t)) rewrite ~ s[t2]=t
  = red⟶s (red⟶w (redex refl ) ) (⟶s[⟶s] _ _ e rs )
    where e = io𝓟 _ (λ x → var⟶s) t12
⟶s!⟶β (app⟶s s12 t12) (appL⟶β st) = app⟶s (⟶s!⟶β s12 st) t12
⟶s!⟶β (app⟶s s12 t12) (appR⟶β st) = app⟶s s12 (⟶s!⟶β t12 st)

⟶s!⟶β⋆ : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β⋆ t → r ⟶s t
⟶s!⟶β⋆ rs ε⋆ = rs
⟶s!⟶β⋆ rs (sy ,⋆ yt) = ⟶s!⟶β⋆ (⟶s!⟶β rs sy) yt

-- Standardization theorem for beta reduction
⟶β⋆⊆⟶s : ∀ {X} {s t : Λ X} →  s ⟶β⋆ t → s ⟶s t
⟶β⋆⊆⟶s = ⟶s!⟶β⋆ refl⟶s

⟶β⋆!⟶s⊆⟶s : ∀ {X} {r s t : Λ X} → r ⟶β⋆ s → s ⟶s t → r ⟶s t
⟶β⋆!⟶s⊆⟶s = ⟶s!⟶s ∘ ⟶β⋆⊆⟶s

-- NF : ∀ {X} → 𝓟 (Λ X)
-- NF M = ∀ N → ¬ (M ⟶β N)

map⇉ : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⇉ t2 → Λ→ f t1 ⇉ Λ→ f t2
map⇉ f (red⇉ {s1} {s2} {t1} {t2} s12 t12 refl) =
  red⇉ (map⇉ (↑→ f) s12) (map⇉ f t12) (~ (bind-map s2 t2 f) )
map⇉ f var⇉ = var⇉
map⇉ f (app⇉ t12 t13) = app⇉ (map⇉ f t12) (map⇉ f t13)
map⇉ f (abs⇉ t12) = abs⇉ (map⇉ (↑→ f) t12)

lift⇉ : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⇉ g x) → (∀ y → lift f y ⇉ lift g y)
lift⇉ f g f→g (i x) = map⇉ i (f→g x)
lift⇉ f g f→g o = var⇉

⇉[⇉] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⇉ g x)
             → ∀ {s t : Λ X} → s ⇉ t →   (s [ f ])  ⇉  (t [ g ])
⇉[⇉] f g f⇉g {(app (abs s1) s2)} {t} (red⇉ {u1} {u2} {t1} {t2} s⇉t1 s⇉t2 refl) =
  red⇉ (⇉[⇉] (lift f) (lift g) (lift⇉ f g f⇉g) s⇉t1) (⇉[⇉] f g f⇉g s⇉t2)
        (~ (subst-lemma u2 t2 g) )
⇉[⇉] f g f⇉g {(var x)} {.(var x)} var⇉ = f⇉g x
⇉[⇉] f g f⇉g {(app s1 s2)} {(app t1 t2)} (app⇉ s1⇉t1 s2⇉t2) = app⇉ (⇉[⇉] f g f⇉g s1⇉t1) (⇉[⇉] f g f⇉g s2⇉t2)
⇉[⇉] f g f⇉g {(abs r1)} {(abs r2)} (abs⇉ s⇉t) = abs⇉ (⇉[⇉] (lift f) (lift g) (lift⇉ f g f⇉g) s⇉t )

⇉[⇉]ₒ : ∀ {X} → {s1 s2 : Λ (↑ X)} → {t1 t2 : Λ X} → s1 ⇉ s2 → t1 ⇉ t2 → (s1 [ t1 ]ₒ) ⇉ (s2 [ t2 ]ₒ)
⇉[⇉]ₒ {X} {s1} {s2} {t1} {t2} s12 t12 =
  ⇉[⇉] (io var t1) (io var t2) (io𝓟 _ (λ x → var⇉) t12) s12

⟶w\⇉ : ∀ {X} {s t1 t2 : Λ X} → s ⟶w t1 → s ⇉ t2 → Σ[ u ∈ Λ X ] (t1 ⇉ u × (_⟶w_ ʳ) t2 u)
⟶w\⇉ (red⟶w (redex refl)) (red⇉ {s2 = s2} {t2 = t2} s⇉s2 t⇉t2 refl) =
  s2 [ t2 ]ₒ ,, ⇉[⇉]ₒ s⇉s2 t⇉t2 , εʳ
⟶w\⇉ (red⟶w (redex refl)) (app⇉ {s2 = (abs s3)} {t2 = t2} (abs⇉ s⇉s3) t⇉t2) =
  s3 [ t2 ]ₒ ,, ⇉[⇉]ₒ s⇉s3 t⇉t2 , axʳ (red⟶w (redex refl))
⟶w\⇉ (appL⟶w (red⟶w ())) (red⇉ s⇉t2 s⇉t3 x)
⟶w\⇉ (appL⟶w s⟶t1) (app⇉ s⇉t2 s⇉t3) with ⟶w\⇉ s⟶t1 s⇉t2
... | u ,, t1⇉u , axʳ W = app u _ ,, app⇉ t1⇉u s⇉t3 , axʳ (appL⟶w W )
... | u ,, t1⇉u , εʳ    = app u _ ,, app⇉ t1⇉u s⇉t3 , εʳ

⟶s\⇉ : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⇉ t2 → Σ[ u ∈ Λ X ] (t1 ⇉ u × t2 ⟶s u)
⟶s\⇉ (red⟶s W s⟶t1) s⇉t2 with ⟶w\⇉ W s⇉t2
... | u ,, s1⇉u , εʳ       = ⟶s\⇉ s⟶t1 s1⇉u
... | u ,, s1⇉u , axʳ W with ⟶s\⇉ s⟶t1 s1⇉u
... | v ,, t1⇉v , u⟶sv = v ,, t1⇉v , red⟶s W u⟶sv
⟶s\⇉ var⟶s var⇉ = var _ ,, var⇉ , var⟶s
⟶s\⇉ (app⟶s (red⟶s (red⟶w ()) s⟶t1) s⟶t2) (red⇉ s⇉t2 s⇉t3 r)
⟶s\⇉ (app⟶s (abs⟶s s1⟶t11) s2⟶t21) (red⇉ {s1} {s2} {t1} {t2} {t3} s1⇉t12 s2⇉t22 refl)
  with ⟶s\⇉ s1⟶t11 s1⇉t12 | ⟶s\⇉ s2⟶t21 s2⇉t22
... | (u1 ,, t11⇉u1 , t21⟶u1) | (u2 ,, t21⇉u2 , t22⟶u2) =
  u1 [ u2 ]ₒ ,, red⇉ t11⇉u1 t21⇉u2 refl , (⟶s[⟶s]ₒ t21⟶u1 t22⟶u2  )
⟶s\⇉ (app⟶s s1⟶t11 s2⟶t21) (app⇉ s1⇉t12 s2⇉t22) with ⟶s\⇉ s1⟶t11 s1⇉t12 | ⟶s\⇉ s2⟶t21 s2⇉t22
... | (u1 ,, t11⇉u1 , t21⟶u1) | (u2 ,, t21⇉u2 , t22⟶u2) = (app u1 u2 ,, app⇉ t11⇉u1 t21⇉u2 , app⟶s t21⟶u1 t22⟶u2 )
⟶s\⇉ (abs⟶s s⟶t1) (abs⇉ s⇉t2) with ⟶s\⇉ s⟶t1 s⇉t2
... | (u ,, t1⇉u , t2⟶u) = abs u ,, abs⇉ t1⇉u , abs⟶s t2⟶u

refl⇉ : ∀ {X} {t : Λ X} → t ⇉ t
refl⇉ {X} {var x} = var⇉
refl⇉ {X} {app s t} = app⇉ refl⇉ refl⇉
refl⇉ {X} {abs r} = abs⇉ refl⇉

⟶β⊆⇉ : ∀ {X} {s t : Λ X} → s ⟶β t  →  s ⇉ t
⟶β⊆⇉ (red⟶β (redex e)) = red⇉ refl⇉ refl⇉ e
⟶β⊆⇉ (appL⟶β st) = app⇉ (⟶β⊆⇉ st ) refl⇉
⟶β⊆⇉ (appR⟶β st) = app⇉ refl⇉ (⟶β⊆⇉ st)
⟶β⊆⇉ (abs⟶β st) = abs⇉ (⟶β⊆⇉ st)

_⇉⋆_ : ∀ {X} → Λ X → Λ X → Set
_⇉⋆_ = _⇉_ ⋆

⟶β⋆⊆⇉⋆ : ∀ {X} {s t : Λ X} → s ⟶β⋆ t  →  s ⇉⋆ t
⟶β⋆⊆⇉⋆ = ⊆⋆ (λ x y → ⟶β⊆⇉) _ _

_⇉[_] : ∀ {X Y : Set} {s t : Λ X} → s ⇉ t → ∀ (σ : X → Λ Y) → s [ σ ] ⇉ t [ σ ]
red⇉ {s1 = s1} {s2} {t1} {t2} p1 p2 e ⇉[ σ ]
  = red⇉ (p1 ⇉[ lift σ ]) (p2 ⇉[ σ ]) (subst-lemma s2 t2 σ ~! cong (λ z → z [ σ ]) e)
var⇉         ⇉[ σ ] = refl⇉
app⇉ st1 st2 ⇉[ σ ] = app⇉ (st1 ⇉[ σ ]) (st2 ⇉[ σ ])
abs⇉ st      ⇉[ σ ] = abs⇉ (st ⇉[ lift σ ])

app⇉⋆ : ∀ {X} {s1 s2 t1 t2 : Λ X} → s1 ⇉⋆ s2 → t1 ⇉⋆ t2 → app s1 t1 ⇉⋆ app s2 t2
app⇉⋆ ε⋆ ε⋆ = ε⋆
app⇉⋆ ε⋆ (t0 ,⋆ t12) = app⇉ refl⇉ t0 ,⋆ app⇉⋆ ε⋆ t12
app⇉⋆ (s0 ,⋆ s12) ε⋆ = app⇉ s0 refl⇉ ,⋆ app⇉⋆ s12 ε⋆
app⇉⋆ (s0 ,⋆ s12) (t0 ,⋆ t12) = app⇉ s0 t0 ,⋆ app⇉⋆ s12 t12

_⇉⋆[_] : ∀ {X Y : Set} {s t : Λ X} → s ⇉⋆ t → ∀ (σ : X → Λ Y) → s [ σ ] ⇉⋆ t [ σ ]
ε⋆         ⇉⋆[ σ ] = ε⋆
(st ,⋆ tu) ⇉⋆[ σ ] = (st ⇉[ σ ]) ,⋆ (tu ⇉⋆[ σ ])


⟶s\⇉⋆ : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⇉⋆ t2 → Σ[ u ∈ Λ X ] (t1 ⇉⋆ u × t2 ⟶s u)
⟶s\⇉⋆ st1 ε⋆ = _ ,, ε⋆ , st1
⟶s\⇉⋆ st1 (pr0 ,⋆ pr1) with ⟶s\⇉ st1 pr0
... | (u ,, pr2 , st2) with ⟶s\⇉⋆ st2 pr1
... | (v ,, pr3 , st3) = v ,, (pr2 ,⋆ pr3) , st3

_⟶w⋆_ : ∀ {X} → Λ X → Λ X → Set 
_⟶w⋆_ = _⟶w_ ⋆

map⟶w⋆ : ∀ {X Y} (f : X → Y) → ∀ {s t : Λ X} → s ⟶w⋆ t → Λ→ f s ⟶w⋆ Λ→ f t  
map⟶w⋆ f ε⋆ = ε⋆
map⟶w⋆ f (R0 ,⋆ R+) = map⟶w f R0 ,⋆ map⟶w⋆ f R+

bind⟶w⋆ : ∀ {X Y} → (f : X → Λ Y) → ∀ {s t : Λ X} → (s ⟶w⋆ t) → (s [ f ]) ⟶w⋆ (t [ f ])
bind⟶w⋆ f ε⋆ = ε⋆
bind⟶w⋆ f (R0 ,⋆ R+) = bind⟶w f R0 ,⋆ bind⟶w⋆ f R+

appL⟶w⋆ : ∀ {X} {s1 s2 t : Λ X} → s1 ⟶w⋆ s2 → app s1 t ⟶w⋆ app s2 t
appL⟶w⋆ ε⋆ = ε⋆
appL⟶w⋆ (W0 ,⋆ W+) = appL⟶w W0 ,⋆ appL⟶w⋆ W+

abs⟶β⋆ : ∀ {X} {r1 r2 : Λ (↑ X)} → r1 ⟶β⋆ r2 → abs r1 ⟶β⋆ abs r2
abs⟶β⋆ ε⋆ = ε⋆
abs⟶β⋆ (r0 ,⋆ r12) = abs⟶β r0 ,⋆ abs⟶β⋆ r12

appL⟶β⋆ : ∀ {X} {s1 s2 : Λ X} → s1 ⟶β⋆ s2 → ∀ t → app s1 t ⟶β⋆ app s2 t
appL⟶β⋆ ε⋆ t = ε⋆
appL⟶β⋆ (s0 ,⋆ s12) t = appL⟶β s0 ,⋆ appL⟶β⋆ s12 t

appR⟶β⋆ : ∀ {X} {s1 s2 : Λ X} → s1 ⟶β⋆ s2 → ∀ t → app t s1 ⟶β⋆ app t s2
appR⟶β⋆ ε⋆ t = ε⋆
appR⟶β⋆ (s0 ,⋆ s12) t = appR⟶β s0 ,⋆ appR⟶β⋆ s12 t

⟶w⋆!⟶s :  ∀ {X} {s t u : Λ X} → s ⟶w⋆ t → t ⟶s u → s ⟶s u 
⟶w⋆!⟶s ε⋆ t→u = t→u
⟶w⋆!⟶s (s0→s ,⋆ s→t) t→u = red⟶s s0→s (⟶w⋆!⟶s s→t t→u)

⟶s⊆⟶β⋆ : ∀ {X} → _⟶s_ {X} ⊆ _⟶β⋆_ {X}
⟶s⊆⟶β⋆ s t (red⟶s W st) = ⟶w⊆⟶β W ,⋆ ⟶s⊆⟶β⋆ _ _ st
⟶s⊆⟶β⋆ (var _) (var _) var⟶s = ε⋆
⟶s⊆⟶β⋆ (abs r1) (abs r2) (abs⟶s r12) = abs⟶β⋆ (⟶s⊆⟶β⋆ _ _ r12)
⟶s⊆⟶β⋆ (app s1 s2) (app t1 t2) (app⟶s s12 t12) =
  appL⟶β⋆ (⟶s⊆⟶β⋆ _ _ s12) s2 ⋆!⋆ appR⟶β⋆ (⟶s⊆⟶β⋆ _ _ t12) t1

⇉⊆⟶β⋆ : ∀ {X} {s t : Λ X} → s ⇉ t  →  s ⟶β⋆ t
⇉⊆⟶β⋆ (red⇉ {s1} {s2} {t1} {t2} s12 t12 refl) = 
  (red⟶β (redex refl ) ) ,⋆ (R1 ⋆!⋆ R3) where 
    R1 = bind⟶β⋆ (io var t1) (⇉⊆⟶β⋆ s12)
    R2 = io𝓟 _ (λ x → var⟶s) (⟶β⋆⊆⟶s (⇉⊆⟶β⋆ t12))
    R3 = ⟶s⊆⟶β⋆ (s2 [ t1 ]ₒ) (s2 [ t2 ]ₒ) (sred-subst (io var t1) (io var t2) R2 s2) 
⇉⊆⟶β⋆ var⇉ = ε⋆
⇉⊆⟶β⋆ (app⇉ s12 t12) = (appL⟶β⋆ (⇉⊆⟶β⋆ s12) _ ) ⋆!⋆ appR⟶β⋆ (⇉⊆⟶β⋆ t12 ) _
⇉⊆⟶β⋆ (abs⇉ st) = abs⟶β⋆ (⇉⊆⟶β⋆ st)

⇉⋆⊆⟶β⋆ : ∀ {X} {s t : Λ X} → s ⇉⋆ t  →  s ⟶β⋆ t
⇉⋆⊆⟶β⋆ ε⋆ = ε⋆
⇉⋆⊆⟶β⋆ (st ,⋆ tu) = ⇉⊆⟶β⋆ st ⋆!⋆ ⇉⋆⊆⟶β⋆ tu

⟶s\⟶s : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⟶s t2 → Σ[ u ∈ Λ X ] (t1 ⟶s u × t2 ⟶s u)
⟶s\⟶s st1 st2 
  with ⟶s\⇉⋆ st1 (⟶β⋆⊆⇉⋆ (⟶s⊆⟶β⋆ _ _ st2))
... | (u ,, t1u , t2u)  = u ,, ⟶β⋆⊆⟶s (⇉⋆⊆⟶β⋆ t1u) , t2u

NF : ∀ {X} → 𝓟 (Λ X)
NF M = ∀ N → ¬ (M ⟶β N)

absInv : ∀ {V} {N1 N2 : Λ (↑ V)} → abs N1 ≡ abs N2 → N1 ≡ N2
absInv refl = refl
appInvL : ∀ {V} {M1 M2 N1 N2 : Λ V} → app M1 M2 ≡ app N1 N2 → M1 ≡ N1
appInvL refl = refl
appInvR : ∀ {V} {M1 M2 N1 N2 : Λ V} → app M1 M2 ≡ app N1 N2 → M2 ≡ N2
appInvR refl = refl

absNFinv : ∀ {V} {s : Λ (↑ V)} → abs s ∈ NF → s ∈ NF
absNFinv s∈NF t s→t = s∈NF (abs t) (abs⟶β s→t )
appNFinvL : ∀ {V} {s t : Λ V} → app s t ∈ NF → s ∈ NF
appNFinvL {t = t} st∈NF u s→u = st∈NF (app u t) (appL⟶β s→u )
appNFinvR : ∀ {V} {s t : Λ V} → app s t ∈ NF → t ∈ NF
appNFinvR {s = s} st∈NF u t→u = st∈NF (app s u) (appR⟶β t→u )

var→w : ∀ {X} {s : Λ X} {x : X} → s ⟶s (var x) → (_⟶w_ ⋆) s (var x)
var→w {X} {s} {x} (red⟶s w R) = w ,⋆ var→w R
var→w {X} {s} {x} var⟶s = ε⋆

⟶sabs : ∀ {X} {s : Λ X} {r : Λ (↑ X)} → s ⟶s abs r → Σ[ t ∈ Λ (↑ X) ] (s ⟶w⋆ abs t × t ⟶s r)
⟶sabs (red⟶s s→s' s'→λr) with ⟶sabs s'→λr 
... | (t ,, s'→λt , t→r) = t ,, s→s' ,⋆ s'→λt , t→r 
⟶sabs (abs⟶s {r1 = t} s→r) = t ,, ε⋆ , s→r

⟶β⋆NF : ∀ {X} {s t : Λ X} → s ⟶β⋆ t → s ∈ NF → t ≡ s
⟶β⋆NF ε⋆ s∈NF = refl
⟶β⋆NF (s→s' ,⋆ s'→t) s∈NF = ∅ (s∈NF _ s→s')

⟶sNF : ∀ {X} {s t : Λ X} → s ⟶s t → s ∈ NF → t ≡ s
⟶sNF s→t s∈NF = ⟶β⋆NF (⟶s⊆⟶β⋆ _ _ s→t) s∈NF

{-
bindCong : ∀ (R : (∀ {X} → 𝓡Λ X)) → isCong R
             → ∀ {X Y : Set} → (f g : X → Λ Y) → (∀ x → R (f x) (g x))
             → ∀ t → R (bind f t) (bind g t)
bindCong R Rcong f g fRg (var x) = fRg x
bindCong R Rcong f g fRg (app s t) = Rcong _ _ (appCC (axCC (bindCong R Rcong f g fRg s))
                                                      (axCC (bindCong R Rcong f g fRg t)))
bindCong R Rcong f g fRg (abs r) = Rcong (abs (r [ io (λ z → Λ→ i (f z)) (var o) ])) (abs (r [ io (λ z → Λ→ i (g z)) (var o) ]))
                                    (absCC (axCC (bindCong R Rcong (lift f) (lift g) lfg r ) ) )
                                    where lfg = io𝓟 _ {!   !} (Rcong (var o) (var o) varCC)

reflCC : ∀ (R : ∀ {X} → 𝓡 (Λ X)) {X : Set} → ∀ (t : Λ X) → CC R t t
reflCC R (var x) = varCC
reflCC R (app t1 t2) = appCC (reflCC R t1) (reflCC R t2)
reflCC R (abs t0) = absCC (reflCC R t0 )


-- Relations between reduction relations
⟶w⊆⟶β : ∀ {X} → _⟶w_ {X} ⊆ _⟶β_
⟶w⊆⟶β s t (red⟶w st) = ax𝓡Λ st
⟶w⊆⟶β (app s t) (app  s' .t) (appL⟶w s→ws') = appL𝓡Λ (⟶w⊆⟶β s s' s→ws')

⟶s⊆⟶β⋆ : ∀ {X} → _⟶s_ {X} ⊆ _⟶β⋆_
⟶s⊆⟶β⋆ s t (red⟶s ss' s't) = ⟶w⊆⟶β s _ ss' ,⋆ ⟶s⊆⟶β⋆ _ t s't
⟶s⊆⟶β⋆ s t (CC⟶s st) = {!   !}

⟶β!⟶s : ∀ {X} {r s t : Λ X} → r ⟶β s → s ⟶s t → r ⟶s t
⟶β!⟶s (ax𝓡Λ rs) st = red⟶s (red⟶w rs ) st
⟶β!⟶s (appL𝓡Λ rs) st = {!   !}
⟶β!⟶s (appR𝓡Λ rs) st = {!   !}
⟶β!⟶s (abs𝓡Λ rs) = {!   !}

⟶s!⟶β : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶β t → r ⟶s t
⟶s!⟶β (red⟶s rr' r's) st = red⟶s rr' (⟶s!⟶β r's st)
⟶s!⟶β (CC⟶s (axCC rs)) st = ⟶s!⟶β rs st
⟶s!⟶β (CC⟶s varCC) (ax𝓡Λ st) = red⟶s (red⟶w st ) {!   !}
⟶s!⟶β (CC⟶s (appCC rs rs₁)) st = {!   !}
⟶s!⟶β (CC⟶s (absCC rs)) (abs𝓡Λ st) = CC⟶s (absCC (axCC (⟶s!⟶β {! rs  !} {!   !} ) ) )

⟶s!⟶s : ∀ {X} {r s t : Λ X} → r ⟶s s → s ⟶s t → r ⟶s t
⟶s!⟶s (red⟶s rr' r's) st = red⟶s rr' (⟶s!⟶s r's st)
⟶s!⟶s (CC⟶s x) st = {!   !}

-- Examples

-- The identity combinator
IC : ∀ {X} → Λ X
IC = abs (var o )

-- One-step beta reduction (contraction at the root)
II→I : ∀ {X} → app (IC {X}) IC ⟶β IC
II→I = ax𝓡Λ (red refl)
-- II→I = redexβ refl

-- Two-step beta reduction
I[II]→⋆I : ∀ {X} → (_⟶β_ ⋆) (app (IC {X}) (app IC IC)) IC
I[II]→⋆I = ax𝓡Λ (red refl) ,⋆ ax⋆ (ax𝓡Λ (red refl))
-- I[II]→⋆I = (redexβ refl ) ,⋆ (II→I ,⋆ ε⋆ )
-- I[II]→⋆I = (appRβ II→I ) ,⋆ (II→I ,⋆ ε⋆ )

-- Parallel reduction (contracting one redex only)
II⇉I : ∀ {X} → app IC IC ⇉ IC {X}
II⇉I {X} = red⇉ (CC⇉ varCC) (CC⇉ (absCC varCC)) refl
-- II⇉I {X} = red⇉ {X} {var o} {var o} {IC} {IC} {IC} (CC⇉ varCC )
--                 (CC⇉ (reflCC _⇉_ (abs (var o)) ) )
--                 refl

-- Parallel reduction (contracting multiple redexes)
src : Λ ⊥ -- (λx.x(II)(Ix))(II)
src = app (abs (app (app (var o) (app IC IC)) (app IC (var o)) ) ) (app IC IC)
tgt : Λ ⊥ -- (II)I
tgt = app (app IC IC) IC
src⇉tgt : src ⇉ tgt
src⇉tgt = red⇉ {s2 = app (app (var o) IC) (var o)} {t2 = IC}
            (CC⇉ (appCC {s1 = app (var o) (app IC IC)} {s2 = app (var o) IC}
                        {t1 = app IC (var o)} {t2 = var o}
                        (appCC varCC (axCC II⇉I ) ) (axCC (red⇉ (CC⇉ varCC) (CC⇉ varCC) refl) ) ) )
          II⇉I refl






-- Fixed Point Theorem
open import Agda.Builtin.Sigma renaming (_,_ to _,,_)

FPT : ∀ {X} (F : Λ X) → Σ[ YF ∈ Λ X ] (YF ⟶β⋆ app F YF)
FPT F =
  let W = abs (app (Λ→ i F) (app (var o) (var o)))
      WW→FWW : app W W ⟶β⋆ app F (app W W)
      WW→FWW = ax𝓡Λ (red (cong2 app {!   !} refl) ) ,⋆ ε⋆
   in (app W W ,, WW→FWW )

-- The end
-}
