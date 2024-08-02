module Reduction where

-- open import Logic-Levels
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
  redex : ∀ {r s t}  →  (s [ t ]ₒ ≡ r)  →  app (abs s) t ⟶ₒ r

-- One-step beta reduction is the contextual closure of ⟶ₒ
data _⟶β_ {X : Set} : Λ X → Λ X → Set where
  red⟶β  : ∀ {s t}     →  s ⟶ₒ t       →  s ⟶β t
  appL⟶β : ∀ {s1 s2 t} → s1 ⟶β s2      → app s1 t ⟶β app s2 t
  appR⟶β : ∀ {s t1 t2} → t1 ⟶β t2      → app s t1 ⟶β app s t2
  abs⟶β  : ∀ {r1 r2}   → r1 ⟶β r2      → abs r1   ⟶β abs r2

-- Weak head reduction is weaker than one-step reduction
data _⟶w_ {X} : Λ X → Λ X → Set where
  red⟶w : ∀ {s t}     →  s ⟶ₒ t  →  s ⟶w t
  appL⟶w : ∀ {s t r}  →  s ⟶w t  →  app s r ⟶w app t r

map⟶ₒ : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶ₒ t2 → Λ→ f t1 ⟶ₒ Λ→ f t2
map⟶ₒ f (redex {_} {r} {t} refl) = redex (e1 ~! e2) where
  e0 = λ {  (i x) → refl ; o → refl }
  e1 = bind-nat₁ {f = ↑→ f} {io var (Λ→ f t)} e0 r
  e2 = bind-nat₂ {f = io var t} {f} !≅! r

map⟶w : ∀ {X Y} → (f : X → Y) → {t1 t2 : Λ X} → t1 ⟶w t2 → Λ→ f t1 ⟶w Λ→ f t2
map⟶w f {t1} {t2} (red⟶w Δ) = red⟶w (map⟶ₒ f Δ)
map⟶w f (appL⟶w t12) = appL⟶w (map⟶w f t12)

-- Multistep reduction is the reflexive-transitive closure of one-step reduction
_⟶β⋆_ : ∀ {X} → Λ X → Λ X → Set
_⟶β⋆_ = (_⟶β_) ⋆

-- Standard reduction is the least congruence closed under
-- weak head expansion
-- AKA "outside-in" reduction strategy
data _⟶s_ {X} : Λ X → Λ X → Set where
  red⟶s : ∀ {r s t}       → r ⟶w s   →  s ⟶s t   →  r ⟶s t
  var⟶s : ∀ {x}           → var x ⟶s var x
  app⟶s : ∀ {s1 s2 t1 t2} → s1 ⟶s s2 → t1 ⟶s t2 → app s1 t1 ⟶s app s2 t2
  abs⟶s : ∀ {r1 r2}       → r1 ⟶s r2 → abs r1 ⟶s abs r2

_≡!⟶s_ : ∀ {X} {r s t : Λ X} → (r ≡ s) → (s ⟶s t) → (r ⟶s t)
refl ≡!⟶s st = st

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

bind⟶s : ∀ {X Y} → (f g : X → Λ Y) → (∀ x → f x ⟶s g x) → (∀ t → (t [ f ]) ⟶s (t [ g ]))
bind⟶s f g f→g (var x) = f→g x
bind⟶s f g f→g (app s t) = app⟶s (bind⟶s f g f→g s) (bind⟶s f g f→g t)
bind⟶s f g f→g (abs t) = abs⟶s (bind⟶s (lift f) (lift g) (lift⟶s f g f→g) t )

⟶ₒ[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶ₒ t →   (s [ f ])  ⟶s  (t [ g ])
⟶ₒ[⟶s] f g f→g (redex {s = s} {t} refl) = red⟶s (red⟶w (redex refl) ) (E ≡!⟶s R) where
  E1 = bind-assoc≅ {f = lift f} {io var (t [ f ])} {io f (t [ f ])}
                   (io𝓟 _ (λ x → ~ (bind-lift2 (t [ f ]) (f x) ) ) refl ) s
  E2 = bind-assoc≅ (io𝓟 _ (λ x → refl) refl) s
  E = E1 ~! E2 -- E1 ! E2
  R = bind⟶s f g f→g (s [ io var t ])

⟶w[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶w t →   (s [ f ])  ⟶s  (t [ g ])
⟶w[⟶s] f g f→g (red⟶w Δ) = ⟶ₒ[⟶s] f g f→g Δ
⟶w[⟶s] f g f→g (appL⟶w {r = r} s→t) = app⟶s (⟶w[⟶s] f g f→g s→t ) (bind⟶s f g f→g r )

⟶s[⟶s] : ∀ {X Y} (f g : X → Λ Y) → (∀ x → f x ⟶s g x)
             → ∀ {s t : Λ X} → s ⟶s t →   (s [ f ])  ⟶s  (t [ g ])
⟶s[⟶s] f g f→g (red⟶s s→t t→u) = red⟶s (bind⟶w f s→t ) (⟶s[⟶s] f g f→g  t→u)
⟶s[⟶s] f g f→g var⟶s = f→g _
⟶s[⟶s] f g f→g (app⟶s R1 R2) = app⟶s (⟶s[⟶s] f g f→g R1) (⟶s[⟶s] f g f→g R2)
⟶s[⟶s] f g f→g (abs⟶s R0) = abs⟶s (⟶s[⟶s] (lift f) (lift g) (lift⟶s f g f→g) R0 )

-- ⟶s!⟶s : ∀ {X} {r s t : Λ X} → (r ⟶s s) → (s ⟶s t) → (r ⟶s t)
-- ⟶s!⟶s (red⟶s W rs) st = red⟶s W (⟶s!⟶s rs st)
-- ⟶s!⟶s var⟶s st = st
-- ⟶s!⟶s (app⟶s (red⟶s s1→s s1s2) t1t2) R@(red⟶s (red⟶w W) s2t2u) =
--   red⟶s (appL⟶w s1→s ) (⟶s!⟶s (app⟶s s1s2 t1t2 ) R)
-- ⟶s!⟶s (app⟶s (abs⟶s s1s2) t1t2) R@(red⟶s (red⟶w W) s2t2u) = {!   !}
--   -- red⟶s (red⟶w (redex refl) ) (⟶s!⟶s (⟶s[⟶s] _ _ (io𝓟 _ (λ x → var⟶s) t1t2 ) s1s2) s2t2u )
-- ⟶s!⟶s (app⟶s s1s2 t1t2) (red⟶s (appL⟶w x) s2t2u) = {!   !}
-- ⟶s!⟶s (app⟶s s1s2 t1t2) (app⟶s s2s3 t2t3) = app⟶s (⟶s!⟶s s1s2 s2s3) (⟶s!⟶s t1t2 t2t3)
-- ⟶s!⟶s (abs⟶s rs) (red⟶s (red⟶w ()) st)
-- ⟶s!⟶s (abs⟶s rs) (abs⟶s st) = abs⟶s (⟶s!⟶s rs st)

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

-- Parallel reduction
-- AKA "inside-out" reduction strategy
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

refl⟶s : ∀ {X} {t : Λ X} → t ⟶s t
refl⟶s {X} {var x} = var⟶s
refl⟶s {X} {app t t₁} = app⟶s refl⟶s refl⟶s
refl⟶s {X} {abs t} = abs⟶s refl⟶s

⟶β⋆⊆⟶s : ∀ {X} {s t : Λ X} →  s ⟶β⋆ t → s ⟶s t
⟶β⋆⊆⟶s = ⟶s!⟶β⋆ refl⟶s

NF : ∀ {X} → 𝓟 (Λ X)
NF M = ∀ N → ¬ (M ⟶β N)


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
