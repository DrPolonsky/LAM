open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Relations.ClosureOperators
open import Reduction
open import Conversion

module FPC.FixedPointContexts where

-- A fixed point context is a term t ∈ Λ(X,vₒ) s.t. t =β vₒt
FPCx : ∀ {X} → 𝓟 (Λ (↑ X))
FPCx t =  t =β app (var o) t

-- The Owl Combinator δ = λyx.x(yx)
SI : ∀ {X} → Λ X
SI = abs (abs (app (var o) (app (var (i o)) (var o) ) ) )

⟶w-unique-tgt : ∀ {X} {s t1 t2 : Λ X} → s ⟶w t1 → s ⟶w t2 → t1 ≡ t2
⟶w-unique-tgt (red⟶w (redex e1)) (red⟶w (redex e2)) = e1 ~! e2
⟶w-unique-tgt (red⟶w (redex e)) (appL⟶w (red⟶w ()))
⟶w-unique-tgt (appL⟶w (red⟶w ())) (red⟶w (redex e))
⟶w-unique-tgt (appL⟶w {r = r} s→t1) (appL⟶w s→t2)
  = cong (λ z → app z r) (⟶w-unique-tgt s→t1 s→t2)

WHNF : ∀ {X} → Λ X → Set 
WHNF t = ∀ u → ¬ (t ⟶w u)

-- →sWHNF : ∀ {X} (s w : Λ X) → s ⟶s w → w ∈ WHNF → Σ[ t ∈ Λ X ] ((s ⟶w t) × ((t ∈ WHNF) × (t ⟶s w)))
-- →sWHNF s w (red⟶s x s→w) w∈WHNF = {! !}
-- →sWHNF s w var⟶s w∈WHNF = {! !}
-- →sWHNF s w (app⟶s s→w s→w₁) w∈WHNF = {! !}
-- →sWHNF s w (abs⟶s s→w) w∈WHNF = {! !}

⟶s\⟶w : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⟶w t2 → Σ[ u ∈ Λ X ] ((_⟶w_ ʳ) t1 u × t2 ⟶s u)
⟶s\⟶w var⟶s (red⟶w ())
⟶s\⟶w (abs⟶s s→t1) (red⟶w ())
⟶s\⟶w (red⟶s {t = t1} W s→t1) s→t2 rewrite ⟶w-unique-tgt s→t2 W = t1 ,, εʳ , s→t1
⟶s\⟶w (app⟶s vov{s2 = s2} {t1} {t2} (red⟶s (red⟶w ()) s→t1) s→t3) (red⟶w (redex {r} {s} e))
⟶s\⟶w (app⟶s {s2 = .(abs _)} {t1} {t2} (abs⟶s {r2 = r2} s→t1) s→t3) (red⟶w (redex {r} {s} e))
  = r2 [ t2 ]ₒ ,, axʳ (red⟶w (redex refl) ) , transp _ e (⟶s[⟶s]ₒ s→t1 s→t3)
⟶s\⟶w (app⟶s {t2 = t2} s→t1 s→t3) (appL⟶w s→t2) with ⟶s\⟶w s→t1 s→t2
... | u ,, axʳ s2→u , t→u = app u t2 ,, axʳ (appL⟶w s2→u ) , app⟶s t→u s→t3
... | u ,, εʳ , t→u = app u t2 ,, εʳ , (app⟶s t→u s→t3)

{-
xY[SI]→Y : ∀ {X} (Y : Λ (↑ X)) → app (Λ→i (app (var o) Y [ SI ]ₒ)) (var o) ⟶s app (var o) Y 
                               → app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y 
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) R)) = {!  !}
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (red⟶w (redex refl))) (red⟶s (appL⟶w (red⟶w ())) R))
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (red⟶w (redex refl))) (app⟶s R (red⟶s (red⟶w ()) R₁)))
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (red⟶w (redex refl))) (app⟶s (red⟶s (red⟶w ()) R) var⟶s))
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (appL⟶w (red⟶w ()))) R)
xY[SI]→Y Y (app⟶s R (red⟶s (red⟶w ()) R₁))
xY[SI]→Y Y (app⟶s (red⟶s (red⟶w (redex refl)) (red⟶s (red⟶w ()) R)) var⟶s)
xY[SI]→Y Y (app⟶s (red⟶s (appL⟶w (red⟶w ())) R) var⟶s)
-} 

SI-wred-lemma : ∀ {X} (Y Z : Λ (↑ X)) → app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y 
                             → Y ⟶w Z → app (Λ→i (Z [ SI ]ₒ)) (var o) ⟶s Z
SI-wred-lemma Y Z R Y→Z 
  with ⟶s\⟶w R (appL⟶w (map⟶w i (bind⟶w (io var SI) Y→Z)))
... | u ,, εʳ , Y→u = ⟶s!⟶s Y→u (red⟶s Y→Z refl⟶s)
... | u ,, axʳ W , Y→u 
  with ⟶w-unique-tgt Y→Z W 
... | refl = Y→u

SI-wred*-lemma : ∀ {X} (Y Z : Λ (↑ X)) → app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y 
                        → (_⟶w_ ⋆) Y Z → app (Λ→i (Z [ SI ]ₒ)) (var o) ⟶s Z
SI-wred*-lemma {X} Y Z R ε⋆ = R
SI-wred*-lemma {X} Y Z R (w ,⋆ W) = SI-wred*-lemma _ Z (SI-wred-lemma Y _ R w) W

SI-sred-lemma : ∀ {X} (Y : Λ (↑ X)) → app (app SI (Λ→i (Y [ SI ]ₒ))) (var o) ⟶s app (var o) Y 
                                    → app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y 
SI-sred-lemma {X} Y (red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (red⟶s (appL⟶w (red⟶w ())) R)))
SI-sred-lemma {X} Y (red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (app⟶s (red⟶s (red⟶w ()) R) R₁)))
SI-sred-lemma {X} Y (red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (app⟶s var⟶s R₁))) = e ≡!⟶s R₁
  where e = cong2 app (~ (bind-lift2 (var o) (Λ→ i (Y [ io var SI ])))) refl
SI-sred-lemma {X} Y (red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (appL⟶w (red⟶w ())) R))
SI-sred-lemma {X} Y (red⟶s (appL⟶w (red⟶w (redex refl))) (app⟶s (red⟶s (red⟶w ()) R) R₁))
SI-sred-lemma {X} Y (red⟶s (appL⟶w (appL⟶w (red⟶w ()))) R)
SI-sred-lemma {X} Y (app⟶s (red⟶s (red⟶w (redex refl)) (red⟶s (red⟶w ()) R1)) R2)
SI-sred-lemma {X} Y (app⟶s (red⟶s (appL⟶w (red⟶w ())) R1) R2)

SI-Lemma : ∀ {X} (Y Z : Λ (↑ X)) → Y ⟶s Z → Y ⟶s app (var o) Z → ¬ (app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y)
SI-Lemma (var x) Z Y→Z (red⟶s (red⟶w ()) Y→xZ) R
SI-Lemma (abs Y) Z Y→Z (red⟶s (red⟶w ()) Y→xZ) R
SI-Lemma (app Y1 Y2) Z (red⟶s {s = s} w1 Y1Y2→Z) (red⟶s w2 Y1Y2→xZ) R 
  with ⟶w-unique-tgt w1 w2 
... | refl = SI-Lemma s Z Y1Y2→Z Y1Y2→xZ (SI-wred-lemma (app Y1 Y2) s R w1) 
SI-Lemma (app Y1 Y2) Z (red⟶s (red⟶w (redex refl)) s→Z) (app⟶s (red⟶s (red⟶w ()) Y1→x) Y2→Z) R
SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} (red⟶w ())) s→Z) (app⟶s var⟶s Y2→Z) R
SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} w1) s→Z) (app⟶s (red⟶s w2 Y1→x) Y2→Z) R 
  with ⟶w-unique-tgt w1 w2 
... | refl = SI-Lemma (app t Y2) Z s→Z (app⟶s Y1→x Y2→Z) 
                      (SI-wred-lemma (app Y1 Y2) (app t Y2) R (appL⟶w w1))
-- This is the intersting case: 
-- SI-Lemma (app Y1 Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) Y1Y2→xZ R = {!  !}
SI-Lemma (app (var x) Y2) (app Z1 Z2) (app⟶s (red⟶s (red⟶w ()) Y1→Z1) Y2→Z2) Y1Y2→xZ R
SI-Lemma (app (var (i x)) Y2) (app Z1 Z2) (app⟶s var⟶s Y2→Z2) (red⟶s (appL⟶w (red⟶w ())) Y1Y2→xZ) R
SI-Lemma (app (var (i x)) Y2) (app Z1 Z2) (app⟶s var⟶s Y2→Z2) (app⟶s (red⟶s (red⟶w ()) Y1Y2→xZ) Y1Y2→xZ₁) R
SI-Lemma (app (var o) Y2) (app Z1 Z2) (app⟶s var⟶s Y2→Z2) (red⟶s (appL⟶w (red⟶w ())) Y1Y2→xZ) R
SI-Lemma (app (var o) Y2) (app Z1 Z2) (app⟶s var⟶s Y2→Z2) (app⟶s x→x Y2→xZ2) R 
  with R 
... | red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (red⟶s (appL⟶w (red⟶w ())) c))
... | red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (app⟶s (red⟶s (red⟶w ()) c) c₁))
-- ... | red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (app⟶s var⟶s c)) = {!  !}
... | red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) (app⟶s var⟶s c)) = 
  SI-Lemma Y2 Z2 Y2→Z2 Y2→xZ2 (transp (λ z → z ⟶s Y2) e c)
     where e = cong2 app (bind-lift2 (var o) (Λ→ i (Y2 [ io var SI ]))) refl
... | red⟶s (appL⟶w (red⟶w (redex refl))) (red⟶s (appL⟶w (red⟶w ())) c)
... | red⟶s (appL⟶w (red⟶w (redex refl))) (app⟶s (red⟶s (red⟶w ()) c) c₁)
... | red⟶s (appL⟶w (appL⟶w (red⟶w ()))) c
... | app⟶s c (red⟶s (red⟶w ()) c₁)
SI-Lemma (app (var o) Y2) (app .(var o) Z2) (app⟶s var⟶s Y2→Z2) (app⟶s x→x (red⟶s (red⟶w ()) Y2→xZ2)) R | app⟶s c var⟶s
-- SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) (app⟶s Y1Y3→Z1 Y2→Z2) Y1Y3Y2→xZ R = {!   !}
SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) (app⟶s Y1Y3→Z1 Y2→Z2) (red⟶s {s = Y4} (appL⟶w {t = t} W) Y4→xZ) R 
  with SI-wred-lemma (app (app Y1 Y3) Y2) (app t Y2) R (appL⟶w W) 
... | R' = {!  !}
  -- with ⟶s\⟶w Y1Y3→Z1 W 
  -- ... | (u ,, Z1→u , t→u) = {!  !}
  -- SI-Lemma (app t Y2) (app Z1 Z2) Q Y4→xZ R'
  --         Q : _ 
  --         Q with ⟶s\⟶w Y1Y3→Z1 W 
  --         ... | u ,, axʳ x , t→u = {! !}
  --         ... | u ,, εʳ , t→u = app⟶s t→u Y2→Z2
SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) Y1Y3Y2→xZ2@(app⟶s Y1Y3→Z1 Y2→Z2) (app⟶s Y1Y3→x Y2→Z1Z2) R 
  with ⟶s\⟶s Y1Y3→x Y1Y3→Z1 
... | u ,, red⟶s (red⟶w ()) x→u , Z1→u
... | u ,, var⟶s , Z1→u 
  with SI-wred*-lemma (app (app Y1 Y3) Y2) (app (var o) Y2) R (appL⟶w⋆ (var→w Y1Y3→x)) 
... | c =  SI-Lemma Y2 Z2 Y2→Z2 (⟶s!⟶s Y2→Z1Z2 (app⟶s Z1→u refl⟶s)) (SI-sred-lemma Y2 c)
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s (red⟶s (red⟶w ()) Y1→Z1) Y2→Z2) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (red⟶s (appL⟶w (red⟶w ())) Y1Y2→xZ) R
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (app⟶s (red⟶s (red⟶w ()) Y1Y2→xZ) Y1Y2→xZ₁) R
SI-Lemma (app (abs Y1) Y2) (app Z0 Z2) (app⟶s (abs⟶s {r2 = Z1} Y1→Z1) Y2→Z2) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R 
  -- = SI-Lemma (Y1 [ Y2 ]ₒ)  (Z1 [ Z2 ]ₒ) {!   !} (⟶s!⟶s Y1Y2→xZ (app⟶s var⟶s (red⟶s (red⟶w (redex refl)) refl⟶s)) ) {!  !}
  = SI-Lemma (Y1 [ Y2 ]ₒ)  (app Z0 Z2) {!  !} Y1Y2→xZ {!  !}

{-
SI-Lemma0 : ∀ {X} (Y Z : Λ (↑ X)) → Y ⟶s Z → app (var o) Y ⟶s Z → ¬ (app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y)
SI-Lemma0 (var x) Z (red⟶s (red⟶w ()) Y→Z) xY→Z R
SI-Lemma0 (var x) Z var⟶s (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma0 (abs Y) Z (red⟶s (red⟶w ()) Y→Z) xY→Z R
SI-Lemma0 (abs Y) Z (abs⟶s Y→Z) (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (red⟶s (appL⟶w (red⟶w ())) xY1Y2→Z1Z2) R
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (app⟶s (red⟶s (red⟶w ()) xY1Y2→Z1Z2) xY1Y2→Z1Z3) R
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (app⟶s var⟶s xY1Y2→Z1Z3) R
  = SI-Lemma0 Y2 Z2 Y2→Z2 {!  !} {!  !} -- these are provable independently, but need to update Z2...
-- SI-Lemma0 (app Y1 Y2) Z (red⟶s {s = s} W Y1Y2→Z) xY1Y2→Z R = {!  !}
-- strategy: again use Y2 
SI-Lemma0 (app Y1 Y2) Z (red⟶s {s = s} W Y1Y2→Z) (red⟶s (appL⟶w (red⟶w ())) xY1Y2→Z) R
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = s} W Y1Y2→Z) (app⟶s (red⟶s (red⟶w ()) xY1Y2→Z) xY1Y2→Z₁) R
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s Y1Y2→Z2) (app⟶s R1 (red⟶s (red⟶w ()) R2))
  -- Below, should Use that o ∉ Y1, per R1 
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (red⟶s W Y1Y2→Z2)) (app⟶s R1 var⟶s) 
  with ⟶w-unique-tgt Y1Y2→Y3 W | W 
SI-Lemma0 (app Y1 .(var o)) (app .(var o) Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (red⟶s W Y1Y2→Z2)) (app⟶s (red⟶s (red⟶w (redex refl)) R1) var⟶s) | refl | red⟶w (redex {s = r} refl) = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 (app⟶s var⟶s Y1Y2→Z2) {! r  !}
SI-Lemma0 (app Y1 .(var o)) (app .(var o) Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (red⟶s W Y1Y2→Z2)) (app⟶s (red⟶s (appL⟶w (red⟶w ())) R1) var⟶s) | refl | red⟶w (redex refl)
... | refl | appL⟶w {t = t} w = SI-Lemma0 (app t (var o)) (app (var o) Z2) Y3→xZ2 (app⟶s var⟶s Y1Y2→Z2) (app⟶s {! !} var⟶s) -- Y1 is still closed
-- ... | refl | w = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 (app⟶s var⟶s Y1Y2→Z2) {!  !} -- Y1 is closed here 
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (app⟶s Y1Y2→Z2 (red⟶s (red⟶w ()) Y1Y2→Z3))) (app⟶s R1 var⟶s)
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (app⟶s Y1Y2→Z2 var⟶s)) (app⟶s R1 var⟶s) = {! !}  -- Y1 still closed 
SI-Lemma0 (app Y1 Y2) (app Z1 Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s Y1Y2→Z2) (red⟶s {s = t} (appL⟶w W) R) = {! !}
--   with ⟶w-unique-tgt W (appL⟶w (map⟶w i (bind⟶w (io var SI) Y1Y2→Y3)))
-- SI-Lemma0 (app Y1 Y2) (app .(var o) Z2) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (red⟶s Y1Y2→s Y1Y2→Z2)) (red⟶s W R) | refl 
--   with ⟶w-unique-tgt Y1Y2→Y3 Y1Y2→s 
-- ... | refl = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 (app⟶s var⟶s Y1Y2→Z2) (⟶s!⟶s R (red⟶s Y1Y2→Y3 refl⟶s))
-- SI-Lemma0 (app Y1 Y2) (app .(var o) (app Z1 Z2)) (red⟶s {s = Y3} Y1Y2→Y3 Y3→xZ2) (app⟶s var⟶s (app⟶s Y1Y2→Z2 Y1Y2→Z3)) (red⟶s W R) | refl 
--   = SI-Lemma0 Y3 (app Z1 Z2) {!  !} {!   !} (⟶s!⟶s R (red⟶s Y1Y2→Y3 refl⟶s)) 
-- ... | refl = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 {!  !} (⟶s!⟶s R (red⟶s Y1Y2→Y3 refl⟶s))
--   with ⟶s\⟶w Y1Y2→Z2 Y1Y2→Y3 
-- ... | u ,, εʳ , Z2→u = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 (app⟶s var⟶s Z2→u) (⟶s!⟶s R (red⟶s Y1Y2→Y3 refl⟶s))
-- ... | u ,, axʳ W' , Z2→u = SI-Lemma0 Y3 (app (var o) u) {!  !} (app⟶s var⟶s Z2→u) (⟶s!⟶s R (red⟶s Y1Y2→Y3 refl⟶s))
-- = SI-Lemma0 Y3 (app (var o) Z2) Y3→xZ2 {!  !} {!  !}
-}

{-
SI-Lemma0 Y Z Y→Z (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma0 Y Z Y→Z (app⟶s (red⟶s (red⟶w ()) xY→Z) xY→Z₁) R
SI-Lemma0 (var x) (app (var o) Z) (red⟶s (red⟶w ()) Y→xZ) (app⟶s var⟶s xY→Z) R
SI-Lemma0 (abs Y0) (app (var o) Z) (red⟶s (red⟶w ()) Y→xZ) (app⟶s var⟶s xY→Z) R
SI-Lemma0 (app Y1 Y2) (app (var o) Z) (app⟶s Y1→x Y2→Z) (app⟶s var⟶s Y1Y2→Z) R 
  = SI-Lemma0 Y2 {!  !} {!  !} {!  !} {!  !}
-- SI-Lemma0 (app Y1 Y2) (app (var o) Z) (app⟶s var⟶s Y2→Z) (app⟶s var⟶s Y1Y2→Z) R 
--   = SI-Lemma0 Y2 Z Y2→Z Y1Y2→Z (xY[SI]→Y Y2 R)
-- SI-Lemma0 (app Y1 Y2) (app (var o) Z) (app⟶s (red⟶s {s = s} x Y1→x) Y2→Z) (app⟶s var⟶s Y1Y2→Z) R 
--   = {!   !}

SI-Lemma0 (app Y1 Y2) (app (var o) Z) (red⟶s {s = s} (red⟶w (redex {s = r} refl)) Y→xZ) (app⟶s var⟶s xY→Z) R = {!  !}
SI-Lemma0 (app Y1 Y2) (app (var o) Z) (red⟶s {s = s} (appL⟶w W) Y→xZ) (app⟶s var⟶s xY→Z) R = {! !}
-}
{-
SI-Lemma1-aux : ∀ {X} (Y Z : Λ (↑ X)) → Y ⟶s Z → app (var o) Y ⟶s Z
                  → ¬ (app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Z)
SI-Lemma1-aux (var x) (var .x) var⟶s (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma1-aux (abs r1) (abs r2) (abs⟶s Y→Z) (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma1-aux (app s1 s2) (app t1 t2) (app⟶s Y→Z Y→Z₁) (red⟶s (appL⟶w (red⟶w ())) xY→Z) R
SI-Lemma1-aux (app s1 s2) (app t1 t2) (app⟶s Y→Z Y→Z₁) (app⟶s (red⟶s (red⟶w ()) xY→Z) xY→Z₁) R
SI-Lemma1-aux (app X₀ Y₀) (app .(var o) Y₁) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s X₀Y₀→Y₁) (app⟶s R (red⟶s (red⟶w ()) R₁))
SI-Lemma1-aux (app X₀ Y₀) (app .(var o) Y₁) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s X₀Y₀→Y₁) R
 = {!   !}
{- 
X0 →s x implies X0 →w x so R must start with X0 →w x, then delta reduces to that too.
-}
-- SI-Lemma1-aux (app X₀ Y₀) (app .(var o) .(var o)) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s X₀Y₀→Y₁) (app⟶s R var⟶s)
--   = {! R   !} -- this case is impossible; if X0 --> x, then X0Y0 -/-> x
-- SI-Lemma1-aux (app X₀ Y₀) (app .(var o) Y₁) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s X₀Y₀→Y₁) (red⟶s {s = s} W R)
-- = {!   !}
-- SI-Lemma1-aux (app X₀ Y₀) (app .(var o) Y₁) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s (red⟶s x X₀Y₀→Y₁)) R = {!   !}
-- SI-Lemma1-aux (app X₀ Y₀) (app .(var o) .(app _ _)) (app⟶s X₀→x Y₀→Y₁) (app⟶s var⟶s (app⟶s X₀Y₀→Y₁ X₀Y₀→Y₂)) R = {!   !}
  -- = SI-Lemma1-aux Y₀ Y₁ Y₀→Y₁ {!   !} {!   !}
SI-Lemma1-aux Y₀ Z (red⟶s {s = Y₁} Y₀→Y₁ Y₁→Z) (red⟶s (appL⟶w (red⟶w ())) xY₀→Z) R
SI-Lemma1-aux Y₀ .(app _ _) (red⟶s {s = Y₁} Y₀→Y₁ Y₁→Z) (app⟶s (red⟶s (red⟶w ()) xY₀→Z) xY₀→Z₁) R
SI-Lemma1-aux Y₀ (app (var o) Y₁) (red⟶s {s = Z} Y₀→Z Z→xY₁) (app⟶s var⟶s Y₀→Y₁) R
  with ⟶s\⟶w Y₀→Y₁ Y₀→Z
... | c = {!   !}
-- ... | u ,, axʳ Y2→u , Y1→u = SI-Lemma1-aux Y₁ (app (var o) u) (⟶s!⟶s Y₁→xY₂ (app⟶s var⟶s (red⟶s Y2→u refl⟶s ) ) ) (app⟶s var⟶s Y1→u ) {!   !}
-- ... | .Y₂ ,, εʳ , Y1→u = SI-Lemma1-aux Y₁ (app (var o) Y₂) Y₁→xY₂ (app⟶s var⟶s Y1→u ) {!   !}
  -- = SI-Lemma1-aux Y₁ (app (var o) Y₂) Y₁→xY₂ (app⟶s var⟶s {!   !} ) {!   !}

-- We first prove that there is no fpc Y such that Yδ ⟶β Y
SI-Lemma1 : ∀ {X} (Y : Λ (↑ X)) → Y ∈ FPCx → ¬ (app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y)
SI-Lemma1 Y Y∈FPCx R with Y∈FPCx
... | (Z ,, Y→βZ , xY→βZ) 
  with ⟶β⋆⊆⟶s  Y→βZ 
     | ⟶β⋆⊆⟶s xY→βZ
... | Y→sZ | xY→sZ = SI-Lemma1-aux Y Z Y→sZ xY→sZ (⟶s!⟶s R Y→sZ)
-}
