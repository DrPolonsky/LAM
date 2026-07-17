open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Relations.ClosureOperators
open import Reduction
open import Conversion

module FPC.FixedPointContexts where

-- The Owl Combinator δ = λyx.x(yx)
SI : ∀ {X} → Λ X
SI = abs (abs (app (var o) (app (var (i o)) (var o) ) ) )

-- A fixed point combinator is a fixed point of SI 
FPC : ∀ {X} → 𝓟 (Λ X) 
FPC t = t =β app SI t 

-- A fixed point context is a term t ∈ Λ(X,vₒ) s.t. t =β vₒt
FPCx : ∀ {X} → 𝓟 (Λ (↑ X))
FPCx t = t =β app (var o) t

-- Alternatively, it is aterm t s.t. t ⟶β⋆ u and t ⟶β⋆ xu for some u
FPCx₂ : ∀ {X} → 𝓟 (Λ (↑ X))
FPCx₂ {X} t = Σ[ u ∈ Λ (↑ X) ] (t ⟶β⋆ u × t ⟶β⋆ app (var o) u)

-- These definitions are equivalent 
FPCx⊆FPCx₂ : ∀ {X} → FPCx {X} ⊆ FPCx₂ 
FPCx⊆FPCx₂ t (u ,, t→u , xt→u)
  with ⟶β⋆⊆⟶s xt→u 
... | red⟶s (appL⟶w (red⟶w ())) c
... | app⟶s (red⟶s (red⟶w ()) R+) c
... | app⟶s {t2 = v} var⟶s t→v = v ,, ⟶s⊆⟶β⋆ _ _ t→v , t→u

FPCx₂⊆FPCx : ∀ {X} → FPCx₂ {X} ⊆ FPCx
FPCx₂⊆FPCx t (u ,, t→u , t→xu) = app (var o) u ,, t→xu , appR⟶β⋆ t→u (var o)

module WeakHeadReductions where 

  WHNF : ∀ {X} → Λ X → Set 
  WHNF t = ∀ u → ¬ (t ⟶w u)

  var⊆WHNF : ∀ {X} {x : X} → var x ∈ WHNF 
  var⊆WHNF u (red⟶w ())

  abs⊆WHNF : ∀ {X} {r : Λ (↑ X)} → abs r ∈ WHNF 
  abs⊆WHNF u (red⟶w ())

  WHNF↓s⊆WHNF : ∀ {X} {s t : Λ X} → s ⟶s t → s ∈ WHNF → t ∈ WHNF 
  WHNF↓s⊆WHNF s→t s∈W u (red⟶w (redex e)) with s→t 
  ... | red⟶s {s = s'} s→s' s'→rdx = s∈W s' s→s'
  ... | app⟶s (red⟶s {s = s'} w _) _ = s∈W _ (appL⟶w w)
  ... | app⟶s (abs⟶s c) c₁ = s∈W _ (red⟶w (redex refl))
  WHNF↓s⊆WHNF (red⟶s w s→t) s∈W u (appL⟶w t→u) = s∈W _ w
  WHNF↓s⊆WHNF (app⟶s s→t s→t₁) s∈W u (appL⟶w t→u) 
    = WHNF↓s⊆WHNF s→t (λ u s1→u → s∈W _ (appL⟶w s1→u)) _ t→u

  ⟶w-unique-tgt : ∀ {X} {s t1 t2 : Λ X} → s ⟶w t1 → s ⟶w t2 → t1 ≡ t2
  ⟶w-unique-tgt (red⟶w (redex e1)) (red⟶w (redex e2)) = e1 ~! e2
  ⟶w-unique-tgt (red⟶w (redex e)) (appL⟶w (red⟶w ()))
  ⟶w-unique-tgt (appL⟶w (red⟶w ())) (red⟶w (redex e))
  ⟶w-unique-tgt (appL⟶w {r = r} s→t1) (appL⟶w s→t2)
    = cong (λ z → app z r) (⟶w-unique-tgt s→t1 s→t2)

  ⟶w⋆-TP : ∀ {X} {s t u : Λ X} → s ⟶w⋆ t → s ⟶w⋆ u → t ⟶w⋆ u ⊔ u ⟶w⋆ t
  ⟶w⋆-TP ε⋆ s→u = in1 s→u
  ⟶w⋆-TP s→t@(s→s' ,⋆ s'→t) ε⋆ = in2 s→t
  ⟶w⋆-TP {u = u} (s→s' ,⋆ s'→t) (s→s'' ,⋆ s''→u) 
    = ⟶w⋆-TP s'→t (transp (λ x → x ⟶w⋆ u) (⟶w-unique-tgt s→s'' s→s') s''→u)

  open import ARS.Properties
  open import ARS.Implications
  open Hierarchy-Implications

  ⟶w-CR : ∀ {X} → _⟶w_ {X} isCR
  ⟶w-CR s s→t s→u with ⟶w⋆-TP s→t s→u
  ... | in1 b→c = _ ,, b→c , ε⋆
  ... | in2 c→b = _ ,, ε⋆ , c→b

  WHNF-unique : ∀ {X} {s t1 t2 : Λ X} → s ⟶w⋆ t1 → s ⟶w⋆ t2 → t1 ∈ WHNF → t2 ∈ WHNF → t1 ≡ t2 
  WHNF-unique {X} {s} {t1} {t2} s→t1 s→t2 t1∈W t2∈W
    with NP→UN {R = _⟶w_ {X}} (MP→NP (CR→MP (⟶w-CR _)))
  ... | un = un {t1} {t2} (t1∈W _) (t2∈W _) s→t1 s→t2

  ⟶s\⟶w : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⟶w t2 → Σ[ u ∈ Λ X ] ((_⟶w_ ʳ) t1 u × t2 ⟶s u)
  ⟶s\⟶w var⟶s (red⟶w ())
  ⟶s\⟶w (abs⟶s s→t1) (red⟶w ())
  ⟶s\⟶w (red⟶s {t = t1} W s→t1) s→t2 rewrite ⟶w-unique-tgt s→t2 W = t1 ,, εʳ , s→t1
  ⟶s\⟶w (app⟶s {s2 = s2} {t1} {t2} (red⟶s (red⟶w ()) s→t1) s→t3) (red⟶w (redex {r} {s} e))
  ⟶s\⟶w (app⟶s {s2 = .(abs _)} {t1} {t2} (abs⟶s {r2 = r2} s→t1) s→t3) (red⟶w (redex {r} {s} e))
    = r2 [ t2 ]ₒ ,, axʳ (red⟶w (redex refl) ) , transp _ e (⟶s[⟶s]ₒ s→t1 s→t3)
  ⟶s\⟶w (app⟶s {t2 = t2} s→t1 s→t3) (appL⟶w s→t2) with ⟶s\⟶w s→t1 s→t2
  ... | u ,, axʳ s2→u , t→u = app u t2 ,, axʳ (appL⟶w s2→u ) , app⟶s t→u s→t3
  ... | u ,, εʳ , t→u = app u t2 ,, εʳ , (app⟶s t→u s→t3)

  ⟶s\⟶w⋆ : ∀ {X} {s t1 t2 : Λ X} → s ⟶s t1 → s ⟶w⋆ t2 → Σ[ u ∈ Λ X ] (t1 ⟶w⋆ u × t2 ⟶s u)
  ⟶s\⟶w⋆ {s = s} s→t1 ε⋆ = _ ,, ε⋆ , s→t1
  ⟶s\⟶w⋆ {s = s} s→t1 (s→y ,⋆ y→t2) 
    with ⟶s\⟶w s→t1 s→y 
  ... | v ,, εʳ , y→v = ⟶s\⟶w⋆ y→v y→t2
  ... | v ,, axʳ t1→v , y→v 
    with ⟶s\⟶w⋆ y→v y→t2
  ... | u ,, v→u , t2→u = u ,, (t1→v ,⋆ v→u) , t2→u

  ⟶s-WHNF : ∀ {X} {s t : Λ X} → s ⟶s t → t ∈ WHNF → Σ[ w ∈ Λ X ] (s ⟶w⋆ w × (w ∈ WHNF × w ⟶s t))
  ⟶s-WHNF (red⟶s s→s' s'→t) t∈W 
    with ⟶s-WHNF s'→t t∈W 
  ... | (w ,, s'→w , (w∈W , w→t)) = w ,, (s→s' ,⋆ s'→w) , (w∈W , w→t)
  ⟶s-WHNF (var⟶s {x}) t∈W = var x ,, ε⋆ , (var⊆WHNF , var⟶s)
  ⟶s-WHNF (abs⟶s {r1} {r2} s→t) t∈W = abs r1 ,, ε⋆ , (abs⊆WHNF , abs⟶s s→t)
  ⟶s-WHNF (app⟶s {s1} {s2} {t1} {t2} s1→s2 t1→t2) t∈W
    with ⟶s-WHNF s1→s2 (λ u s2→u → t∈W _ (appL⟶w s2→u))
  ... | (w ,, s1→w , (w∈W , w→s2)) = app w t1 ,, appL⟶w⋆ s1→w , (wt1∈W , app⟶s w→s2 t1→t2)
    where red→WHNF : ∀ {y} → abs y ⟶s s2 → ⊥ 
          red→WHNF (red⟶s (red⟶w ()) R)
          red→WHNF (abs⟶s R) = t∈W _ (red⟶w (redex refl))
          wt1∈W : app w t1 ∈ WHNF
          wt1∈W u (appL⟶w wt1→u) = w∈W _ wt1→u
          wt1∈W u (red⟶w (redex refl)) = red→WHNF w→s2

  SI⟶w : ∀ {X} {t : Λ X} → app (Λ→i (app SI t)) (var o) ⟶w⋆ app (var o) (app (Λ→i t) (var o))
  SI⟶w = appL⟶w (red⟶w (redex refl)) ,⋆ (red⟶w (redex e) ,⋆ ε⋆)
    where e = cong2 app refl (cong2 app (bind-lift2 (var o) _) refl)

  SI∈NF : ∀ {X} → SI {X} ∈ NF 
  SI∈NF N (abs⟶β (abs⟶β (appL⟶β (red⟶β ()))))
  SI∈NF N (abs⟶β (abs⟶β (appR⟶β (appL⟶β (red⟶β ())))))
  SI∈NF N (abs⟶β (abs⟶β (appR⟶β (appR⟶β (red⟶β ())))))


open WeakHeadReductions

FPC→FPCx : ∀ {X} (Y Z : Λ X) → Y ⟶β⋆ Z → app SI Y ⟶β⋆ Z → Σ[ Z ∈ Λ (↑ X) ] (Y ⟶w⋆ abs Z × Z ∈ FPCx)
FPC→FPCx Y Z Y→Zβ SIY→Zβ
  with ⟶β⋆⊆⟶s Y→Zβ | ⟶β⋆⊆⟶s SIY→Zβ 
... | Y→Z | app⟶s {s2 = Z1} {t2 = Z2} SI→Z1 SI→Z2 = f
  where f : _ 
        f with ⟶s\⟶s SI→Z2 Y→Z 
        ... | (u ,, Z1→u , Z1Z2→u) with ⟶sNF SI→Z1 SI∈NF 
        ... | refl 
          with ⟶s-WHNF (⟶s!⟶s Y→Z (red⟶s (red⟶w (redex refl)) refl⟶s)) abs⊆WHNF
        ... | v ,, Y→v , (v∈WHNF , red⟶s x v→xZ2x) = ∅ (v∈WHNF _ x)
        ... | v ,, Y→v , (v∈WHNF , abs⟶s {r1 = r1} v→xZ2x) 
          with ⟶s\⟶w⋆ (app⟶s (map⟶s i (⟶s!⟶s Y→Z Z1Z2→u)) var⟶s) 
                      (appL⟶w⋆ (map⟶w⋆ i Y→v) ⋆!⋆ (red⟶w (redex (~ eq)) ,⋆ ε⋆))
                        where eq = bind-unit0 r1 ~! bind-nat₁ (io𝓟 _ (λ x → refl) refl) r1
        ... | (w ,, ux→w , r1→w) = r1 ,, Y→v , (FPCx₂⊆FPCx _ v∈FPCx)
          where Z2x→w = ⟶s!⟶s (app⟶s (map⟶s i Z1→u) var⟶s) (⟶w⋆!⟶s ux→w refl⟶s)
                r1→xw = ⟶s⊆⟶β⋆ r1 _ (⟶s!⟶s v→xZ2x (app⟶s var⟶s Z2x→w)) 
                v∈FPCx = w ,, ⟶s⊆⟶β⋆ r1 w r1→w , r1→xw
... | Y→Z | red⟶s (red⟶w (redex refl)) (red⟶s (red⟶w ()) s→Z)
... | Y→Z | red⟶s (appL⟶w (red⟶w ())) s→Z
... | Y→Z | red⟶s (red⟶w (redex refl)) (abs⟶s {r2 = r2} s→Z) 
  with ⟶sabs Y→Z
... | (r ,, Y→λr , r→r2) 
  with s→Z 
... | red⟶s (appL⟶w (red⟶w ())) c
... | app⟶s (red⟶s (red⟶w ()) c) c₁
... | app⟶s {t2 = t2} var⟶s Yx→t2 
  with ⟶s\⟶w⋆ Yx→t2 (appL⟶w⋆ (map⟶w⋆ i Y→λr) ⋆!⋆ (red⟶w (redex refl) ,⋆ ε⋆))
... | u ,, t2→u , q→u 
      = r ,, Y→λr , r∈FPCx 
  where xt2→xu : app (var o) t2 ⟶s app (var o) u
        xt2→xu = app⟶s var⟶s (⟶β⋆⊆⟶s (⊆⋆ (λ _ _ → ⟶w⊆⟶β) t2 u t2→u))
        r→xu : r ⟶s app (var o) u
        r→xu = ⟶s!⟶s r→r2 xt2→xu 
        eq = bind-unit0 r ~! bind-nat₁ (io𝓟 _ (λ x → refl) refl) r
        r→q = eq ≡!⟶s refl⟶s
        xr→xu = app⟶s var⟶s (⟶s!⟶s r→q q→u)
        r∈FPCx : r ∈ FPCx
        r∈FPCx = app (var o) u ,, ⟶s⊆⟶β⋆ r (app (var o) u) r→xu , ⟶s⊆⟶β⋆ _ _ xr→xu
 
FPC→FPCx₂ : ∀ {X} (Y : Λ X) → Y ∈ FPC → Σ[ Z ∈ Λ (↑ X) ] (Y ⟶w⋆ abs Z × Z ∈ FPCx₂)
FPC→FPCx₂ Y (t ,, Y→t , δY→t) 
  with FPC→FPCx Y t Y→t δY→t
... | (Z ,, Y→Z , Z∈FPCx) = Z ,, Y→Z , FPCx⊆FPCx₂ Z Z∈FPCx

FPC-Case4-0 : ∀ {X} (Y : Λ X) → Y ∈ FPC → app Y SI ⟶β⋆ Y → 
                Σ[ Z ∈ Λ (↑ X) ] (Z ∈ FPCx × app (Λ→i (Z [ SI ]ₒ)) (var o) ⟶s Z)
FPC-Case4-0 Y Y∈FPC YSI→Y 
  with FPC→FPCx₂ Y Y∈FPC
... | (Z ,, Y→λZ , Z∈FPCx@(Z1 ,, Z→βZ1 , Z→βxZ1))
  with ⟶s-WHNF (⟶β⋆⊆⟶s Z→βxZ1) (λ { u (appL⟶w (red⟶w ()))})
... | var x ,, Z→wxZ1 , (xZ1∈WFPC , red⟶s (red⟶w ()) Z0→sxZ1)
... | abs Z0 ,, Z→wxZ1 , (xZ1∈WFPC , red⟶s (red⟶w ()) Z0→sxZ1)
... | app Z0 Z2 ,, Z→wxZ1 , (xZ1∈WFPC , red⟶s w Z0→sxZ1) = ∅ (xZ1∈WFPC _ w)
... | app Z0 Z2 ,, Z→wxZ1 , (xZ1∈WFPC , app⟶s (red⟶s w Z0→sxZ1) Z0→sxZ2) = ∅ (xZ1∈WFPC _ (appL⟶w w))
... | app (.var o) Z2 ,, Z→wxZ1 , (xZ1∈WFPC , app⟶s var⟶s Z0→sxZ2) 
  with ⟶s\⟶w⋆ S W where 
    Yδ→δZ2[δ] : app Y SI ⟶w⋆ app SI (Z2 [ SI ]ₒ)
    Yδ→δZ2[δ] = appL⟶w⋆ Y→λZ ⋆!⋆ (red⟶w (redex refl) ,⋆ bind⟶w⋆ (io var SI) Z→wxZ1)
    W : app (Λ→i (app Y SI)) (var o) ⟶w⋆ app (var o) (app (Λ→i (Z2 [ SI ]ₒ)) (var o))
    W = appL⟶w⋆ (map⟶w⋆ i Yδ→δZ2[δ]) ⋆!⋆ SI⟶w
    e = bind-nat₁ (io𝓟 _ (λ x → refl) refl ) Z ~! bind-unit0 Z
    S1 = app⟶s (map⟶s i (⟶β⋆⊆⟶s YSI→Y)) var⟶s
    S2 = ⟶w⋆!⟶s (appL⟶w⋆ (map⟶w⋆ i Y→λZ) ⋆!⋆ (red⟶w (redex e) ,⋆ Z→wxZ1)) refl⟶s
    S : app (Λ→i (app Y SI)) (var o) ⟶s app (var o) Z2
    S = ⟶s!⟶s S1 S2
... | .(app (var o) Z2) ,, ε⋆ , red⟶s (appL⟶w (red⟶w ())) xZ2x→xu
... | .(app (var o) Z2) ,, ε⋆ , app⟶s (red⟶s (red⟶w ()) xZ2x→xu) xZ2x→xu₁
... | u ,, (appL⟶w (red⟶w ()) ,⋆ u→xu) , xZ2x→xu
... | .(app (var o) Z2) ,, ε⋆ , app⟶s var⟶s R 
  with ⟶s\⟶w⋆ (⟶β⋆⊆⟶s Z→βZ1) Z→wxZ1
... | u ,, Z1→u , xZ2→u = Z2 ,, u∈FPCx , R
  where u∈FPCx = u ,, (⟶s⊆⟶β⋆ _ _ Z0→sxZ2 ⋆!⋆ ⊆⋆ (λ _ _ → ⟶w⊆⟶β) Z1 u Z1→u) , ⟶s⊆⟶β⋆ _ _ xZ2→u


{-
xY[SI]→Y : ∀ {X} (Y : Λ (↑ X)) → app (Λ→i (app (var o) Y [ SI ]ₒ)) (var o) ⟶s app (var o) Y 
                               → app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y 
xY[SI]→Y Y (red⟶s {s = Z} (appL⟶w {t = t} (red⟶w (redex refl))) (red⟶s (red⟶w (redex refl)) R)) = {!   !}
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
SI-Lemma (app Y1 Y2) Z (red⟶s {s = s1} w1 Y1Y2→Z) (red⟶s {s = s2} w2 Y1Y2→xZ) R rewrite ⟶w-unique-tgt w1 w2 = 
  -- SI-Lemma s1 Z Y1Y2→Z (transp (λ x → x ⟶s app (var o) Z) (⟶w-unique-tgt w2 w1) Y1Y2→xZ) (SI-wred-lemma (app Y1 Y2) s1 R w1)
  SI-Lemma s2 Z Y1Y2→Z Y1Y2→xZ (SI-wred-lemma (app Y1 Y2) s2 R w2) 
-- with ⟶w-unique-tgt w1 w2 
-- ... | refl = SI-Lemma s Z Y1Y2→Z Y1Y2→xZ (SI-wred-lemma (app Y1 Y2) s R w1) 
SI-Lemma (app Y1 Y2) Z (red⟶s (red⟶w (redex refl)) s→Z) (app⟶s (red⟶s (red⟶w ()) Y1→x) Y2→Z) R
SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} (red⟶w ())) s→Z) (app⟶s var⟶s Y2→Z) R
-- SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} w1) s→Z) (app⟶s (red⟶s w2 Y1→x) Y2→Z) R 
SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} w1) s→Z) (app⟶s (red⟶s w2 Y1→x) Y2→Z) R 
  -- the following might be better, after red⟶s-appL⟶w  normalization...
  -- = SI-Lemma (app Y1 Y2) Z (red⟶s (appL⟶w {t = t} w1) s→Z) (red⟶s (appL⟶w w2) (app⟶s Y1→x Y2→Z)) R 
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
SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) (app⟶s (red⟶s {s = s} V Y1Y3→Z1) Y2→Z2) (red⟶s {s = Y4} (appL⟶w {t = t} W) Y4→xZ) R 
  rewrite ⟶w-unique-tgt V W -- this should actually pass the termination checker -- it definitely IS terminating!
  = SI-Lemma (app t Y2) (app Z1 Z2) ? --  (app⟶s Y1Y3→Z1 Y2→Z2) 
            Y4→xZ
            (SI-wred-lemma (app (app Y1 Y3) Y2) (app t Y2) R (appL⟶w W))
SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) (app⟶s (app⟶s Y1Y3→Z1 Y1Y3→Z2) Y2→Z2) (red⟶s {s = Y4} (appL⟶w {t = t} W) Y4→xZ) R = {!  !}
--   = SI-Lemma (app t Y2) (app Z1 Z2) {!  !} Y4→xZ 
--              (SI-wred-lemma (app (app Y1 Y3) Y2) (app t Y2) R (appL⟶w W))
-- -- ... | c = {!  !}
--   with SI-wred-lemma (app (app Y1 Y3) Y2) (app t Y2) R (appL⟶w W) 
-- ... | R'
--   with ⟶s\⟶w Y1Y3→Z1 W 
-- ... | u ,, axʳ Z1→u , t→u = SI-Lemma t u t→u {!  !} {! !}
-- ... | u ,, axʳ Z1→u , t→u = SI-Lemma t u t→u {!  !} {! !}
-- ... | u ,, axʳ Z1→u , t→u = SI-Lemma (app t Y2) (app u Z2) (app⟶s t→u Y2→Z2) 
--                                   (⟶s!⟶s Y4→xZ (app⟶s refl⟶s (red⟶s (appL⟶w Z1→u) refl⟶s))) 
--                                   R'
  -- the following termination error shows we are induction on Y→Z first
-- ... | u ,, εʳ , t→u = SI-Lemma (app t Y2) (app Z1 Z2) (app⟶s t→u Y2→Z2) Y4→xZ R'
SI-Lemma (app (app Y1 Y3) Y2) (app Z1 Z2) Y1Y3Y2→xZ2@(app⟶s Y1Y3→Z1 Y2→Z2) (app⟶s Y1Y3→x Y2→Z1Z2) R 
  with ⟶s\⟶s Y1Y3→x Y1Y3→Z1 
... | u ,, red⟶s (red⟶w ()) x→u , Z1→u
... | u ,, var⟶s , Z1→u 
  with SI-wred*-lemma (app (app Y1 Y3) Y2) (app (var o) Y2) R (appL⟶w⋆ (var→w Y1Y3→x)) 
... | c =  SI-Lemma Y2 Z2 Y2→Z2 (⟶s!⟶s Y2→Z1Z2 (app⟶s Z1→u refl⟶s)) (SI-sred-lemma Y2 c)
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s (red⟶s (red⟶w ()) Y1→Z1) Y2→Z2) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (red⟶s (appL⟶w (red⟶w ())) Y1Y2→xZ) R
SI-Lemma (app (abs Y1) Y2) (app Z1 Z2) (app⟶s Y1→Z1 Y2→Z2) (app⟶s (red⟶s (red⟶w ()) Y1Y2→xZ) Y1Y2→xZ₁) R
SI-Lemma (app (abs Y1) Y2) (app (.abs Z1) Z2) (app⟶s (abs⟶s {r2 = Z1} Y1→Z1) Y2→Z2) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R
  -- = SI-Lemma (Y1 [ Y2 ]ₒ)  (Z1 [ Z2 ]ₒ) (⟶s[⟶s]ₒ Y1→Z1 Y2→Z2) (⟶s!⟶s Y1Y2→xZ (app⟶s var⟶s (red⟶s (red⟶w (redex refl)) refl⟶s)) ) ? 
  = SI-Lemma (Y1 [ Y2 ]ₒ)  (app (abs Z1) Z2) {!  !} Y1Y2→xZ 
             (SI-wred-lemma (app (abs Y1) Y2) (Y1 [ io var Y2 ]) R (red⟶w (redex refl)))
  -- = ?

-- OLD ATTEMPT 
--   with R 
-- ... | red⟶s R1 R2 = RecCall where 
--                 e0 = bind-map (Y1 [ lift (io var SI) ]) (Y2 [ io var SI ]) i ~! cong (Λ→ i) (~ (subst-lemma Y1 Y2 (io var SI)))
--                 Y→Z'  = (⟶s[⟶s]ₒ Y1→Z1 Y2→Z2) 
--                 Y→xZ' = (⟶s!⟶s Y1Y2→xZ (app⟶s var⟶s (red⟶s (red⟶w (redex refl)) refl⟶s)))
--                 R' = (⟶w-unique-tgt (appL⟶w (red⟶w (redex e0))) R1 ≡!⟶s ⟶s!⟶ₒ R2 (redex refl))
--                 RecCall = SI-Lemma (Y1 [ Y2 ]ₒ) (Z1 [ Z2 ]ₒ) Y→Z' Y→xZ' R'
-- ... | app⟶s R0 (red⟶s (red⟶w ()) R1)
-- SI-Lemma (app (abs Y1) Y2) (app (abs Z1) Z2) (app⟶s (abs⟶s {r2 = Z1} Y1→Z1) (red⟶s (red⟶w ()) Y2→Z2)) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R | app⟶s R0 var⟶s
-- SI-Lemma (app (abs Y1) Y2) (app (abs Z1) Z2) (app⟶s (abs⟶s {r2 = Z1} Y1→Z1) var⟶s) (red⟶s (red⟶w (redex refl)) Y1Y2→xZ) R | app⟶s R0 var⟶s 
--   = {!  !}
--   with R0 
-- ... | red⟶s (appL⟶w (red⟶w ())) R1
-- ... | red⟶s (red⟶w (redex refl)) R1 with Y1 
-- ... | var x = {!  !}
-- ... | app V1 V2 = {!  !}
-- ... | abs V3 with Y1Y2→xZ 
-- ... | red⟶s (red⟶w ()) c

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
-}
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
-- SI-Lemma1-aux Y₀ Z (red⟶s {s = Y₁} Y₀→Y₁ Y₁→Z) (red⟶s (appL⟶w (red⟶w ())) xY₀→Z) R
-- SI-Lemma1-aux Y₀ .(app _ _) (red⟶s {s = Y₁} Y₀→Y₁ Y₁→Z) (app⟶s (red⟶s (red⟶w ()) xY₀→Z) xY₀→Z₁) R
-- SI-Lemma1-aux Y₀ (app (var o) Y₁) (red⟶s {s = Z} Y₀→Z Z→xY₁) (app⟶s var⟶s Y₀→Y₁) R
--   with ⟶s\⟶w Y₀→Y₁ Y₀→Z
-- ... | c = {!   !}
-- ... | u ,, axʳ Y2→u , Y1→u = SI-Lemma1-aux Y₁ (app (var o) u) (⟶s!⟶s Y₁→xY₂ (app⟶s var⟶s (red⟶s Y2→u refl⟶s ) ) ) (app⟶s var⟶s Y1→u ) {!   !}
-- ... | .Y₂ ,, εʳ , Y1→u = SI-Lemma1-aux Y₁ (app (var o) Y₂) Y₁→xY₂ (app⟶s var⟶s Y1→u ) {!   !}
  -- = SI-Lemma1-aux Y₁ (app (var o) Y₂) Y₁→xY₂ (app⟶s var⟶s {!   !} ) {!   !}

-- We first prove that there is no fpc Y such that Yδ ⟶β Y
-- SI-Lemma1 : ∀ {X} (Y : Λ (↑ X)) → Y ∈ FPCx → ¬ (app (Λ→i (Y [ SI ]ₒ)) (var o) ⟶s Y)
-- SI-Lemma1 Y Y∈FPCx R with Y∈FPCx
-- ... | (Z ,, Y→βZ , xY→βZ) 
--   with ⟶β⋆⊆⟶s  Y→βZ 
--      | ⟶β⋆⊆⟶s xY→βZ
-- ... | Y→sZ | xY→sZ = {!  !}
-- ... | Y→sZ | xY→sZ = SI-Lemma1-aux Y Z Y→sZ xY→sZ (⟶s!⟶s R Y→sZ)

FPC-Case4-0-Impossible : ∀ {X} (Y : Λ X) → Y ∈ FPC → app Y SI ⟶β⋆ Y → ⊥
FPC-Case4-0-Impossible Y Y∈FPC R 
  with FPC-Case4-0 Y Y∈FPC R
... | (Z ,, Z∈WFPCx , Zδx→Z) 
  with FPCx⊆FPCx₂ Z Z∈WFPCx 
... | (Z' ,, Z→Z' , Z→xZ') = SI-Lemma Z Z' (⟶β⋆⊆⟶s Z→Z') (⟶β⋆⊆⟶s Z→xZ') Zδx→Z
