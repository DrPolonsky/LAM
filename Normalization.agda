module Normalization where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Relations.ClosureOperators
open import Reduction
open import TypedLambda

WN : ∀ {X} → 𝓟 (Λ X)
WN {X} t = Σ[ n ∈ Λ X ] ((t ⟶β⋆ n) × NF n)

data WNind {X : Set} : 𝓟 (Λ X) where
  NF⊆WN : ∀ {t} → t ∈ NF → t ∈ WNind
  redWN : ∀ {t} → ∀ s → (t ⟶β s) → s ∈ WNind → t ∈ WNind

redex!WN : ∀ {X} {s t : Λ X} → s ⟶β t → t ∈ WN → s ∈ WN
redex!WN s→t (n ,, t⟶β⋆n , n∈NF) = (n ,, (s→t ,⋆ t⟶β⋆n) , n∈NF)

WNind⊆WN : ∀ {X} → WNind {X} ⊆ WN
WNind⊆WN t (NF⊆WN t∈NF) = t ,, ε⋆ , t∈NF
WNind⊆WN t (redWN s t→βs s∈WNind) with WNind⊆WN s s∈WNind
... | n ,, s⟶β⋆n , n∈NF = n ,, (t→βs ,⋆ s⟶β⋆n) , n∈NF

WN⊆WNind : ∀ {X} → WN {X} ⊆ WNind
WN⊆WNind t (.t ,, ε⋆ , n∈NF) = NF⊆WN n∈NF
WN⊆WNind t (n ,, (t⟶βy ,⋆ y⟶β⋆n) , n∈NF) = redWN _ t⟶βy (WN⊆WNind _ (n ,, y⟶β⋆n , n∈NF ) )

data SN {X : Set} : 𝓟 (Λ X) where
  -- NF⊆SN : ∀ {t} → t ∈ NF → t ∈ SN
  redSN : ∀ {t} → (∀ s → (t ⟶β s) → s ∈ SN) → t ∈ SN

SN← : ∀ {X Y : Set} (f : X → Y) (t : Λ X) → Λ→ f t ∈ SN → t ∈ SN
SN← f s (redSN s[f]∈SN) = redSN λ t s→t → SN← f t (s[f]∈SN (Λ→ f t) (map⟶β f s→t) )

NF⊆SN : ∀ {X} {t : Λ X} → t ∈ NF → t ∈ SN
NF⊆SN {X} {t} t∈NF = redSN (λ s t⟶βs → ∅ (t∈NF s t⟶βs ) )

var⊆NF : ∀ {X} {x : X} → var x ∈ NF
var⊆NF N (red⟶β ())

abs⊆NF : ∀ {X} {t : Λ (↑ X)} → t ∈ NF → abs t ∈ NF
abs⊆NF t∈NF .(abs _) (abs⟶β r) = t∈NF _ r

-- -- this is simply not true without additional condition, that s is SN also?
-- ⟶ₒSN⊆SN : ∀ {X} {s t : Λ X} → s ⟶ₒ t → t ∈ SN → s ∈ SN
-- ⟶ₒSN⊆SN {X} {app (abs r) s} {.(r [ s ]ₒ)} (redex refl) T@(redSN r[s]∈SN)
--   = redSN λ { .(r [ s ]ₒ) (red⟶β (redex refl)) → T
--             ; (app (var x) .s) (appL⟶β (red⟶β ()))
--             ; (app (app u1 u2) .s) (appL⟶β (red⟶β ()))
--             ; (app (abs u1) .s) (appL⟶β (abs⟶β rs→u)) →
--                 ⟶ₒSN⊆SN (redex refl) (r[s]∈SN (u1 [ s ]ₒ) (rs→u ⟶β[ io var s ]) )
--             ; (app (abs .r) t) (appR⟶β rs→u) → redSN (λ u rt→u → f t u rs→u rt→u)
--             } where f : ∀ (t u : Λ X) → s ⟶β t → app (abs r) t ⟶β u → u ∈ SN
--                     f t u s→t rt→u = {!   !}
--                     -- Counterexample: s = (λx.I)Ω , t = I


appvar⊆NF : ∀ {X} {x : X} {s2 : Λ X} → (var x) ∈ NF → s2 ∈ NF → app (var x) s2 ∈ NF
appvar⊆NF s1∈NF s2∈NF (var x)         (red⟶β ())
appvar⊆NF s1∈NF s2∈NF (app M N)       (appL⟶β (red⟶β ()))
appvar⊆NF s1∈NF s2∈NF (app (var x) N) (appR⟶β n) = s2∈NF N n
appvar⊆NF s1∈NF s2∈NF (abs M)         (red⟶β ())

appapp⊆NF : ∀ {X} {s1 s2 s3 : Λ X} → (app s1 s3) ∈ NF → s2 ∈ NF → app (app s1 s3) s2 ∈ NF
appapp⊆NF s2∈NF s1s3∈NF (var x)            (red⟶β ())
appapp⊆NF s2∈NF s1s3∈NF (app M N)          (appL⟶β n) = s2∈NF M n
appapp⊆NF s2∈NF s1s3∈NF (app .(app _ _) N) (appR⟶β n) = s1s3∈NF N n
appapp⊆NF s2∈NF s1s3∈NF (abs M)            (red⟶β ())

decNF : ∀ {X} (s : Λ X) → (s ∈ NF) ⊔ Σ[ t ∈ Λ X ] (s ⟶β t)
decNF (var x) = in1 var⊆NF
decNF (app (var x) s2) with decNF s2
... | in1 s2∈NF        = in1 (appvar⊆NF var⊆NF s2∈NF)
... | in2 (t ,, s2⟶βt) = in2 (app (var x) t ,, appR⟶β s2⟶βt)
decNF (app (app s1 s3) s2) with decNF (app s1 s3) | decNF s2
... | in1 s1s3∈NF           | in1 s2∈NF           = in1 (appapp⊆NF s1s3∈NF s2∈NF)
... | _                     | in2 (t ,, apps2⟶βt) = in2 (app (app s1 s3) t ,, appR⟶β apps2⟶βt)
... | in2 (t ,, apps1s3⟶βt) | _                   = in2 (app t s2 ,, appL⟶β apps1s3⟶βt)
decNF (app (abs s1) s2) = in2 ((s1 [ io var s2 ]) ,, red⟶β (redex refl))
decNF (abs s) with decNF s
... | in1 s∈NF        = in1 (abs⊆NF s∈NF )
... | in2 (t ,, s⟶βt) = in2 (abs t ,, abs⟶β s⟶βt )

SN⊆WN : ∀ {X} → SN {X} ⊆ WN
-- SN⊆WN t (NF⊆SN t∈NF) = t ,, ε⋆ , t∈NF
SN⊆WN t (redSN IH) = case f g (decNF t) where
  f = λ t∈NF → t ,, ε⋆ , t∈NF
  g = λ { (u ,, t⟶βu) → redex!WN t⟶βu (SN⊆WN u (IH u t⟶βu) ) }

Λ𝓟 : Set₁
Λ𝓟 = ∀ {X} → 𝓟 (Λ X)

_⊆Λ_ : Λ𝓟 → Λ𝓟 → Set₁
P ⊆Λ Q = ∀ X → P {X} ⊆ Q {X}

↓β : Λ𝓟 → Λ𝓟
↓β P = λ t → Σ[ s ∈ Λ _ ] (s ∈ P × s ⟶β t)

↓β⋆ : Λ𝓟 → Λ𝓟
↓β⋆ P = λ t → Σ[ s ∈ Λ _ ] (s ∈ P × s ⟶β⋆ t)

is_β-closed : Λ𝓟 → Set₁
is P β-closed = ↓β P ⊆Λ P

is_β⋆-closed : Λ𝓟 → Set₁
is P β⋆-closed = ↓β⋆ P ⊆Λ P

⋆-closure-lemma : ∀ (P : Λ𝓟) → is P β-closed
                    → ∀ X (s t : Λ X) → s ∈ P → s ⟶β⋆ t → t ∈ P
⋆-closure-lemma P Pisβ-closed X s .s s∈P ε⋆ = s∈P
⋆-closure-lemma P Pisβ-closed X s t s∈P (s→y ,⋆ y⟶β⋆t)
  = ⋆-closure-lemma P Pisβ-closed X _ t (Pisβ-closed X _ (s ,, s∈P , s→y)) y⟶β⋆t

⋆-closure : ∀ (P : Λ𝓟) → is P β-closed → is P β⋆-closed
⋆-closure P Pisβ-closed X t (s ,, s∈P , s⟶β⋆t) = ⋆-closure-lemma P Pisβ-closed X s t s∈P s⟶β⋆t

-- SN is closed under reduction
SN-is-β-closed : is SN β-closed
-- SN-is-β-closed X t (s ,, NF⊆SN x , s⟶βt) = ∅ (x t s⟶βt )
SN-is-β-closed X t (s ,, redSN x , s⟶βt) = x t s⟶βt

SN-is-β⋆-closed : is SN β⋆-closed
SN-is-β⋆-closed = ⋆-closure SN SN-is-β-closed

SN-abs : ∀ {V} (r : Λ (↑ V)) → abs r ∈ SN → r ∈ SN
SN-abs {V} r (redSN absr∈SN) = redSN (λ s r→s → SN-abs s (absr∈SN (abs s) (abs⟶β r→s)))

SN+abs : ∀ {V} (r : Λ (↑ V)) → r ∈ SN → abs r ∈ SN
SN+abs {V} r (redSN r∈SN) = redSN (λ { (abs s) (abs⟶β r→s) → SN+abs s (r∈SN s r→s)})

subst-SN : ∀ {X} (t : Λ X) → ∀ {Y} (f : X → Λ Y) → t [ f ] ∈ SN → t ∈ SN
subst-SN {X} t f (redSN t[f]∈SN) = redSN sSN where
  sSN : ∀ (s : Λ X) → t ⟶β s → SN s
  sSN s t⟶βs = subst-SN s f (t[f]∈SN (s [ f ]) (t⟶βs ⟶β[ f ]))

appSN : ∀ {X} (s t : Λ X) → app s t ∈ SN → s ∈ SN
appSN {X} s t (redSN st∈SN) = redSN s∈SN where
  s∈SN : ∀ (u : Λ X) → s ⟶β u → SN u
  s∈SN u s⟶βu = appSN u t (st∈SN (app u t) (appL⟶β s⟶βu))

data whexp {X : Set} (P : 𝓟 (Λ X)) : 𝓟 (Λ X) where
  whe : ∀ {s t : Λ X} → s ⟶w t → t ∈ P → s ∈ whexp P

-- Neutral terms, 𝓝 is \MCN
data 𝓝Λ {X : Set} : 𝓟 (Λ X) where
  var𝓝Λ : ∀ (x : X) → var x ∈ 𝓝Λ
  app𝓝Λ : ∀ (s t : Λ X) → s ∈ 𝓝Λ → t ∈ SN → app s t ∈ 𝓝Λ

𝓝Λ↓β⊆𝓝Λ : ∀ {X} (s t : Λ X) → s ∈ 𝓝Λ → s ⟶β t → t ∈ 𝓝Λ
𝓝Λ↓β⊆𝓝Λ .(var x)     t (var𝓝Λ x) (red⟶β ())
𝓝Λ↓β⊆𝓝Λ .(app (abs _) s2) t (app𝓝Λ .(abs _) s2 () s2∈SN) (red⟶β (redex e))
𝓝Λ↓β⊆𝓝Λ (app s1 t) (app s2 t) (app𝓝Λ s1 t s1∈N t∈SN) (appL⟶β s12)
  = app𝓝Λ s2 t (𝓝Λ↓β⊆𝓝Λ s1 s2 s1∈N s12 ) t∈SN
𝓝Λ↓β⊆𝓝Λ {X} (app s t1) (app s t2) (app𝓝Λ s t1 s∈N t1∈SN) (appR⟶β t12)
  = app𝓝Λ s t2 s∈N (SN-is-β-closed X t2 (t1 ,, t1∈SN , t12))

app𝓝ΛSN : ∀ {X} (s t : Λ X) → s ∈ SN → s ∈ 𝓝Λ → t ∈ SN → app s t ∈ SN
app𝓝ΛSN₀ : ∀ {X} (s t : Λ X) → s ∈ SN → s ∈ 𝓝Λ → t ∈ SN → ∀ u → app s t ⟶β u → u ∈ SN

app𝓝ΛSN s t ssn snl tsn = redSN (app𝓝ΛSN₀ s t ssn snl tsn )
app𝓝ΛSN₀ {X} .(abs _) t S () t∈SN u (red⟶β (redex e))
app𝓝ΛSN₀ {X} s1 t S@(redSN s∈SN) s∈Neut t∈SN (app s2 .t) U@(appL⟶β s12)
  = app𝓝ΛSN s2 t (s∈SN s2 s12) (𝓝Λ↓β⊆𝓝Λ s1 s2 s∈Neut s12) t∈SN
app𝓝ΛSN₀ {X} s t1 S@(redSN s∈SN) s∈Neut (redSN t1∈SN) (app .s t2) (appR⟶β t12)
  = app𝓝ΛSN s t2 S s∈Neut (t1∈SN t2 t12)

𝓝Λ⊆SN : 𝓝Λ ⊆Λ SN
𝓝Λ⊆SN X .(var x)   (var𝓝Λ x) = NF⊆SN var⊆NF
𝓝Λ⊆SN X .(app s t) (app𝓝Λ s t s∈N t∈SN) = app𝓝ΛSN s t (𝓝Λ⊆SN X s s∈N) s∈N t∈SN

module CompPred {𝔸 : Set} (P₀ : 𝔸 → Λ𝓟) where

  ⇒𝓟 : Λ𝓟 → Λ𝓟 → Λ𝓟
  ⇒𝓟 P Q {X} = λ t → ∀ (a : Λ X) → a ∈ P → app t a ∈ Q

  -- 𝓒 is \MCC
  𝓒 : ∀ (A : 𝕋 𝔸) → Λ𝓟
  𝓒 (atom α) = P₀ α
  𝓒 (A ⇒ B) {X} = ⇒𝓟 (𝓒 A) (𝓒 B)

  record Saturated (S : Λ𝓟) : Set₁ where
    field
      SatSN : S ⊆Λ SN
      Sat𝓝 : 𝓝Λ ⊆Λ S
      SatWE : whexp S ⊆Λ S

  SNisSat : Saturated SN
  SNisSat = record { SatSN = λ X ΛX SNΛX → SNΛX ;
                     Sat𝓝 = 𝓝Λ⊆SN ;
                     SatWE = λ X t t∈whexpSN → {!   !} } -- SUPER HARD!!
                     -- (Because, it's not true.)
  open Saturated

  -- Natural : Λ𝓟 → Set₁
  -- Natural P = ∀ {A B : Set} (f : A → B) → ∀ {t : Λ A} → t ∈ P {A} → Λ→ f t ∈ P {B}
  --
  -- ⇒𝓟isNatural : ∀ {P Q : Λ𝓟} → Natural P → Natural Q → Natural (⇒𝓟 P Q)
  -- ⇒𝓟isNatural Pnat Qnat f {t} t∈P⇒Q u u∈P = {!   !}

  -- Liftable : Λ𝓟 → Set₁
  -- Liftable P = ∀ {X} (t : Λ X) → t ∈ P → Λ→i t ∈ P
  --
  -- ⇒𝓟isLiftable : ∀ {P Q : Λ𝓟} → Liftable P → Liftable Q → Liftable (⇒𝓟 P Q)
  -- ⇒𝓟isLiftable Plift Qlift t t∈X a = {!   !}

  ⇒𝓟isSN- : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → ∀ X t → t ∈ ⇒𝓟 P Q {↑ X} → t ∈ SN
  ⇒𝓟isSN- P Q Psat Qsat X t H =
    let to∈Q : app t (var o) ∈ Q {↑ X}
        to∈Q = H (var o) (Sat𝓝 Psat (↑ X) (var o) (var𝓝Λ o ) )
        to∈SN : app t (var o) ∈ SN
        to∈SN = SatSN Qsat (↑ X) (app t (var o)) to∈Q
     in appSN t (var o) to∈SN
  ⇒𝓟isSN : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → ⇒𝓟 P Q ⊆Λ SN
  ⇒𝓟isSN P Q Psat Qsat X t H = SN← i t {!   !} -- Need P⇒Q to be natural or liftable
  Λ𝓝⊆⇒𝓟 : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → 𝓝Λ ⊆Λ ⇒𝓟 P Q
  Λ𝓝⊆⇒𝓟 P Q Psat Qsat X t t∈N u u∈P = Sat𝓝 Qsat X (app t u) (app𝓝Λ t u t∈N (SatSN Psat X u u∈P) )
  ⇒𝓟WE : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → whexp (⇒𝓟 P Q) ⊆Λ ⇒𝓟 P Q
  ⇒𝓟WE P Q Psat Qsat X s (whe {t = t} s→t t∈P⇒Q) u u∈P =
    SatWE Qsat X (app s u) (whe (appL⟶w s→t ) (t∈P⇒Q u u∈P ) )

  ⇒𝓟isSat : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → Saturated (⇒𝓟 P Q)
  ⇒𝓟isSat P Q Psat Qsat = record { SatSN = ⇒𝓟isSN P Q Psat Qsat ;
                                   Sat𝓝 = Λ𝓝⊆⇒𝓟 P Q Psat Qsat ;
                                   SatWE = ⇒𝓟WE P Q Psat Qsat }

  𝓒isSat : (∀ (a : 𝔸) → Saturated (P₀ a)) → (∀ (A : 𝕋 𝔸) → Saturated (𝓒 A))
  𝓒isSat atomSat (atom α) = atomSat α
  𝓒isSat atomSat (A ⇒ B) = ⇒𝓟isSat (𝓒 A) (𝓒 B) (𝓒isSat atomSat A) (𝓒isSat atomSat B)
















-- The end
