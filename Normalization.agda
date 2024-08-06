module Normalization where

open import Logic
open import Lifting
open import Lambda
open import Predicates
open import Relations.ClosureOperators
open import Reduction
open import TypedLambda

WN : ∀ {X} → 𝓟 (Λ X)
WN {X} t = Σ[ n ∈ Λ X ] (t ⟶β⋆ n × NF n)

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
  NF⊆SN : ∀ {t} → t ∈ NF → t ∈ SN
  redSN : ∀ {t} → (∀ s → (t ⟶β s) → s ∈ SN) → t ∈ SN

var⊆NF : ∀ {X} {x : X} → var x ∈ NF
var⊆NF N (red⟶β ())

abs⊆NF : ∀ {X} {t : Λ (↑ X)} → t ∈ NF → abs t ∈ NF
abs⊆NF t∈NF .(abs _) (abs⟶β r) = t∈NF _ r

appvar⊆NF : ∀ {X} {x : X} {s2 : Λ X} → (var x) ∈ NF → s2 ∈ NF → app (var x) s2 ∈ NF
appvar⊆NF s1∈NF s2∈NF (var x) (red⟶β ())
appvar⊆NF s1∈NF s2∈NF (app M N) (appL⟶β (red⟶β ()))
appvar⊆NF s1∈NF s2∈NF (app (var x) N) (appR⟶β n) = s2∈NF N n
appvar⊆NF s1∈NF s2∈NF (abs M) (red⟶β ())

appapp⊆NF : ∀ {X} {s1 s2 s3 : Λ X} → (app s1 s3) ∈ NF → s2 ∈ NF → app (app s1 s3) s2 ∈ NF
appapp⊆NF s2∈NF s1s3∈NF (var x) (red⟶β ())
appapp⊆NF s2∈NF s1s3∈NF (app M N) (appL⟶β n) = s2∈NF M n
appapp⊆NF s2∈NF s1s3∈NF (app .(app _ _) N) (appR⟶β n) = s1s3∈NF N n
appapp⊆NF s2∈NF s1s3∈NF (abs M) (red⟶β ())

decNF : ∀ {X} (s : Λ X) → (s ∈ NF) ⊔ Σ[ t ∈ Λ X ] (s ⟶β t)
decNF (var x) = in1 var⊆NF
decNF (app (var x) s2) with decNF s2
... | in1 s2∈NF = in1 (appvar⊆NF var⊆NF s2∈NF)
... | in2 (t ,, s2⟶βt) = in2 (app (var x) t ,, appR⟶β s2⟶βt)
decNF (app (app s1 s3) s2) with decNF (app s1 s3) | decNF s2
... | in2 (t ,, apps1s3⟶βt) | _ = in2 (app t s2 ,, appL⟶β apps1s3⟶βt)
... | in1 _ | in2 (t ,, apps2⟶βt) = in2 (app (app s1 s3) t ,, appR⟶β apps2⟶βt)
... | in1 s1s3∈NF | in1 s2∈NF = in1 (appapp⊆NF s1s3∈NF s2∈NF)
decNF (app (abs s1) s2) = in2 ((s1 [ io var s2 ]) ,, red⟶β (redex refl))
decNF (abs s) with decNF s
... | in1 s∈NF = in1 (abs⊆NF s∈NF )
... | in2 (t ,, s⟶βt) = in2 (abs t ,, abs⟶β s⟶βt )

SN⊆WN : ∀ {X} → SN {X} ⊆ WN
SN⊆WN t (NF⊆SN t∈NF) = t ,, ε⋆ , t∈NF
SN⊆WN t (redSN IH) = case f g (decNF t) where
  f = λ t∈NF → t ,, ε⋆ , t∈NF
  g = λ { (u ,, t⟶βu) → redex!WN t⟶βu (SN⊆WN u (IH u t⟶βu) ) }

Λ𝓟 : Set₁
Λ𝓟 = ∀ {X} → 𝓟 (Λ X)

_⊆Λ_ : Λ𝓟 → Λ𝓟 → Set₁
P ⊆Λ Q = ∀ X → P {X} ⊆ Q {X}

data whexp {X : Set} (P : 𝓟 (Λ X)) : 𝓟 (Λ X) where
  whe : ∀ {s t : Λ X} → s ⟶w t → t ∈ P → s ∈ whexp P


-- Neutral terms, 𝓝 is \MCN
data 𝓝Λ {X : Set} : 𝓟 (Λ X) where
  var𝓝Λ : ∀ (x : X) → var x ∈ 𝓝Λ
  app𝓝Λ : ∀ (s t : Λ X) → s ∈ 𝓝Λ → t ∈ SN → app s t ∈ 𝓝Λ

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
                     Sat𝓝 = λ X ΛX 𝓝ΛX → NF⊆SN λ N x → {!   !} ;
                     SatWE = {!   !} }

  ⇒𝓟isSat : ∀ (P Q : Λ𝓟) → Saturated P → Saturated Q → Saturated (⇒𝓟 P Q)
  ⇒𝓟isSat P Q Psat Qsat = record { SatSN = λ X ΛX ⇒𝓟PQΛX → {!   !} ;
                                   Sat𝓝 = {!   !} ;
                                   SatWE = {!   !} }

  𝓒isSat : (∀ (a : 𝔸) → Saturated (P₀ a)) → (∀ (A : 𝕋 𝔸) → Saturated (𝓒 A))
  𝓒isSat atomSat A = record { SatSN = λ X x x₁ → redSN λ s x₂ → {!   !} ;
                              Sat𝓝 = {!   !} ;
                              SatWE = {!   !} }


























-- The end
 