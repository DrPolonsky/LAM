module QADT.Examples where

open import Logic
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import ADT-Isomorphisms
open import QADT.Environment

module G=1+2G+G²+G³ where

  g : ADT 1
  g = 𝟏 ⊔ (Num 2 × (𝕍 (here 0))) ⊔ (𝕍 (here 0)) ² ⊔ (𝕍 (here 0)) ³

  G : ADT 0
  G = μ g

  GG : Set
  GG = ⟦ G ⟧ EmptyEnv

  Gleaf : GG
  Gleaf = lfp (in1 tt )
  Gunode1 : GG → GG
  Gunode1 g = lfp (in2 (in1 (in1 tt , g ) ) )
  Gunode2 : GG → GG
  Gunode2 g = lfp (in2 (in1 (in2 (in1 tt) , g ) ) )
  Gbnode : GG ∧ GG → GG
  Gbnode g12 = lfp (in2 (in2 (in1 g12 ) ) )
  Gtnode : GG ∧ (GG ∧ GG) → GG
  Gtnode g123 = lfp (in2 (in2 (in2 g123)))

  allG : ℕ → List GG
  allG zero = [] -- Gleaf ∷ []
  allG (succ n) = let
      un1 = List→ Gunode1 (allG n)
      un2 = List→ Gunode2 (allG n)
      allG² : List (GG ∧ GG)
      allG² = lazyProd (allG n) (allG n)
      allG³ : List (GG ∧ (GG ∧ GG))
      allG³ = lazyProd (allG n) allG²
      bn  = List→ Gbnode allG²
      tn =  List→ Gtnode allG³
    in Gleaf ∷ merge (merge un1 un2) (merge bn tn)

  ==G : GG → GG → 𝔹
  ==G (lfp (in1 _)) (lfp (in1 _)) = true
  ==G (lfp (in2 (in1 (in1 _ , g1)))) (lfp (in2 (in1 (in1 _ , g2)))) = ==G g1 g2
  ==G (lfp (in2 (in1 (in2 (in1 _) , g1)))) (lfp (in2 (in1 (in2 (in1 _) , g2)))) = ==G g1 g2
  ==G (lfp (in2 (in2 (in1 (g1 , g2))))) (lfp (in2 (in2 (in1 (g1' , g2'))))) = and (==G g1 g2) (==G g1' g2')
  ==G (lfp (in2 (in2 (in2 (g1 , (g2 , g3)))))) (lfp (in2 (in2 (in2 (g1' , (g2' , g3')))))) =
    and (==G g3 g3') (and (==G g1 g2) (==G g1' g2'))
  ==G _ _ = false

module M=1+M+M² where

  m : ADT 1
  m = 𝟏 ⊔ (𝕍 (here 0)) ⊔ (𝕍 (here 0)) ²

  M : ADT 0
  M = μ m

  MM : Set
  MM = ⟦ M ⟧ EmptyEnv

  Mleaf : MM
  Mleaf = lfp (in1 tt)
  Munode : MM → MM
  Munode m = lfp (in2 (in1 m) )
  Mbnode : MM → MM → MM
  Mbnode m1 m2 = lfp (in2 (in2 ((m1 , m2 )) ) )
  MbnodeCurried : MM ∧ MM → MM
  MbnodeCurried (m1 , m2) = lfp (in2 (in2 ((m1 , m2 )) ) )


  allM : ℕ → List MM
  allM zero = []
  allM (succ n) = let
    un = List→ Munode (allM n)
    allM² : List (MM ∧ MM)
    allM² = lazyProd (allM n) (allM n)
    bn = List→ MbnodeCurried allM²
    in Mleaf ∷ merge un bn

  ==M : MM → MM → 𝔹
  ==M (lfp (in1 _)) (lfp (in1 _)) = true
  ==M (lfp (in2 (in1 m1))) (lfp (in2 (in1 m2))) = ==M m1 m2
  ==M (lfp (in2 (in2 (m1 , m2)))) (lfp (in2 (in2 (m1' , m2')))) = and (==M m1 m1') (==M m2 m2')
  ==M _ _ = false

  open G=1+2G+G²+G³

  gM : ADT 0
  gM = g [ M ]

  gM=M : Iso gM M
  -- gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r ) !! )) =!= a+= (+= e ) ) ) )
  gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= !! ar i+r) !! )) =!= a+= (+= e ) ) ) )
    where  e = dist3 ~!= ×= (~~ (fix≃ m ) )

  G→M : ⟦ G ⟧ EmptyEnv  → ⟦ M ⟧ EmptyEnv
  G→M = foldADT g (λ ()) (⟦ M ⟧ EmptyEnv) ((_≃_.f+ (≃⟦ gM=M ⟧ EmptyEnv )))

  findm? : MM → ℕ → 𝔹
  findm? m n = elem ==M m (List→ G→M (allG n))

  allGlength : ℕ → ℕ
  allGlength = length ∘ allG

  [1-4] : List ℕ
  [1-4] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

  [1-10] : List ℕ
  [1-10] = 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ []

  cn : ∀ {A : Set} → ℕ → (A → A) → A → A
  cn {A} zero f x = x
  cn {A} (succ n) f x = f (cn n f x)

  bigM : MM
  bigM = cn 7 (Mbnode Mleaf) Mleaf

  check : Set
  check = {! findm? Mtest3 5  !}
  -- check = {! findm? (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) Mleaf))) 4   !}
  -- check = {! ==M  (G→M (Gleaf)) Mleaf   !}

  -- take 100 (allM 4) works
  -- take 100 (allM 5) works
  20ms : List MM
  20ms = take 20 (allM 6)

  filter : ∀ {A} → (A → 𝔹) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) = if f x then (filter f xs) else x ∷ (filter f xs)

  pass1 : List MM
  pass1 = filter (λ x → (findm? x 3)) 20ms

  pass2 : List MM
  pass2 = filter (λ x → findm? x 4) pass1

  pass3 : List MM
  pass3 = filter (λ x → findm? x 5) pass2

  -- why does it stop at a number? agda limitation? or the way allM is generated?
  -- test = {! length (filter (λ {(x , y) → ==M x y})  (zip (take 1000000 (allM 5)) (take 1000000 (allM 6))))  !}


  -- T→B : ⟦ T ⟧ EmptyEnv  → ⟦ B ⟧ EmptyEnv
  -- T→B = foldADT t (λ ()) (⟦ B ⟧ EmptyEnv) ((_≃_.f+ (≃⟦ tB=B ⟧ EmptyEnv )))

  h : ⟦ G ⟧ ρ₀ → ⟦ M ⟧ ρ₀
  h x = fold {λ X → ⟦ g ⟧ (extEnv X ρ₀)} (λ j →  ⟦ g ⟧→ (λ tt → j)) (_≃_.f+ (≃⟦ gM=M ⟧ ρ₀ ) ) x

  M²=M+M²+M³ : Iso (M ²) (M ⊔ M ² ⊔ M ³)
  M²=M+M²+M³ = t= (t= (×= (fix≃ m)) (dist3) ) (∨≃ (c×= (i×l= r= ) ) r=  )  -- (s= {! dist3   !} )
  --
  M²=M³+M²+M : Iso (M ²) (M ³ ⊔ M ² ⊔ M)
  M²=M³+M²+M = t= M²=M+M²+M³ (c+= (t= (=+ (c+= r= )) (a+= r=) ) )
  --
  -- -- M²=1+2M+2M²+2M³ : Iso (M ²) (𝟏 ⊔ M ⊔ M ⊔ M ² ⊔ M ² ⊔ M ³ ⊔ M ³)
  M²=1+2M+2M²+2M³ : Iso (M ²) (M ³ ⊔ M ³ ⊔ M ² ⊔ M ² ⊔ M ⊔ M ⊔ 𝟏)
  M²=1+2M+2M²+2M³  = t= M²=M³+M²+M (+= (t= (=+ M²=M³+M²+M ) (a+= (+= (a+= (+= e ) ) ) ) ) )
    where e = t= (+= (fix≃ m ) ) (s= (t= cycle+ (+= (t= (=+ (c+= r= ) ) (a+= r=) ) ) ) )

  e3 : Iso (M ²) ((M ³ ⊔ M ³) ⊔ ( M ² ⊔ M ²) ⊔ (M ⊔ M) ⊔ 𝟏)
  e3 = t= M²=1+2M+2M²+2M³ (s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) ) )

  X+X=2X : ∀ {n} (X : ADT n) → Iso (X ⊔ X) (Num 2 × X)
  X+X=2X A = ~~ (dr= (cong+ i×l (dr= (+! i×l =!= (!+ al =!= i+r) ) ) ) )
  -- X+X=2X A = s= (dl= (∨≃ (i×l r=) (dl= (t= (∨≃ (i×l r=) (c× (ar= r= ) ) ) (c+ (i+ r= ) ) ) ) ) )

  M²=2M²+1 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
  -- M²=2M²+1 = t= e3 (s= {! t=   !} ) -- (s= (t= (=+ (t= (×= M²=M³+M²+M ) {!   !} )  ) {!   !} ) )
  M²=2M²+1 = t= e3 (s= (t= (=+ (t= (×= M²=M³+M²+M ) (s= (X+X=2X _ ) ) )  )
    (t= (a+= (a+= (+= (c+= (a+= (a+= (+= (a+= (+= (c+= (a+= (c+= (a+= (a+= (+= r= ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) e) ) )
    where e = s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) )
  -- M²=2M²+1 = t= e3 (s= (t= (=+ (s= (X+X=2X (M ²) ) ) ) {!    !} ) )


module 1+X²=1+X+X³ where
  -- The explicitly defined version
  data BT : Set where
    BTleaf : BT
    BTnode : BT → BT → BT

  data TT : Set where
    TTleaf : TT
    TUnode : TT → TT
    TTnode : TT → TT → TT → TT

  BT→TT : BT → TT
  BT→TT BTleaf = TTleaf
  BT→TT (BTnode bt1 BTleaf) = TUnode (BT→TT bt1)
  BT→TT (BTnode bt1 (BTnode bt2 bt3)) = TTnode (BT→TT bt1) (BT→TT bt2) (BT→TT bt3)

  TT→BT : TT → BT
  TT→BT TTleaf = BTleaf
  TT→BT (TUnode t) = BTnode (TT→BT t) BTleaf
  TT→BT (TTnode t1 t2 t3) = BTnode (TT→BT t1) (BTnode (TT→BT t2) (TT→BT t3) )

  cong : ∀ {A B : Set} (f : A → B) {a1 a2 : A} → a1 ≡ a2 → f a1 ≡ f a2
  cong f (refl _) = refl _

  cong2 : ∀ {A B C : Set} (f : A → B → C)
           {a1 a2 : A} → a1 ≡ a2 → {b1 b2 : B} → b1 ≡ b2 → f a1 b1 ≡ f a2 b2
  cong2 f (refl _) (refl _) = (refl _)

  cong3 : ∀ {A B C D : Set} (f : A → B → C → D) {a1 a2 b1 b2 c1 c2}
            → a1 ≡ a2 → b1 ≡ b2 → c1 ≡ c2 → f a1 b1 c1 ≡ f a2 b2 c2
  cong3 f (refl _) (refl _) (refl _) = refl _

  BT→TT→BT : ∀ b → TT→BT (BT→TT b) ≡ b
  BT→TT→BT BTleaf = refl BTleaf
  BT→TT→BT (BTnode b1 BTleaf) = cong (λ x → BTnode x BTleaf) (BT→TT→BT b1)
  BT→TT→BT (BTnode b1 (BTnode b2 b3)) = cong3 (λ x y z → BTnode x (BTnode y z)) (BT→TT→BT b1) (BT→TT→BT b2) (BT→TT→BT b3)

  TT→BT→TT : ∀ t → BT→TT (TT→BT t) ≡ t
  TT→BT→TT TTleaf = refl TTleaf
  TT→BT→TT (TUnode t) = cong TUnode (TT→BT→TT t)
  TT→BT→TT (TTnode t1 t2 t3) = cong3 TTnode (TT→BT→TT t1) (TT→BT→TT t2) (TT→BT→TT t3)

  -- Using the calculus of isomorphisms

  b : ADT 1
  b = 1+ (𝕧₀ ²)

  t : ADT 1
  t = 1+ (𝕧₀ ⊔ (𝕧₀ ³))

  t-func : Set → Set
  t-func X = ⟦ t ⟧ (λ _ → X )

  -- t-functor : Functor t-func
  -- t-functor f = ⟦ t ⟧→ emap where
  --   emap = {!   !}

  B : ADT 0
  B = μ b

  T : ADT 0
  T = μ t

  tB=B : Iso (t [ B ]) B
  tB=B = ~~ (fix≃ b =!= += (×= (fix≃ b) =!= dl= (=+ i×r ) ) )

  foldT : ∀ (X : Set) → (t-func X → X) → ⟦ T ⟧ EmptyEnv → X
  foldT X Xalg (lfp (in1 tt)) = Xalg (in1 tt)
  foldT X Xalg (lfp (in2 (in1 x))) = Xalg (in2 (in1 (foldT X Xalg x ) ) )
  foldT X Xalg (lfp (in2 (in2 (x1 , (x2 , x3)))))
    = Xalg (in2 (in2 ((fT x1) , ((fT x2) , fT x3 ) ) ) ) where fT = foldT X Xalg
  -- foldT X = fold {F = t-func} λ {A} {B} f → ⟦ t ⟧→ {!   !}

  T→B : ⟦ T ⟧ EmptyEnv  → ⟦ B ⟧ EmptyEnv
  T→B = foldADT t (λ ()) (⟦ B ⟧ EmptyEnv) ((_≃_.f+ (≃⟦ tB=B ⟧ EmptyEnv )))
  -- foldT (⟦ B ⟧ EmptyEnv) (_≃_.f+ (≃⟦ tB=B ⟧ EmptyEnv ) )


-- Iso ((𝟏 ⊔ 𝟎) × A × B ⊔ A × B) ((𝟏 ⊔ 𝟏 ⊔ 𝟎) × A × B)
-- Iso (1+ (1+ 𝟎) × A × B) (1+ 𝟎 × A × B ⊔ A × B)

𝔹≃𝔹₁ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₁ = !!
𝔹≃𝔹₂ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₂ = a+ ~!= i+r= (c+= (!+ (~~ i+r) ) )
-- 𝔹≃𝔹₂ = c+= (cong+ i+r (~~ i+r) )
-- 𝔹≃𝔹₂ = c+= (a+= (!+ c+ ) )

iso≠lemma : ∀ {A B : Set} (i1 i2 : A ≃ B) → ∀ (a : A) → ¬ (_≃_.f+ i1 a ≡ _≃_.f+ i2 a) → ¬ (i1 ≡ i2)
iso≠lemma i1 .i1 a neq (refl .i1) = neq (refl (_≃_.f+ i1 a) )

𝔹1≠𝔹2 : ¬ (≃⟦ 𝔹≃𝔹₁ ⟧ EmptyEnv ≡ ≃⟦ 𝔹≃𝔹₂ ⟧ EmptyEnv)
𝔹1≠𝔹2 i1=i2 = iso≠lemma (≃⟦ 𝔹≃𝔹₁ ⟧ EmptyEnv) (≃⟦ 𝔹≃𝔹₂ ⟧ EmptyEnv) (in1 tt) (λ {()} ) i1=i2


-- 1 + X + X^3
FADT : ADT 1
FADT = 𝟏 ⊔ (𝕍 (here 0) ⊔ (𝕍 (here 0) × (𝕍 (here 0) × 𝕍 (here 0) ) ) )

-- 1 + X^2
GADT : ADT 1
GADT = 𝟏 ⊔ (𝕍 (here 0) × 𝕍 (here 0) )

Iso1 : Iso FADT GADT
Iso1 = {! fold   !}

module X=X^4 where

  ∛1 : ADT 0
  ∛1 = μ ((1+ (𝕍 (here 0))) ²)

  X : ADT 0
  X = ∛1

  skel : ADT 1
  skel = (1+ ((wk (here 0) X) × (𝕍 (here 0)))) ²

  -- 1+X^2=1+X[1+X^2] : Iso (1+ (X ²)) (1+ (X × (1+ (X ²))))
  -- 1+X^2=1+X[1+X^2] = subst≃ {0} {skel} {skel} {X} {1+ (X ²)} (refl≃ skel) (fix≃ ((1+ (𝕍 (here 0))) ²))

  1+X²≃1+X[1+X²] : Iso (1+ (X ²)) (1+ (X × (1+ X ²)))
  1+X²≃1+X[1+X²] = {!   !} -- subst≃ {0} {skel} {skel} {X} {1+ X ²} (refl≃ skel) (fix≃ ((1+ (𝕍 (here 0))) ²) )

  X=1+X+X^2 : Iso X (1+ (X ⊔ (X ²)))
  X=1+X+X^2 = fix≃ ((1+ (𝕍 (here 0))) ²) =!= {!   !}

exsub : ADT 1
exsub = μ (𝟏 ⊔ (𝕍 (here 1) × 𝕍 (down (here 0 ) ) )) ⊔ (𝕍 (here 0))

ex2sub : ADT 1
ex2sub = (𝟏 ⊔ 𝕍 (here 0))

Nat' : ADT 0
Nat' = μ (𝟏 ⊔ 𝕍 (here 0) )

List' : ADT 1
List' = μ (𝟏 ⊔ (𝕍 (down (here 0)) × 𝕍 (here 1) ) )

Nat : Set
Nat = ⟦ Nat' ⟧ EmptyEnv

one : Nat
one = lfp (in2 (lfp (in1 tt ) ) )
