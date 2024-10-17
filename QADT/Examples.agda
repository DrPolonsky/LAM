module QADT.Examples where

open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment

-- TODO
-- implement convenient syntax for substitution inside isomorphisms
-- automate search for ring isomorphisms proofs


module G=1+2G+G²+G³ where

  g : ADT 1
  g = 𝟏 ⊔ (Num 2 × (𝕍 (o))) ⊔ (𝕍 (o)) ² ⊔ (𝕍 (o)) ³

  G : ADT 0
  G = μ g

  GG : Set
  GG = ⟦ G ⟧ Γ₀

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
  m = 𝟏 ⊔ (𝕍 (o)) ⊔ (𝕍 (o)) ²

  M : ADT 0
  M = μ m

  MM : Set
  MM = ⟦ M ⟧ Γ₀

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

  G→M : ⟦ G ⟧ Γ₀  → ⟦ M ⟧ Γ₀
  G→M = foldADT g (λ ()) (⟦ M ⟧ Γ₀) ((_≃_.f+ (≃⟦ gM=M ⟧ Γ₀ )))

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

  -- check : Set
  -- check = {! findm? Mtest3 5  !}
  -- check = {! findm? (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) (Mbnode (Munode Mleaf) Mleaf))) 4   !}
  -- check = {! ==M  (G→M (Gleaf)) Mleaf   !}

  -- take 100 (allM 4) works
  -- take 100 (allM 5) works
  20ms : List MM
  20ms = take 20 (allM 6)

  filter : ∀ {A} → (A → 𝔹) → List A → List A
  filter f [] = []
  filter f (x ∷ xs) = if f x then (filter f xs) else x ∷ (filter f xs)

  pass0 : List MM
  pass0 = filter (λ x → (findm? x 3)) 20ms

  pass1 : List MM
  pass1 = filter (λ x → findm? x 4) pass0

  pass3 : List MM
  pass3 = filter (λ x → findm? x 5) pass1

  -- why does it stop at a number? agda limitation? or the way allM is generated?
  -- test = {! length (filter (λ {(x , y) → ==M x y})  (zip (take 1000000 (allM 5)) (take 1000000 (allM 6))))  !}


  -- T→B : ⟦ T ⟧ Γ₀  → ⟦ B ⟧ Γ₀
  -- T→B = foldADT t (λ ()) (⟦ B ⟧ Γ₀) ((_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ )))

  h : ⟦ G ⟧ Γ₀ → ⟦ M ⟧ Γ₀
  h x = fold {λ X → ⟦ g ⟧ (Γ₀ ⅋o:= X)} (λ j →  ⟦ g ⟧→ (λ tt → j)) (_≃_.f+ (≃⟦ gM=M ⟧ Γ₀ ) ) x

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

-- The binary strings
module S=1+2S where

  s : ADT 1
  s = Num 2 × 𝕍 o ⊔ 𝟏

  S : ADT 0
  S = μ s

  2+S : ADT 0
  2+S = 1+ (1+ S)

  S+3=2S+4 : Iso (1+ 2+S) (2+S ⊔ 2+S)
  S+3=2S+4 = += (+= (+= (fix≃ s) )) =!= ~~ (a+= (+= (a+= (+= (c+= (a+= (+= (c+= (a+ ~!= c+= e ) ) ) ) ) ) ) ) )
    where e = a+ ~!= =+ (~~ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r) !! ) ) )

  open M=1+M+M²

  M²=2M²+1 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
  -- M²=2M²+1 = t= e3 (s= {! t=   !} ) -- (s= (t= (=+ (t= (×= M²=M³+M²+M ) {!   !} )  ) {!   !} ) )
  M²=2M²+1 = t= e3 (s= (t= (=+ (t= (×= M²=M³+M²+M ) (s= (X+X=2X _ ) ) )  )
    (t= (a+= (a+= (+= (c+= (a+= (a+= (+= (a+= (+= (c+= (a+= (c+= (a+= (a+= (+= r= ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) e) ) )
    where e = s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) )

  M²=2M²+1v2 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
  M²=2M²+1v2 = c× =!= M²=2M²+1

  sM² : ADT 0
  sM² = s [ M ² ]

  sM²=M² : Iso sM² (M ²)
  sM²=M² = ~~ M²=2M²+1

  sM²=M²v2 : Iso sM² (M ²)
  sM²=M²v2 = ~~ M²=2M²+1v2

  sM²=M²v3 : Iso sM² (M ²)
  sM²=M²v3 = =+ (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) r=) ) =!= a+= (=+ (×= (fix≃ m) =!= dl= (cong+= i×r (dl ) r=) ) =!= a+= (+= (a+ ) =!= c+= (a+= (+= (a+= (+= (a+= (c+= (a+= (~~ (fix≃ m) ) ) ) ) ) ) =!= c+= (a+= (=+ (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (+= (c×= (a×) ) ) ) r=) ) =!= a+= (+= (a+= (c+= (a+= (+= (a+) =!= (a+ ~!= (=+ (c+) =!= a+= (+= (c+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (~~ a× ) (~~ dl)) (dl ~!= (×= (~~ (fix≃ m)) =!= a×) )) ) ) ) ) ) ) ) ) ) =!= c+= (a+= (+= c+ =!= cong+= (~~ i×r) (~~ dl ) (dl ~!= ×= (~~ (fix≃ m) ) ) ) ) ) ) ) ) )  ) )
  M²_t : Set
  M²_t = ⟦ M ² ⟧ Γ₀

  preimg :  M²_t → ⟦ sM² ⟧ Γ₀
  preimg mmmm = _≃_.f- (≃⟦ sM²=M² ⟧ Γ₀) mmmm

  what : Set
  what = {! _≃_.f-  (≃⟦ sM²=M²v2 ⟧ Γ₀) (Mleaf , Munode Mleaf) !}


  S→M² : ⟦ S ⟧ Γ₀ → ⟦ M ² ⟧ Γ₀
  S→M² = foldADT s (λ ()) (⟦ M ² ⟧ Γ₀) (_≃_.f+ (≃⟦ sM²=M² ⟧ Γ₀ ) )

  S→M²v2 : ⟦ S ⟧ Γ₀ → ⟦ M ² ⟧ Γ₀
  S→M²v2 = foldADT s (λ ()) (⟦ M ² ⟧ Γ₀) (_≃_.f+ (≃⟦ sM²=M²v2 ⟧ Γ₀ ) )

  S→M²v3 : ⟦ S ⟧ Γ₀ → ⟦ M ² ⟧ Γ₀
  S→M²v3 =  foldADT s (λ ()) (⟦ M ² ⟧ Γ₀) (_≃_.f+ (≃⟦ sM²=M²v3 ⟧ Γ₀ ) )

  SS : Set
  SS = ⟦ S ⟧ Γ₀

  Sλ : SS
  Sλ = lfp (in2 tt)
  S0 : SS → SS
  S0 s' = lfp (in1 ((in1 tt) , s' ) )
  S1 : SS → SS
  S1 s' = lfp (in1 ((in2 (in1 tt) ) , s' ) )

  stuff? : ⟦ M ² ⟧ Γ₀
  stuff? = {! S→M² (S0 (S0 (S0 Sλ)))  !}

  allS : ℕ → List SS
  allS 0 = []
  allS (succ n) = let
    un1 = List→ S0 (allS n)
    un2 = List→ S1 (allS n)
    in Sλ ∷ merge un1 un2

  allM² : ℕ → List M²_t
  allM² n = lazyProd (allM n) (allM n)


  ==S : SS → SS → 𝔹
  ==S (lfp (in1 (in1 tt , pr2))) (lfp (in1 (in1 tt , pr6))) = ==S pr2 pr6
  ==S (lfp (in1 (in1 tt , pr4))) (lfp (in1 (in2 (in1 x) , pr6))) = false
  ==S (lfp (in1 (in2 (in1 x) , pr4))) (lfp (in1 (in1 tt , pr6))) = false
  ==S (lfp (in1 (in2 (in1 tt) , pr4))) (lfp (in1 (in2 (in1 tt) , pr6))) = ==S pr4 pr6
  ==S (lfp (in1 x)) (lfp (in2 y)) = false
  ==S (lfp (in2 x)) (lfp (in1 y)) = false
  ==S (lfp (in2 tt)) (lfp (in2 tt)) = true

  StoString : SS → List ℕ
  StoString (lfp (in1 (in1 tt , pr4))) = 0 ∷ StoString pr4
  StoString (lfp (in1 (in2 (in1 tt) , pr4))) = 1 ∷ StoString pr4
  StoString (lfp (in2 tt)) = []

  ==M² : M²_t → M²_t → 𝔹
  ==M² (pr3 , pr4) (pr5 , pr6) = and (==M pr3 pr5) (==M pr4 pr6)

  hasBnode : MM → 𝔹
  hasBnode (lfp (in1 tt)) = false
  hasBnode (lfp (in2 (in1 (lfp x)))) = hasBnode (lfp x)
  hasBnode (lfp (in2 (in2 (pr3 , pr4)))) = true


  findm²? : M²_t → ℕ → 𝔹
  findm²? m² n = elem ==M² m² (List→ S→M²v3 (allS n))


  some_m² : List M²_t
  some_m² = take 1000 (allM² 10)

  notPass : ℕ → List M²_t
  notPass q = filter (λ x → not (findm²? x q)) some_m²

  pass0m² : List M²_t
  pass0m² = filter (λ x → (findm²? x 3)) some_m²

  pass1m² : List M²_t
  pass1m² = filter (λ x → findm²? x 4) pass0m²

  pass3m² : List M²_t
  pass3m² = filter (λ x → findm²? x 5) pass1m²

  passN : ℕ → List M²_t
  passN zero = some_m²
  passN (succ n) = filter (λ x → findm²? x (succ n)) (passN n)


  an_M² : M²_t
  an_M² = (lfp (in1 tt) , lfp (in2 (in2 (lfp (in1 tt) , lfp (in1 tt)))))

  check' : Set
  check' = {! List→ StoString (filter (λ z → f (S→M²v3 z)) (allS 10)) !} where
    f : M²_t → 𝔹
    f (m1 , m2) = not (hasBnode m2)

module prettyPrint where
  data 𝕄 : Set where
    l : 𝕄
    u : 𝕄 → 𝕄
    b : 𝕄 → 𝕄 → 𝕄

  open M=1+M+M²
  open S=1+2S

  M→𝕄 : MM → 𝕄
  M→𝕄 (lfp (in1 tt)) = l
  M→𝕄 (lfp (in2 (in1 x))) = u (M→𝕄 x)
  M→𝕄 (lfp (in2 (in2 (pr3 , pr4)))) = b (M→𝕄 pr3 ) (M→𝕄 pr4)

  𝕄→M : 𝕄 → MM
  𝕄→M l = lfp (in1 tt)
  𝕄→M (u mm) = lfp (in2 (in1 (𝕄→M mm) ))
  𝕄→M (b mm1 mm2) = lfp (in2 (in2 ((𝕄→M mm1) , 𝕄→M mm2 ) ))

  M²→𝕄² : M²_t → 𝕄 ∧ 𝕄
  M²→𝕄² (pr3 , pr4) = (M→𝕄 pr3) , (M→𝕄 pr4)

  𝕄²→M² : 𝕄 ∧ 𝕄 → M²_t
  𝕄²→M² (pr3 , pr4) = (𝕄→M pr3 ) , 𝕄→M pr4

  check37 : Set
  check37 = {! List→ M²→𝕄² (notPass 6)  !}

  check4 : Set
  check4 = {! List→ (f ∘ preimg) (passN 5)  !} where
    f : ⟦ sM² ⟧ Γ₀ → ↑ (𝔹 ∧ (𝕄 ∧ 𝕄))
    f (in1 (in1 tt , m2)) = i (false , M²→𝕄² m2 )
    f (in1 (in2 (in1 tt) , pr4)) = i (true , M²→𝕄² pr4 )
    f (in2 tt) = o


module JX=1+2X+X² where
  j : ADT 1
  j = 𝟏 ⊔ (𝕍 o) ⊔ (𝕍 o) ⊔ (𝕍 o) ²

  J : ADT 0
  J = μ j

  JJ : Set
  JJ = ⟦ J ⟧ Γ₀

  Jleaf : JJ
  Jleaf = lfp (in1 tt)
  Junode1 : JJ → JJ
  Junode1 x = lfp (in2 (in1 x ) )
  Junode2 : JJ → JJ
  Junode2 x = lfp (in2 (in2 (in1 x)))
  Jbnode : JJ → JJ → JJ
  Jbnode x1 x2 = lfp (in2 (in2 (in2 (x1 , x2))))
  JbnodeCurried : JJ ∧ JJ → JJ
  JbnodeCurried (x1 , x2) = lfp (in2 (in2 (in2 (x1 , x2))))

  allJ : ℕ → List JJ
  allJ zero = []
  allJ (succ n) = let
    un1 = List→ Junode1 (allJ n)
    un2 = List→ Junode2 (allJ n)
    allJ² : List (JJ ∧ JJ)
    allJ² = lazyProd (allJ n) (allJ n)
    bn = List→ JbnodeCurried allJ²
    in Jleaf ∷ merge (merge un1 un2) bn

  ==J : JJ → JJ → 𝔹
  ==J (lfp (in1 x)) (lfp (in1 x₁)) = true
  ==J (lfp (in1 x)) (lfp (in2 x₁)) = false
  ==J (lfp (in2 x)) (lfp (in1 x₁)) = false
  ==J (lfp (in2 (in1 x))) (lfp (in2 (in1 x₁))) = ==J x x₁
  ==J (lfp (in2 (in1 x))) (lfp (in2 (in2 x₁))) = false
  ==J (lfp (in2 (in2 (in1 x)))) (lfp (in2 (in1 x₁))) = ==J x x₁
  ==J (lfp (in2 (in2 (in1 x)))) (lfp (in2 (in2 x₁))) = false
  ==J (lfp (in2 (in2 (in2 x)))) (lfp (in2 (in1 x₁))) = false
  ==J (lfp (in2 (in2 (in2 x)))) (lfp (in2 (in2 (in1 x₁)))) = false
  ==J (lfp (in2 (in2 (in2 (pr3 , pr4))))) (lfp (in2 (in2 (in2 (pr5 , pr6))))) = and (==J pr3 pr5) (==J pr4 pr6)

  jJ²=J² : Iso (j [ J ² ]) (J ²)
  jJ²=J² = += (=+ (×= (fix≃ j ) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) =!= += (=+ (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) ) ) =!= (+= (a+= (+= (a+= (+= (a+= (+= (+= (a+= (+= (a+=  (+= (a+= (+= (+= (a× ) ) ) ) ) ) ) ) ) ) ) )  ) ) ) =!=  (+= (+= (+= (c+= (=+ (c+= (a+= (+= (a+= (+= (c+= (a+ ~!= (a+ ~!= (=+ (=+ c+ ) =!= a+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (cong+ (~~ a×) (~~ a×) ) (+= (~~ dl) =!= ~~ dl )) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) )  ) ) ) ) ) ) ) ) ) ) ) =!= ( (a+ ~!= (a+ ~!= (a+ ~!= =+ (a+ ~!= =+ (a+= (a+= (+= (+= c+ ) =!= ~~ (fix≃ j) ) ) ) ) ) ) ) =!= a+= (+= (c+= (cong+= r= (+= a× =!= ~~ dl ) (~~ dl)) ) =!= (=+ (~~ i×r) =!= (dl ~!= ×= (~~ (fix≃ j) ) )  ) ) ) ) )

  jJ²→J² : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  jJ²→J² = foldADT j Γ₀ (⟦ J ² ⟧ Γ₀) (_≃_.f+ (≃⟦ jJ²=J² ⟧ Γ₀))


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

  BT→TT→BT : ∀ b → TT→BT (BT→TT b) ≡ b
  BT→TT→BT BTleaf = refl
  BT→TT→BT (BTnode b1 BTleaf) = cong (λ x → BTnode x BTleaf) (BT→TT→BT b1)
  BT→TT→BT (BTnode b1 (BTnode b2 b3)) = cong3 (λ x y z → BTnode x (BTnode y z)) (BT→TT→BT b1) (BT→TT→BT b2) (BT→TT→BT b3)

  TT→BT→TT : ∀ t → BT→TT (TT→BT t) ≡ t
  TT→BT→TT TTleaf = refl
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

  foldT : ∀ (X : Set) → (t-func X → X) → ⟦ T ⟧ Γ₀ → X
  foldT X Xalg (lfp (in1 tt)) = Xalg (in1 tt)
  foldT X Xalg (lfp (in2 (in1 x))) = Xalg (in2 (in1 (foldT X Xalg x ) ) )
  foldT X Xalg (lfp (in2 (in2 (x1 , (x2 , x3)))))
    = Xalg (in2 (in2 ((fT x1) , ((fT x2) , fT x3 ) ) ) ) where fT = foldT X Xalg
  -- foldT X = fold {F = t-func} λ {A} {B} f → ⟦ t ⟧→ {!   !}

  T→B : ⟦ T ⟧ Γ₀  → ⟦ B ⟧ Γ₀
  T→B = foldADT t (λ ()) (⟦ B ⟧ Γ₀) ((_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ )))
  -- foldT (⟦ B ⟧ Γ₀) (_≃_.f+ (≃⟦ tB=B ⟧ Γ₀ ) )


-- Iso ((𝟏 ⊔ 𝟎) × A × B ⊔ A × B) ((𝟏 ⊔ 𝟏 ⊔ 𝟎) × A × B)
-- Iso (1+ (1+ 𝟎) × A × B) (1+ 𝟎 × A × B ⊔ A × B)

𝔹≃𝔹₁ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₁ = !!
𝔹≃𝔹₂ : ∀ {n} → Iso (Num {n} 2) (Num 2)
𝔹≃𝔹₂ = a+ ~!= i+r= (c+= (!+ (~~ i+r) ) )
-- 𝔹≃𝔹₂ = c+= (cong+ i+r (~~ i+r) )
-- 𝔹≃𝔹₂ = c+= (a+= (!+ c+ ) )

iso≠lemma : ∀ {A B : Set} (i1 i2 : A ≃ B) → ∀ (a : A) → ¬ (_≃_.f+ i1 a ≡ _≃_.f+ i2 a) → ¬ (i1 ≡ i2)
iso≠lemma i1 .i1 a neq (refl) = neq (refl )

𝔹1≠𝔹2 : ¬ (≃⟦ 𝔹≃𝔹₁ ⟧ Γ₀ ≡ ≃⟦ 𝔹≃𝔹₂ ⟧ Γ₀)
𝔹1≠𝔹2 i1=i2 = iso≠lemma (≃⟦ 𝔹≃𝔹₁ ⟧ Γ₀) (≃⟦ 𝔹≃𝔹₂ ⟧ Γ₀) (in1 tt) (λ {()} ) i1=i2

module X=X^4 where

  -- Q: Can we prove X = X² or is that not a rig iso?

  ∛1 : ADT 0
  ∛1 = μ ((1+ (𝕍 (o))) ²)

  X : ADT 0
  X = ∛1

  skel : ADT 1
  skel = (1+ ((wk (o) X) × (𝕍 (o)))) ²

  -- 1+X^2=1+X[1+X^2] : Iso (1+ (X ²)) (1+ (X × (1+ (X ²))))
  -- 1+X^2=1+X[1+X^2] = subst≃ {0} {skel} {skel} {X} {1+ (X ²)} (refl≃ skel) (fix≃ ((1+ (𝕍 (o))) ²))

  1+X²≃1+X[1+X²] : Iso (1+ (X ²)) (1+ (X × (1+ X ²)))
  1+X²≃1+X[1+X²] = {!   !} -- subst≃ {0} {skel} {skel} {X} {1+ X ²} (refl≃ skel) (fix≃ ((1+ (𝕍 (o))) ²) )

  X=1+X+X^2 : Iso X (1+ (X ⊔ (X ²)))
  X=1+X+X^2 = fix≃ ((1+ (𝕍 (o))) ²) =!= {!   !}

exsub : ADT 1
exsub = μ (𝟏 ⊔ (𝕍 (o) × 𝕍 (i (o ) ) )) ⊔ (𝕍 (o))

ex2sub : ADT 1
ex2sub = (𝟏 ⊔ 𝕧₀)

Nat' : ADT 0
Nat' = μ (𝟏 ⊔ 𝕧₀ )

List' : ADT 1
List' = μ (𝟏 ⊔ (𝕍 (i (o)) × 𝕍 (o) ) )

Nat : Set
Nat = ⟦ Nat' ⟧ Γ₀

one : Nat
one = lfp (in2 (lfp (in1 tt ) ) )
