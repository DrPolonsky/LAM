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
  ==G = ==ADT {G}

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
  ==M = ==ADT {M}

  open G=1+2G+G²+G³

  gM : ADT 0
  gM = g [ M ]

  gM=M : Iso gM M
  -- gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= i×r ar i+r ) !! )) =!= a+= (+= e ) ) ) )
  gM=M = ~~ (fix≃ m =!= += (~~ (=+ (c×= (dist3 =!= cong+= i×r (cong+= !! ar i+r) !! )) =!= a+= (+= e ) ) ) )
    where  e = dist3 ~!= ×= (~~ (fix≃ m ) )

  G→M : ⟦ G ⟧ Γ₀  → ⟦ M ⟧ Γ₀
  G→M = RigFold g M gM=M

  findm : MM → ℕ → 𝔹
  findm m n = elem ==M m (List→ G→M (allG n))

  cn : ∀ {A : Set} → ℕ → (A → A) → A → A
  cn {A} zero f x = x
  cn {A} (succ n) f x = f (cn n f x)

  bigM : MM
  bigM = cn 7 (Mbnode Mleaf) Mleaf

  -- take 100 (allM 4) works
  -- take 100 (allM 5) works
  20ms : List MM
  20ms = take 20 (allM 6)

  passNm : ℕ → List MM
  passNm zero = 20ms
  passNm (succ n) = filter (λ x → findm x (succ n)) (passNm n)

  -- why does it stop at a number? agda limitation? or the way allM is generated?
  -- test = {! length (filter (λ {(x , y) → ==M x y})  (zip (take 1000000 (allM 5)) (take 1000000 (allM 6))))  !}


  h : ⟦ G ⟧ Γ₀ → ⟦ M ⟧ Γ₀
  h x = fold {λ X → ⟦ g ⟧ (Γ₀ ⅋o:= X)} (λ j →  ⟦ g ⟧→ (λ tt → j)) (_≃_.f+ (≃⟦ gM=M ⟧ Γ₀ ) ) x

  M²=M+M²+M³ : Iso (M ²) (M ⊔ M ² ⊔ M ³)
  M²=M+M²+M³ = t= (t= (×= (fix≃ m)) (dist3) ) (∨≃ (c×= (i×l= r= ) ) r=  )  -- (s= {! dist3   !} )

  M²=M³+M²+M : Iso (M ²) (M ³ ⊔ M ² ⊔ M)
  M²=M³+M²+M = t= M²=M+M²+M³ (c+= (t= (=+ (c+= r= )) (a+= r=) ) )

  M²=1+2M+2M²+2M³ : Iso (M ²) (M ³ ⊔ M ³ ⊔ M ² ⊔ M ² ⊔ M ⊔ M ⊔ 𝟏)
  M²=1+2M+2M²+2M³  = t= M²=M³+M²+M (+= (t= (=+ M²=M³+M²+M ) (a+= (+= (a+= (+= e ) ) ) ) ) )
    where e = t= (+= (fix≃ m ) ) (s= (t= cycle+ (+= (t= (=+ (c+= r= ) ) (a+= r=) ) ) ) )

  e3 : Iso (M ²) ((M ³ ⊔ M ³) ⊔ ( M ² ⊔ M ²) ⊔ (M ⊔ M) ⊔ 𝟏)
  e3 = t= M²=1+2M+2M²+2M³ (s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) ) )

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

  3+S→ : ⟦ 1+ 2+S ⟧ Γ₀ → ⟦ 2+S ⊔ 2+S ⟧ Γ₀
  3+S→ = _≃_.f+ (≃⟦ S+3=2S+4 ⟧ Γ₀)

  open M=1+M+M²

  sM² : ADT 0
  sM² = s [ M ² ]

  sM²=M² : Iso sM² (M ²)
  sM²=M² = ~~ (t= e3 (s= (t= (=+ (t= (×= M²=M³+M²+M ) (s= (X+X=2X _ ) ) )  ) (t= (a+= (a+= (+= (c+= (a+= (a+= (+= (a+= (+= (c+= (a+= (c+= (a+= (a+= (+= r= ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) e) ) ))
    where e = s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) )

  M²=2M²+1v2 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
  M²=2M²+1v2 = c× =!~ sM²=M²

  sM²=M²v2 : Iso sM² (M ²)
  sM²=M²v2 = ~~ M²=2M²+1v2

  sM²=M²v3 : Iso sM² (M ²)
  sM²=M²v3 = =+ (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) r=) ) =!= a+= (=+ (×= (fix≃ m) =!= dl= (cong+= i×r (dl ) r=) ) =!= a+= (+= (a+ ) =!= c+= (a+= (+= (a+= (+= (a+= (c+= (a+= (~~ (fix≃ m) ) ) ) ) ) ) =!= c+= (a+= (=+ (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (+= (c×= (a×) ) ) ) r=) ) =!= a+= (+= (a+= (c+= (a+= (+= (a+) =!= (a+ ~!= (=+ (c+) =!= a+= (+= (c+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (~~ a× ) (~~ dl)) (dl ~!= (×= (~~ (fix≃ m)) =!= a×) )) ) ) ) ) ) ) ) ) ) =!= c+= (a+= (+= c+ =!= cong+= (~~ i×r) (~~ dl ) (dl ~!= ×= (~~ (fix≃ m) ) ) ) ) ) ) ) ) )  ) )

  MM² : Set
  MM² = ⟦ M ² ⟧ Γ₀

  preimg :  MM² → ⟦ sM² ⟧ Γ₀
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

  allM² : ℕ → List MM²
  allM² n = lazyProd (allM n) (allM n)

  ==S : SS → SS → 𝔹
  ==S = ==ADT {S}

  ==2+S : ⟦ 2+S ⊔ 2+S ⟧ Γ₀ → ⟦ 2+S ⊔ 2+S ⟧ Γ₀ → 𝔹
  ==2+S = ==ADT {2+S ⊔ 2+S}

  some2+S : List (⟦ 1+ 2+S ⟧ Γ₀)
  some2+S = in1 tt ∷ in2 (in1 tt) ∷ in2 (in2 (in1 tt)) ∷ List→ (in2 ∘ (in2 ∘ in2)) (allS 10)

  find-the-y : List (⟦ 1+ 2+S ⟧ Γ₀)
  find-the-y = filter p some2+S where
    p : ⟦ 1+ 2+S ⟧ Γ₀ → 𝔹
    p (in1 y) = false
    p (in2 y) = not (or (==2+S (3+S→ (in2 y)) (in1 y)) (==2+S (3+S→ (in2 y)) (in2 y)))

  checky : Set
  checky = {! find-the-y  !}

  StoString : SS → List ℕ
  StoString (lfp (in1 (in1 tt , pr4))) = 0 ∷ StoString pr4
  StoString (lfp (in1 (in2 (in1 tt) , pr4))) = 1 ∷ StoString pr4
  StoString (lfp (in2 tt)) = []

  ==M² : MM² → MM² → 𝔹
  ==M² = ==ADT {M ²}

  hasBnode : MM → 𝔹
  hasBnode (lfp (in1 tt)) = false
  hasBnode (lfp (in2 (in1 (lfp x)))) = hasBnode (lfp x)
  hasBnode (lfp (in2 (in2 (pr3 , pr4)))) = true


  findm² : MM² → ℕ → 𝔹
  findm² m² n = elem ==M² m² (List→ S→M²v3 (allS n))


  some_m² : List MM²
  some_m² = take 1000 (allM² 10)

  notPass : ℕ → List MM²
  notPass q = filter (λ x → not (findm² x q)) some_m²

  passN : ℕ → List MM²
  passN zero = some_m²
  passN (succ n) = filter (λ x → findm² x (succ n)) (passN n)


  an_M² : MM²
  an_M² = (lfp (in1 tt) , lfp (in2 (in2 (lfp (in1 tt) , lfp (in1 tt)))))

  check' : Set
  check' = {! List→ StoString (filter (λ z → f (S→M²v3 z)) (allS 10)) !} where
    f : MM² → 𝔹
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

  M²→𝕄² : MM² → 𝕄 ∧ 𝕄
  M²→𝕄² (pr3 , pr4) = (M→𝕄 pr3) , (M→𝕄 pr4)

  𝕄²→M² : 𝕄 ∧ 𝕄 → MM²
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

  allJ² : ℕ → List (JJ ∧ JJ)
  allJ² n = lazyProd (allJ n) (allJ n)

  ==J : JJ → JJ → 𝔹
  ==J = ==ADT {J}

  ==J² : ⟦ J ² ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀ → 𝔹
  ==J² = ==ADT {J ²}

  jJ²=J² : Iso (j [ J ² ]) (J ²)
  jJ²=J² = += (=+ (×= (fix≃ j ) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) =!= += (=+ (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) ) ) =!= (+= (a+= (+= (a+= (+= (a+= (+= (+= (a+= (+= (a+=  (+= (a+= (+= (+= (a× ) ) ) ) ) ) ) ) ) ) ) )  ) ) ) =!=  (+= (+= (+= (c+= (=+ (c+= (a+= (+= (a+= (+= (c+= (a+ ~!= (a+ ~!= (=+ (=+ c+ ) =!= a+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (cong+ (~~ a×) (~~ a×) ) (+= (~~ dl) =!= ~~ dl )) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) )  ) ) ) ) ) ) ) ) ) ) ) =!= ( (a+ ~!= (a+ ~!= (a+ ~!= =+ (a+ ~!= =+ (a+= (a+= (+= (+= c+ ) =!= ~~ (fix≃ j) ) ) ) ) ) ) ) =!= a+= (+= (c+= (cong+= r= (+= a× =!= ~~ dl ) (~~ dl)) ) =!= (=+ (~~ i×r) =!= (dl ~!= ×= (~~ (fix≃ j) ) )  ) ) ) ) )

  jJ²=J²v2 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v2 = jJ²=J² =!= c×


  -- 𝟏 ⊔ J × (unfold J) ⊔ J × (unfold J) ⊔ (J × J) × J × J
  jJ²=J²v3 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v3 = += (a+ ~!= =+ (cong+= (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!) ) (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) ) ) ) =!= ((a+ ~!= =+ (a+ ~!= (a+ ~!= (+= (c+= (a+= (c+= (a+= (a+= !! ) )  ) ) ) =!= (a+ ~!= =+ (a+= (+= c+ =!= a+= (~~ (fix≃ j) ) ) ) ) ) ) ) ) =!= (a+= (+= (a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (cong+= (~~ i×r ) (cong+= (~~ a×) (~~ a×) (~~ dl) ) (~~ dl)) ) ) =!= ~~ dl) ) ) ) ) ) ) =!= (+= (+= (+= (×= (a+= (+= a+  =!= ~~ (fix≃ j) ) )  =!= a× ) ) ) =!= cong+= (~~ i×r) (cong+= !! (cong+= !! !! (~~ dl)) (~~ dl)) (~~ dl =!= ×= (~~ (fix≃ j) ) ) )) ) )

  -- j3 but commute the J×J terms before unfold
  jJ²=J²v4 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v4 = += (a+ ~!= =+ (cong+= (c×= (×= (fix≃ j) )  =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!) ) ( c×= (×= (fix≃ j)) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) ) ) ) =!= ((a+ ~!= =+ (a+ ~!= (a+ ~!= (+= (c+= (a+= (c+= (a+= (a+= !! ) )  ) ) ) =!= (a+ ~!= =+ (a+= (+= c+ =!= a+= (~~ (fix≃ j) ) ) ) ) ) ) ) ) =!= (a+= (+= (a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (cong+= (~~ i×r ) (cong+= (~~ a×) (~~ a×) (~~ dl) ) (~~ dl)) ) ) =!= ~~ dl) ) ) ) ) ) ) =!= (+= (+= (+= (×= (a+= (+= a+  =!= ~~ (fix≃ j) ) )  =!= a× ) ) ) =!= cong+= (~~ i×r) (cong+= !! (cong+= !! !! (~~ dl)) (~~ dl)) (~~ dl =!= ×= (~~ (fix≃ j) ) ) )) ) )

  -- 𝟏 ⊔ (unfold J) × J ⊔ (unfold J) × J ⊔ (J × J) × J × J
  jJ²=J²v5 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v5 = += (a+ ~!= =+ (cong+= (=× (fix≃ j) =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) ) ) (=× (fix≃ j)  =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) )) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) )) ) =!= (+= (a+=  (+= (=+ (a+ ~!= (a+ ~!= (a+ ~!= =+ c+ ) ) ) ) ) ) =!= (+= (+= (a+= (a+= (+= (a+= (a+= !! ) ) ) ) ) ) =!= (a+ ~!= (a+ ~!= (a+ ~!= (=+ (a+= (a+= (~~ (fix≃ j) ) ) ) =!= (+= (+= (a+ ~!= (=+ (a+ ~!= =+ c+ ) =!= a+= (a+= (+= (a+ ~!= (=+ (a+ ~!= =+ c+ ) =!= a+= (a+= (cong+= (~~ i×r) (cong+= !! (~~ dl ) (~~ dl)) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) ) ) ) ) ) ) =!= cong+= (~~ i×r) (+= (+= (a× ) =!= ~~ dl ) =!= ~~ dl ) (dl ~!= ×= (~~ (fix≃ j) ) ) ) ) ) ) ) ) )

  -- 𝟏 ⊔ (unfold J) × J ⊔ J × (unfold J) ⊔ (J × J) × J × J
  jJ²=J²v6 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v6 = += (a+ ~!= =+ (cong+= (=× (fix≃ j) =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) )) (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) a+) ) =!= (+= (a+= (+= (a+= (a+= (+= (a+ ~!= =+ (a+ ~!= =+ c+ ) ) =!= (a+ ~!= =+ (a+ ~!= =+ (a+ ~!= =+ c+ ) ) ) ) ) ) ) ) =!= (a+ ~!= (a+ ~!= (=+ (a+ ~!= =+ (a+ ~!= =+ (a+= (~~ (fix≃ j) ) )  ) ) =!= a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (+= (a+= (+= c+ ) ) ) ) ) =!= a+= (+= (a+= (cong+= (~~ i×r) (a+= (cong+= !! (cong+= (~~ a×) !! (~~ dl)) (~~ dl)) ) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) ) ) ) ) =!= cong+= (~~ i×r) (+= (+= a× =!= ~~ dl ) =!= ~~ dl ) (dl ~!= ×= (~~ (fix≃ j)) ) ) ) ) ) ) )

  -- 𝟏 ⊔ J × (unfold J) ⊔ (unfold J) × J ⊔ (J × J) × J × J
  jJ²=J²v7 : Iso (j [ J ² ]) (J ²)
  jJ²=J²v7 = += (a+ ~!= =+ (cong+= (×= (fix≃ j) =!= dl= (cong+ i×r (dl= (+= (dl= !! ) ) ) ) ) (=× (fix≃ j) =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) ) ) (a+= (+= (a+= (+= (a+= !! ) ) ) ) )) ) =!= (+= (a+= (+= (a+= (+= (a+= (+= (a+= (+= (a+= !! ) =!= c+= (a+= (+= (c+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) ) ) ) ) ) =!= (a+ ~!= =+ c+ ) ) ) =!= (a+ ~!= =+ (a+ ~!= =+ c+ ) ) ) ) ) ) =!= (a+ ~!= (a+ ~!= (=+ (a+ ~!= =+ (a+= (~~ (fix≃ j) ) )  ) =!= (+= (a+ ~!= (=+ c+ =!= a+= (+= (a+ ~!= (=+ c+ =!= a+= (cong+= (~~ i×r ) (cong+= (~~ a× ) (~~ dl ) (~~ dl )) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) ) ) ) =!= a+= (cong+= (~~ i×r ) (cong+= !! (+= a× =!= ~~ dl ) (~~ dl)) (dl ~!= ×= (~~ (fix≃ j)) )) ) ) ) ) )

  J→J² : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J² = RigFold j (J ²) jJ²=J²

  J→J²v2 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v2 = RigFold j (J ²) jJ²=J²v2

  J→J²v3 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v3 = RigFold j (J ²) jJ²=J²v3

  J→J²v4 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v4 = RigFold j (J ²) jJ²=J²v4

  J→J²v5 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v5 = RigFold j (J ²) jJ²=J²v5

  J→J²v6 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v6 = RigFold j (J ²) jJ²=J²v6

  J→J²v7 : ⟦ J ⟧ Γ₀ → ⟦ J ² ⟧ Γ₀
  J→J²v7 = RigFold j (J ²) jJ²=J²v7

  findj² : ⟦ J ² ⟧ Γ₀ → ℕ → 𝔹
  findj² j² n = elem ==J² j² (List→ J→J²v6 (allJ n))


  some_j² : List (⟦ J ² ⟧ Γ₀)
  some_j² = take 50 (allJ² 10)

  passNj² : ℕ → List (⟦ J ² ⟧ Γ₀)
  passNj² zero = some_j²
  passNj² (succ n) = filter (λ x → findj² x (succ n)) (passNj² n)

  notPassj : ℕ → List (⟦ J ² ⟧ Γ₀)
  notPassj 0 = []
  notPassj (succ n) = filter (λ x → not (findj² x (succ n))) some_j²

  data 𝕁 : Set where
    jl : 𝕁
    ju1 : 𝕁 → 𝕁
    ju2 : 𝕁 → 𝕁
    jb : 𝕁 → 𝕁 → 𝕁

  J→𝕁 : JJ → 𝕁
  J→𝕁 (lfp (in1 tt)) = jl
  J→𝕁 (lfp (in2 (in1 x))) = ju1 (J→𝕁 x)
  J→𝕁 (lfp (in2 (in2 (in1 x)))) = ju2 (J→𝕁 x)
  J→𝕁 (lfp (in2 (in2 (in2 (pr3 , pr4))))) = jb (J→𝕁 pr3) (J→𝕁 pr4)

  𝕁→J : 𝕁 → JJ
  𝕁→J jl = Jleaf
  𝕁→J (ju1 x) = Junode1 (𝕁→J x)
  𝕁→J (ju2 x) = Junode2 (𝕁→J x)
  𝕁→J (jb x x₁) = Jbnode (𝕁→J x) (𝕁→J x₁)

  J²→𝕁² : (JJ ∧ JJ) → 𝕁 ∧ 𝕁
  J²→𝕁² (x , y) = (J→𝕁 x) , (J→𝕁 y)

  𝕁²→J² : 𝕁 ∧ 𝕁 → JJ ∧ JJ
  𝕁²→J² (pr3 , pr4) = (𝕁→J pr3) , (𝕁→J pr4)

  depthJ : JJ → ℕ
  depthJ (lfp (in1 tt)) = 0
  depthJ (lfp (in2 (in1 x))) = succ (depthJ x)
  depthJ (lfp (in2 (in2 (in1 x)))) = succ (depthJ x)
  depthJ (lfp (in2 (in2 (in2 (pr3 , pr4))))) = succ (max (depthJ pr3) (depthJ pr4))



  check'''' : Set
  check'''' = {! length (filter (λ x → not (eqℕ x 2)) (List→ depthJ (allJ 5)))  !} -- {! take 100 (filter (λ x → not (le 5 (depthJ x)) (allJ 5))   !} -- {! List→ J²→𝕁² (passNj² 4)  !}

  chek : Set
  chek = {! findj² (𝕁²→J² (jl , jb (ju1 jl) jl)) 5  !}

  check''' : Set
  check''' = {! List→ J→𝕁 (take 100 (allJ 6))  !}

  check'' : Set
  check'' = {! List→ J²→𝕁² (List→ J→J²v7 (take 100 (allJ 6)))  !}

module N=N+N where
  f : ADT 1
  f = 𝟏 ⊔ 𝕧₀

  g : ADT 1
  g = 𝟏 ⊔ 𝟏 ⊔ 𝕧₀

  F : ADT 0
  F = μ f

  G : ADT 0
  G = μ g

  gF=F : Iso (g [ F ]) F
  gF=F = ~~ (fix≃ _ =!= += (fix≃ _) )

  gF=Fv2 : Iso (g [ F ]) F
  gF=Fv2 = a+ ~!= (=+ c+ =!= a+= gF=F )

  gF=Fv3 : Iso (g [ F ]) F
  gF=Fv3 = {!   !}

  G→F : ⟦ G ⟧ Γ₀ → ⟦ F ⟧ Γ₀
  G→F = RigFold g F gF=F

  G→Fv2 : ⟦ G ⟧ Γ₀ → ⟦ F ⟧ Γ₀
  G→Fv2 = RigFold g F gF=Fv2

  data 𝔾 : Set where
    Z : 𝔾
    Z' : 𝔾
    S : 𝔾 → 𝔾

  𝔾→G : 𝔾 → ⟦ G ⟧ Γ₀
  𝔾→G Z = lfp (in2 (in1 tt))
  𝔾→G Z' = lfp (in1 tt)
  𝔾→G (S x) = lfp (in2 (in2 (𝔾→G x) ) )

  F→ℕ : ⟦ F ⟧ Γ₀ → ℕ
  F→ℕ (lfp (in1 tt)) = 0
  F→ℕ (lfp (in2 x)) = succ (F→ℕ x)

  ℕ→𝔾 : ℕ → 𝔾
  ℕ→𝔾 zero = Z
  ℕ→𝔾 (succ zero) = Z'
  ℕ→𝔾 (succ (succ n)) = S (ℕ→𝔾 n )

  ℕ→G : ℕ → ⟦ G ⟧ Γ₀
  ℕ→G = 𝔾→G ∘ ℕ→𝔾

  [1-n]G : ℕ → List (⟦ G ⟧ Γ₀)
  [1-n]G zero = []
  [1-n]G (succ n) = ℕ→G n ∷ [1-n]G n

  check5 : Set
  check5 = {! List→ (F→ℕ ∘ G→F) ([1-n]G 30)  !}

module PX=X^2+1 where
  p : ADT 1
  p = 𝕧₀ ² ⊔ 𝟏

  Ψ : ADT 1
  Ψ = p ⊔ 𝕧₀

  ϕ : ADT 1
  ϕ = Num 3 × p ⊔ 𝕧₀

  μϕ : ADT 0
  μϕ = μ ϕ

  μΨ : ADT 0
  μΨ = μ Ψ

  ϕμΨ=μΨ : Iso (ϕ [ μΨ ]) (μΨ)
  ϕμΨ=μΨ = =+ (dr= (cong+= i×l (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) !!) ) !!) ) =!= a+= (+= (a+= (+= (a+= (~~ (fix≃ Ψ =!= a+ ) ) ) =!= ~~ (fix≃ Ψ) ) ) =!= ~~ (fix≃ Ψ) )

  μϕ→μΨ : ⟦ μϕ ⟧ Γ₀ → ⟦ μΨ ⟧ Γ₀
  μϕ→μΨ = RigFold ϕ μΨ ϕμΨ=μΨ

  Enum : Set → Set
  Enum A = List A

  EnumEnv : ∀ {n} → SetEnv n → Set
  EnumEnv Γ = ∀ x → Enum (Γ x)

  {-# TERMINATING #-}
  EnumADT : ∀ {n} → (e : ADT n) → (Γ : SetEnv n) → EnumEnv Γ → Enum (⟦ e ⟧ Γ)
  EnumADT (𝕍 x) Γ GG = GG x
  EnumADT 𝟎 Γ GG = []
  EnumADT 𝟏 Γ GG = tt ∷ []
  EnumADT (e1 × e2) Γ GG = lazyProd (EnumADT e1 Γ GG) ((EnumADT e2 Γ GG))
  EnumADT (e1 ⊔ e2) Γ GG = (List→ in1 (EnumADT e1 Γ GG)) ++ (List→ in2 (EnumADT e2 Γ GG))
  EnumADT (μ e) Γ GG with EnumADT e (Γ ⅋o:= (⟦ (μ e) ⟧ Γ) ) (io𝓟 _ GG (EnumADT (μ e) Γ GG))
    -- where f = λ { (i x) → GG x ; o → EnumADT (μ e) Γ GG }
  ... | c = List→ lfp c

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
