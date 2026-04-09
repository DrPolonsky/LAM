open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_ ; K to Kcomb)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

module QADT.Examples.Demo2 where

k : ADT (↑ ⊥)
k = (𝕧₀ ²) ⊔ 𝕧₀ ⊔ (𝟏 ⊔ 𝟏)

K : ADT ⊥
K = μ k

zK : ADT ⊥
zK = K ² ⊔ (𝟏 ⊔ 𝟏)

l : ADT (↑ ⊥)
l = 𝕧₀ ² ⊔ 𝕧₀ ⊔ 𝕧₀ ⊔ 𝟏

L : ADT ⊥
L = μ l

zL : ADT ⊥
zL = L ² ⊔ L ⊔ 𝟏

z : ADT ⊥
z = zK × zL

zK=2zK : Iso zK (zK ⊔ zK)
zK=2zK = =+ (×= (fix≃ k) =!= dl= (+= dl ) ) =!= a+= (+= (a+= (+= (=+ (dl= (cong+ i×r i×r ) ) =!= (=+ (+= (fix≃ k) ) =!= a+= (+= (=+ (c+= (a+= !! ) ) =!= a+= !! ) ) ) ) =!= cong+= !! (a+ ~!= =+ (cong+= (~~ i×r) (~~ i×r) (~~ dl)) ) (a+ ~!= =+ (~~ dl) )  ) ) =!= (a+ ~!= (=+ (dl ~!= ×= (~~ (fix≃ k) ) ) =!= (+= (cong+= c+ !! c+) =!= (a+ ~!= !! ) ) ) ))

KzK=zK : Iso (K × zK) zK
KzK=zK = dl= (+= (dl= (+= (i×r= (fix≃ k) ) =!= !! ) ) =!= (+= (+= (c+= (a+= (=+ (~~ i×r) =!= !! ) ) ) =!= (a+ ~!= =+ (~~ dl) ) ) =!= (a+ ~!= cong+= (~~ dl) !! (c+= (a+= (c+= (=+ (dl ~!= ×= (c+= (a+= (cong+= !! c+ (~~ (fix≃ k) )) ) ) ) =!= !!) ) ) ) ) ) )

KⁿzK=zK : {n : ℕ} → Iso ((Pow' K n) × zK) zK
KⁿzK=zK {zero} = i×l
KⁿzK=zK {succ zero} = KzK=zK
KⁿzK=zK {succ (succ n)} = a×= (c×= (a×= (cong×= !! (c×= KzK=zK ) (KⁿzK=zK {succ n})) ) )

nzK=zK : {n : ℕ} → Iso ((Num' (succ n)) × zK) zK
nzK=zK {zero} = i×l
nzK=zK {succ n} = dr= (cong+= i×l (nzK=zK {n}) (~~ zK=2zK))

Kⁿ+zK=Kⁿ : {n : ℕ} → Iso (Pow' K (succ n) ⊔ zK) (Pow' K (succ n))
Kⁿ+zK=Kⁿ {zero} = c+= (a+= (+= c+ =!= ~~ (fix≃ k) ) )
Kⁿ+zK=Kⁿ {succ n} = cong+= c× (~~ (KⁿzK=zK {succ n}) ) (dl ~!= (×= (Kⁿ+zK=Kⁿ {zero}) =!= c×))

nKᵐ+zK=zK : {n m : ℕ} → Iso (Num' (succ m) × Pow' K (succ n) ⊔ zK) (Num' (succ m) × Pow' K (succ n))
nKᵐ+zK=zK {n} {zero} = =+ i×l =!= ~~ (i×l= (~~ Kⁿ+zK=Kⁿ ) )
nKᵐ+zK=zK {n} {succ m} = =+ (dr= (c+= (+= i×l ) ) ) =!= (a+ ~!= a+= (a+= (+= Kⁿ+zK=Kⁿ =!= ~~ (dr= (c+= (+= i×l ) ) ) ) ) )

zL+zL=zL : Iso (zL ⊔ zL) zL
zL+zL=zL = a+= (!+ (a+ ~!= (a+ ~!= +! (c+= (cycle+ ~!~ fix≃ l))) ))

ac+ : ∀ {V} {a b c : ADT V} → Iso (a ⊔ b ⊔ c) (b ⊔ a ⊔ c)
ac+ = a+ ~!= (+! c+ ~!= a+)
ac+= : ∀ {V} {a b c d : ADT V} → Iso (b ⊔ a ⊔ c) d → Iso (a ⊔ b ⊔ c) d
ac+= e = ac+ =!= e
ac× : ∀ {V} {a b c : ADT V} → Iso (a × b × c) (b × a × c)
ac× = a× ~!= (×! c× ~!= a×)
ac×= : ∀ {V} {a b c d : ADT V} → Iso (b × a × c) d → Iso (a × b × c) d
ac×= e = ac× =!= e

LzL=zL : Iso (L × zL) zL
LzL=zL = ×!= (~~ a+) (dl= (!+= i×r (!+= (fix≃ l) (!+= ac+ (!+= (~~ a+) (a+ ~!= +! e1))))))
     where e1 = !+= (+!= (~~ i×r) (~~ dl)) (dl ~!= !× (!+= c+ (a+= (~~ (fix≃ l)))))

LⁿzL=zL : ∀ {n} → Iso (Pow' L n × zL) zL
LⁿzL=zL {zero}   = i×l
LⁿzL=zL {succ zero} = LzL=zL
LⁿzL=zL {succ (succ n)} = a×= (×!= (LⁿzL=zL {succ n}) LzL=zL)

L+zL=L : Iso (L ⊔ zL) L
L+zL=L = ac+ =!= (μ- l)

Lⁿ+zL=Lⁿ : ∀ {n} → Iso (Pow' L (succ n) ⊔ zL) (Pow' L (succ n))
Lⁿ+zL=Lⁿ {zero} = L+zL=L
Lⁿ+zL=Lⁿ {succ n} = !+= (~~ LzL=zL) (dl ~!= !× (Lⁿ+zL=Lⁿ {n}))

z+z=z : Iso (z ⊔ z) z
z+z=z = dl ~!= ×= zL+zL=zL

nz=z : {n : ℕ} → Iso (Num' (succ n) × z) z
nz=z {zero} = i×l
nz=z {succ n} = dr= (cong+= i×l (nz=z {n}) z+z=z)

Lⁿz=z : ∀ {n} → Iso (Pow' L n × z) z
Lⁿz=z {n} = ac×= (×= LⁿzL=zL)

Kⁿz=z : ∀ {n} → Iso (Pow' K n × z) z
Kⁿz=z {n} = a× ~!= =× KⁿzK=zK

mz=z : {n j k : ℕ} → Iso (((Num' (succ n)) × (Pow' K j) × (Pow' L k)) × z) z
mz=z {n} {j} {k} = a×= (×= (a×) =!= (×= (×= (Lⁿz=z {k}) =!= Kⁿz=z {j} ) =!= nz=z {n}) )

1mz=z : {j k : ℕ} → Iso (((Pow' K j) × (Pow' L k)) × z) z
1mz=z {j} {k} = a× =!= (×= Lⁿz=z =!= Kⁿz=z)

z=z+zL : Iso z (z ⊔ zL)
z=z+zL = dr= (+= (dr= (+= (i×l= (~~ zL+zL=zL) ) =!= (a+ ~!= =+ (cong+= !! (~~ i×l) (~~ dr)) ) ) ) ) =!= (a+ ~!= =+ (~~ dr) )

KzL=z : Iso (K × zL) z
KzL=z = ~~ (~~ (Kⁿz=z {1}) =!= (×= z=z+zL =!= dl= (=+ (~~ a×) =!= (dr ~!= =× (=+ KzK=zK =!= c+= (Kⁿ+zK=Kⁿ {0}) ) ) ) ) )

1m+z=1m : {j k : ℕ} → Iso (((Pow' K (succ j)) × (Pow' L (succ k))) ⊔ z) ((Pow' K (succ j)) × (Pow' L (succ k)))
1m+z=1m {zero} {k} = += (~~ KzL=z) =!= (dl ~!= ×= (Lⁿ+zL=Lⁿ {k}) )
1m+z=1m {succ j} {k} = += (~~ (Kⁿz=z {succ j}) =!= ×= ((~~ KzL=z) ) ) =!= (+= (a× ~!= =× c× ) =!= (dl ~!= ×= (Lⁿ+zL=Lⁿ {k}) ) )

m+z=m : {n j k : ℕ} → Iso (((Num' (succ n)) × Pow' K (succ j) × Pow' L (succ k)) ⊔ z) ((Num' (succ n)) × Pow' K (succ j) × Pow' L (succ k))
m+z=m {zero} = =+ i×l =!= (1m+z=1m =!= ~~ i×l )
m+z=m {succ n} = =+ (dr )  =!= a+= (+= (m+z=m {n}) =!= ~~ dr )

diviso1 : ∀ {X} {a b x1 x2 y z : ADT X} → Iso (a ⊔ b ⊔ (x1 ⊔ x2) × y ⊔ z) (a ⊔ b ⊔ x1 × y ⊔ x2 × y ⊔ z)
diviso1 = !+ (!+ (+! dr =!= a+))
diviso2 : ∀ {X} {a b x y1 y2 y3 z : ADT X} → Iso (a ⊔ b ⊔ x × (y1 ⊔ y2 ⊔ y3) ⊔ z) (x × y2 ⊔ x × y3 ⊔ a ⊔ b ⊔ x × y1 ⊔ z)
diviso2 = a+ ~!= (!+ (+! dist3) =!= (cycle+ =!= (+! c+ =!= a+= (a+= (!+ (!+ (a+ ~!= cycle+)))))))
diviso3 : ∀ {X} {a b x1 x2 x3 y z : ADT X} → Iso (x1 ⊔ x2 ⊔ x3) y → Iso (a ⊔ b ⊔ x1 ⊔ x2 ⊔ x3 ⊔ z) (a ⊔ b ⊔ y ⊔ z)
diviso3 x1+x2+x3=y = !+ (!+ (a+ ~!= (a+ ~!= +! (a+= x1+x2+x3=y))))
diviso4 : ∀ {X} {a1 a2 a3 x y1 y2 y3 : ADT X} → Iso a1 (x × y1) → Iso a2 (x × y2) → Iso a3 (x × y3) → Iso (a1 ⊔ a2 ⊔ a3) (x × (y1 ⊔ y2 ⊔ y3))
diviso4 e1 e2 e3 = cong+ e1 (cong+ e2 e3 =!~ dl) =!~ dl
diviso5 : ∀ {X} {a1 a2 x y z1 z2 : ADT X} → Iso x y → Iso (a2 × x ⊔ z1) z2 → Iso ((a1 ⊔ a2) × x ⊔ z1) (a1 × y ⊔ z2)
diviso5 e1 e2 = +! dr =!= (a+ =!= cong+ (!× e1) e2)
cong+4 : ∀ {X} {a1 b1 c1 d1 a2 b2 c2 d2 : ADT X} → Iso a1 a2 → Iso b1 b2 → Iso c1 c2 → Iso d1 d2 → Iso (a1 ⊔ b1 ⊔ c1 ⊔ d1) (a2 ⊔ b2 ⊔ c2 ⊔ d2)
cong+4 e1 e2 e3 e4 = cong+ e1 (cong+ e2 (cong+ e3 e4))

ac2× : ∀ {X} {a b c : ADT X} → Iso ((a × b) × c) (c × a × b)
ac2× = a× =!~ cycle×3

2X=X+X : ∀ {X} {a : ADT X} → Iso (Num' 2 × a) (a ⊔ a)
2X=X+X = dr =!= cong+ i×l i×l

doubleIter= : ∀ {X} {a b c : ADT X} → Iso b c → Iso (Num' 2 × a ⊔ b) (a ⊔ a ⊔ c)
doubleIter= b=c = cong+ 2X=X+X b=c =!= a+

2*2=4 : ∀ {X} → Iso (Num' {X} 2 × Num' 2) (Num' 4)
2*2=4 = dl =!= (cong+ i×r i×r =!= a+)

diviso' : Iso (Pow' K 4 × L ³ ⊔ K ³ × L ³ ⊔ (K × K ⊔ K ⊔ (Num' 2)) × (Num' 2 × L ³ ⊔ Num' 2 × L ² ⊔ Num' 2 × L) ⊔ (Num' 4 × L ²)) ((Num' 2 × K ² × L ²) ⊔ (Num' 2 × K ² × L) ⊔ K ² × L ³ × (K ² ⊔ K ⊔ (Num' 2)) ⊔ K × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L × (L ² ⊔ L ⊔ L ⊔ 𝟏)))
diviso' =     diviso1 {a = Pow' K 4 × L ³} {K ³ × L ³} {K × K} {K ⊔ Num' 2} {(Num' 2 × L ³ ⊔ Num' 2 × L ² ⊔ Num' 2 × L)} {Num' 4 × L ²}
         =!= (diviso2 {_} {Pow' K 4 × L ³} {K ³ × L ³} {K × K} {Num' 2 × L ³} {Num' 2 × L ²} {Num' 2 × L} {(K ⊔ Num' 2) × (Num' 2 × L ³ ⊔ Num' 2 × L ² ⊔ Num' 2 × L) ⊔ (Num' 4 × L ²)}
         =!= e0 )
  where e1 = diviso3 {_} {(K × K) × Num' 2 × L × L} {(K × K) × Num' 2 × L} {Pow' K 4 × L ³} {K ³ × L ³} {(K × K) × (Num' 2 × L × L × L)}
        e21 = ~~ (ac2× =!= (a× ~!= ×! a×))
        e22 = a× =!~ ac2×
        e23 = a× =!~ (ac2× =!= (ac× =!= a×))
        e2 = diviso4 {_} {x = Pow' K 2 × Pow' L 3} {K × K} {K} {Num' 2} e21 e22 e23
        e4 = doubleIter= (doubleIter= 2X=X+X)  -- ~~ (a+ ~!= cong+ double {!  !})
        e51 = ~~ (a×= (!×= (~~ 2*2=4) a×))
        e52 = ~~ a×
        e53 = a× ~!~ (a× =!= ×! (~~ 2*2=4))
        e54 = (a× ~!= ×! 2*2=4) =!~ i×r
        e5 = +! dist3 =!= c+= (ac+ =!= (cong+4 {_} e51 e52 e53 e54 =!~ (a× ~!= (dl= (!+ dist3))))) --
        e6 = diviso5 {_} {K} {Num' 2} {(Num' 2 × L × L × L ⊔ Num' 2 × L × L ⊔ Num' 2 × L)} {(L × L × L ⊔ L × L × L ⊔ L × L ⊔ L × L ⊔ L ⊔ L)} {Num' 4 × L × L} {Num' 4 × L × (L × L ⊔ L ⊔ L ⊔ 𝟏)} e4 e5
        e0 = e1 e2 =!= cong+4 ac× ac× a× e6

diviso : Iso (Pow' K 4 × L ³ ⊔ K ³ × L ³ ⊔ (K × K ⊔ K ⊔ (Num' 2)) × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L ²)) ((Num' 2 × K ² × L ²) ⊔ (Num' 2 × K ² × L) ⊔ K ² × L ³ × (K ² ⊔ K ⊔ (Num' 2)) ⊔ K × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L × (L ² ⊔ L ⊔ L ⊔ 𝟏)))
diviso = += (+= (=+ (×= (a+ ~!= cong+ (~~ (Num'=Num'' (L ³) 2 ) ) (a+ ~!= cong+ (~~ (Num'=Num'' (L ²) 2) ) (~~ (Num'=Num'' L 2) ) ) ) ) ) ) =!= diviso'

apply_fix≃ : Iso (Pow' K 4 × L ³ ⊔ K ³ × L ³ ⊔ K × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L ²)) ((Num' 2 × K ² × L ²) ⊔ (Num' 2 × K ² × L) ⊔ K ² × L ³ × K ⊔ K × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L ²))
apply_fix≃ = += (+= (=+ (=× (fix≃ k) )) ) =!= (diviso =!= += (+= (cong+ (×= (×= (~~ (fix≃ k) ) ) ) (+= (×= (×= (~~ (fix≃ l) ) ) ) ) ) ) )

simplify : Iso (Pow' K 4 × L ³ ⊔ K ³ × L ³ ⊔ K × L ³ ⊔ K × L ³ ⊔ K × L ² ⊔ K × L ² ⊔ K × L ⊔ K × L ⊔ (Num' 4 × L ²)) ((Num' 2 × K ² × L ²) ⊔ (Num' 2 × K ² × L) ⊔ K ³ × L ³ ⊔ K × L ³ ⊔ K × L ³ ⊔ K × L ² ⊔ K × L ² ⊔ K × L ⊔ K × L ⊔ (Num' 4 × L × L))
simplify = += (+= (~~ (=+ (dl= (+= (dl= (+= (dl= (+= dl) ) ) ) ) ) =!= a+= (+= (a+= (+= (a+= (+= (a+= (+= (~~ (a+ ~!= =+ (~~ dl) ) ) ) ) ) ) ) ) ) ) ) ) =!= (apply_fix≃ =!= += (+= (cong+ (ac×= (c×= (=× a× ) ) ) (=+ (dl= (+= (dl= (+= (dl= (+= (dl= (+= (dl ) ) ) ) ) ) ) ) ) =!= a+= (+= (a+= (+= (a+= (+= (a+= (+= (a+) ) ) ) ) ) ) ) ) ) ) )

R : ADT ⊥
R = K ³ × L ³ ⊔ K × L ³ ⊔ K × L ³ ⊔ K × L ² ⊔ K × L ² ⊔ K × L ⊔ K × L ⊔ (Num' 4 × L ²)

simplify_again : Iso (Pow' K 4 × L ³ ⊔ R) ((Num' 2 × K ² × L ² ⊔ Num' 2 × K ² × L) ⊔ R)
simplify_again = simplify =!= ~~ a+

neg1 : ADT ⊥
neg1 = K ² × L ² ⊔ K ² × L ⊔ K ² ⊔ (Num' 2 × L ²) ⊔ (Num' 2 × L) ⊔ 𝟏

1+neg1=z : Iso (𝟏 ⊔ neg1) z
1+neg1=z = c+= (~~ (dr= (cong+ (dl= (+= dl) ) !! ) =!= a+= (~~ (a+= (+= (a+= (~~ (a+= (+= (~~ (a+= (cong+ (~~ i×r) (~~ (dl= (~~ (a+= (+= (a+= (~~ (dl= (+= i×r ) ) )  ) ) ) ) ) ) ) ) ) ) )  ) ) ) ) ) ) )

subtraction_step1 : Iso (Pow' K 4 × L ³ ⊔ R × z) ((Num' 2 × K ² × L ² ⊔ Num' 2 × K ² × L) ⊔ R × z)
subtraction_step1 = ~~ (a+= (+= (=+ (~~ i×r) =!= (dl ~!= ×= 1+neg1=z ) ) ) ) =!= ((∨≃ simplify_again (refl≃ (R × neg1)) ) =!= a+= (a+= (~~ (a+= (+= (+= (~~ (=+ (~~ i×r) =!= (dl ~!= ×= 1+neg1=z ) ) ) ) ) ) ) ) )

Rz=z : Iso (R × z) z
Rz=z = (dr= (cong+ (1mz=z {3} {3}) (dr= (cong+ (1mz=z {1} {3}) (dr= (cong+ (1mz=z {1} {3}) (dr= (cong+ (1mz=z {1} {2}) (dr= (cong+ (1mz=z {1} {2}) (dr= (cong+ (1mz=z {1} {1}) (dr= (cong+ (1mz=z {1} {1}) (=× (×= (~~ i×l) ) =!= mz=z {3} {0} {2}  ) ) ) ) ) ) ) ) ) ) ) ) )) =!= (a+ ~!= cong+= z+z=z (a+ ~!= cong+= z+z=z (a+ ~!= cong+= z+z=z z+z=z z+z=z ) z+z=z ) z+z=z ))

subtraction_step2 : Iso (Pow' K 4 × L ³ ⊔ z) ((Num' 2 × K ² × L ² ⊔ Num' 2 × K ² × L) ⊔ z)
subtraction_step2 = += (~~ Rz=z) =!= (subtraction_step1 =!= += Rz=z )

K⁴L³=2K²L²+2K²L : Iso (Pow' K 4 × L ³) (Num' 2 × K ² × L ² ⊔ Num' 2 × K ² × L)
K⁴L³=2K²L²+2K²L = ~~ (1m+z=1m {3} {2}) =!= (subtraction_step2 =!= a+= (+= (m+z=m {1} {1} {0}) ) )
