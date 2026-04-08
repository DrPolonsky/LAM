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

Lⁿ+zL=Lⁿ : ∀ n → Iso (Pow' L (succ n) ⊔ zL) (Pow' L (succ n))
Lⁿ+zL=Lⁿ zero = L+zL=L
Lⁿ+zL=Lⁿ (succ n) = !+= (~~ LzL=zL) (dl ~!= !× (Lⁿ+zL=Lⁿ n))

z+z=z : Iso (z ⊔ z) z
z+z=z = dl ~!= ×= zL+zL=zL

nz=z : {n : ℕ} → Iso (Num' (succ n) × z) z
nz=z {zero} = i×l
nz=z {succ n} = dr= (cong+= i×l (nz=z {n}) z+z=z)

Lⁿz=z : ∀ {n} → Iso (Pow' L n × z) z
Lⁿz=z {n} = ac×= (×= LⁿzL=zL)

Kⁿz=z : ∀ {n} → Iso (Pow' K n × z) z
Kⁿz=z {n} = a× ~!= =× KⁿzK=zK

mz=z : {n j k : ℕ} → Iso ((Num' (succ n)) × (Pow' K j) × (Pow' L k) × z) z
mz=z {n} {j} {k} = ×= (×= (Lⁿz=z {k}) =!= Kⁿz=z {j} ) =!= nz=z {n}

diviso : Iso (Pow' K 4 × L ³ ⊔ K ³ × L ³ ⊔ (K × K ⊔ K ⊔ (Num' 2)) × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L ²)) ((Num' 2 × K ² × L ²) ⊔ (Num' 2 × K ² × L) ⊔ K ² × L ³ × (K ² ⊔ K ⊔ (Num' 2)) ⊔ K × (L ³ ⊔ L ³ ⊔ L ² ⊔ L ² ⊔ L ⊔ L) ⊔ (Num' 4 × L × (L ² ⊔ L ⊔ L ⊔ 𝟏)))
diviso = {!   !}
