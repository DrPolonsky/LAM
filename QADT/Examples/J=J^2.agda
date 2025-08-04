open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.J=J^2 where

j[c×J²] : Iso (subst j (J ²)) (subst j (J ²))
j[c×J²] = substIso j c×

testRig : Iso (subst j (J ²)) (J ²) → ℕ → 𝔹
testRig α n = all (λ { (x , y) → ==jJ² x y }) ((List→ f (allJ² n)))
  where i1 = c× =!~ α
        i2 = α ~!= j[c×J²]
        f =  λ x → _≃_.f+ (≃⟦ i1 ⟧ Γ₀ ) x , _≃_.f+ (≃⟦ i2  ⟧ Γ₀ ) x

jJ²=J² : Iso (subst j (J ²)) (J ²)
jJ²=J² = += (=+ (×= (fix≃ j ) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) =!= += (=+ (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl) ) ) r=) ) ) ) =!= (+= (a+= (+= (a+= (+= (a+= (+= (+= (a+= (+= (a+=  (+= (a+= (+= (+= (a× ) ) ) ) ) ) ) ) ) ) ) )  ) ) ) =!=  (+= (+= (+= (c+= (=+ (c+= (a+= (+= (a+= (+= (c+= (a+ ~!= (a+ ~!= (=+ (=+ c+ ) =!= a+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (cong+ (~~ a×) (~~ a×) ) (+= (~~ dl) =!= ~~ dl )) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) )  ) ) ) ) ) ) ) ) ) ) ) =!= ( (a+ ~!= (a+ ~!= (a+ ~!= =+ (a+ ~!= =+ (a+= (a+= (+= (+= c+ ) =!= ~~ (fix≃ j) ) ) ) ) ) ) ) =!= a+= (+= (c+= (cong+= r= (+= a× =!= ~~ dl ) (~~ dl)) ) =!= (=+ (~~ i×r) =!= (dl ~!= ×= (~~ (fix≃ j) ) )  ) ) ) ) )

jJ²=J²v2 : Iso (subst j (J ²)) (J ²)
jJ²=J²v2 = jJ²=J² =!= c×

-- 𝟏 ⊔ J × (unfold J) ⊔ J × (unfold J) ⊔ (J × J) × J × J
jJ²=J²v3 : Iso (subst j (J ²)) (J ²)
jJ²=J²v3 = += (a+ ~!= =+ (cong+= (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!) ) (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) ) ) ) =!= ((a+ ~!= =+ (a+ ~!= (a+ ~!= (+= (c+= (a+= (c+= (a+= (a+= !! ) )  ) ) ) =!= (a+ ~!= =+ (a+= (+= c+ =!= a+= (~~ (fix≃ j) ) ) ) ) ) ) ) ) =!= (a+= (+= (a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (cong+= (~~ i×r ) (cong+= (~~ a×) (~~ a×) (~~ dl) ) (~~ dl)) ) ) =!= ~~ dl) ) ) ) ) ) ) =!= (+= (+= (+= (×= (a+= (+= a+  =!= ~~ (fix≃ j) ) )  =!= a× ) ) ) =!= cong+= (~~ i×r) (cong+= !! (cong+= !! !! (~~ dl)) (~~ dl)) (~~ dl =!= ×= (~~ (fix≃ j) ) ) )) ) )

-- j3 but commute the J×J terms before unfold
jJ²=J²v4 : Iso (subst j (J ²)) (J ²)
jJ²=J²v4 = += (a+ ~!= =+ (cong+= (c×= (×= (fix≃ j) )  =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!) ) ( c×= (×= (fix≃ j)) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) ) ) ) =!= ((a+ ~!= =+ (a+ ~!= (a+ ~!= (+= (c+= (a+= (c+= (a+= (a+= !! ) )  ) ) ) =!= (a+ ~!= =+ (a+= (+= c+ =!= a+= (~~ (fix≃ j) ) ) ) ) ) ) ) ) =!= (a+= (+= (a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (cong+= (~~ i×r ) (cong+= (~~ a×) (~~ a×) (~~ dl) ) (~~ dl)) ) ) =!= ~~ dl) ) ) ) ) ) ) =!= (+= (+= (+= (×= (a+= (+= a+  =!= ~~ (fix≃ j) ) )  =!= a× ) ) ) =!= cong+= (~~ i×r) (cong+= !! (cong+= !! !! (~~ dl)) (~~ dl)) (~~ dl =!= ×= (~~ (fix≃ j) ) ) )) ) )

-- 𝟏 ⊔ (unfold J) × J ⊔ (unfold J) × J ⊔ (J × J) × J × J
jJ²=J²v5 : Iso (subst j (J ²)) (J ²)
jJ²=J²v5 = += (a+ ~!= =+ (cong+= (=× (fix≃ j) =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) ) ) (=× (fix≃ j)  =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) )) (a+= (+= (a+= (+= (a+= (+= !! ) ) ) ) ) )) ) =!= (+= (a+=  (+= (=+ (a+ ~!= (a+ ~!= (a+ ~!= =+ c+ ) ) ) ) ) ) =!= (+= (+= (a+= (a+= (+= (a+= (a+= !! ) ) ) ) ) ) =!= (a+ ~!= (a+ ~!= (a+ ~!= (=+ (a+= (a+= (~~ (fix≃ j) ) ) ) =!= (+= (+= (a+ ~!= (=+ (a+ ~!= =+ c+ ) =!= a+= (a+= (+= (a+ ~!= (=+ (a+ ~!= =+ c+ ) =!= a+= (a+= (cong+= (~~ i×r) (cong+= !! (~~ dl ) (~~ dl)) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) ) ) ) ) ) ) =!= cong+= (~~ i×r) (+= (+= (a× ) =!= ~~ dl ) =!= ~~ dl ) (dl ~!= ×= (~~ (fix≃ j) ) ) ) ) ) ) ) ) )

-- 𝟏 ⊔ (unfold J) × J ⊔ J × (unfold J) ⊔ (J × J) × J × J
jJ²=J²v6 : Iso (subst j (J ²)) (J ²)
jJ²=J²v6 = += (a+ ~!= =+ (cong+= (=× (fix≃ j) =!= dr= (cong+ i×l (dr= (+= (dr= !! ) ) ) )) (×= (fix≃ j) =!= dl= (cong+= i×r (dl= (+= (dl= r= ) ) ) !!)) a+) ) =!= (+= (a+= (+= (a+= (a+= (+= (a+ ~!= =+ (a+ ~!= =+ c+ ) ) =!= (a+ ~!= =+ (a+ ~!= =+ (a+ ~!= =+ c+ ) ) ) ) ) ) ) ) =!= (a+ ~!= (a+ ~!= (=+ (a+ ~!= =+ (a+ ~!= =+ (a+= (~~ (fix≃ j) ) )  ) ) =!= a+= (a+= (+= (a+= (+= (a+ ~!= (=+ (c+= (a+= (+= (a+= (+= c+ ) ) ) ) ) =!= a+= (+= (a+= (cong+= (~~ i×r) (a+= (cong+= !! (cong+= (~~ a×) !! (~~ dl)) (~~ dl)) ) (dl ~!= ×= (~~ (fix≃ j) ) )) ) ) ) ) ) ) =!= cong+= (~~ i×r) (+= (+= a× =!= ~~ dl ) =!= ~~ dl ) (dl ~!= ×= (~~ (fix≃ j)) ) ) ) ) ) ) )

-- 𝟏 ⊔ J × (unfold J) ⊔ (unfold J) × J ⊔ (J × J) × J × J
jJ²=J²v7 : Iso (subst j (J ²)) (J ²)
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
findj² j² n = elem ==J² j² (List→ J→J² (allJ n))


some_j² : List (⟦ J ² ⟧ Γ₀)
some_j² = take 50 (allJ² 10)

passNj² : ℕ → List (⟦ J ² ⟧ Γ₀)
passNj² zero = some_j²
passNj² (succ n) = filter (λ x → findj² x (succ n)) (passNj² n)

notPassj : ℕ → List (⟦ J ² ⟧ Γ₀)
notPassj 0 = []
notPassj (succ n) = filter (λ x → not (findj² x (succ n))) some_j²


depthJ : JJ → ℕ
depthJ (lfp (in1 tt)) = 0
depthJ (lfp (in2 (in1 x))) = succ (depthJ x)
depthJ (lfp (in2 (in2 (in1 x)))) = succ (depthJ x)
depthJ (lfp (in2 (in2 (in2 (pr3 , pr4))))) = succ (max (depthJ pr3) (depthJ pr4))


check'''' : Set
check'''' = {! length (filter (λ x → not (eqℕ x 2)) (List→ depthJ (allJ 5)))  !} -- {! take 100 (filter (λ x → not (le 5 (depthJ x)) (allJ 5))   !} -- {! List→ J²→𝕁² (passNj² 4)  !}

chek : Set
chek = {! List→ J²→𝕁² (passNj² 5)  !}

check''' : Set
check''' = {! List→ J→𝕁 (take 100 (allJ 6))  !}

check'' : Set
check'' = {! List→ J²→𝕁² (List→ J→J²v7 (take 100 (allJ 6)))  !}
