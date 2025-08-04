open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import QADT.Examples.ExampleADTs
open import Environment

module QADT.Examples.S=M^2 where

sM² : ADT ⊥
sM² = subst s (M ²)

M²=M+M²+M³ : Iso (M ²) (M ⊔ M ² ⊔ M ³)
M²=M+M²+M³ = t= (t= (×= (fix≃ m)) (dist3) ) (∨≃ (c×= (i×l= r= ) ) r=  )  -- (s= {! dist3   !} )

M²=M³+M²+M : Iso (M ²) (M ³ ⊔ M ² ⊔ M)
M²=M³+M²+M = t= M²=M+M²+M³ (c+= (t= (=+ (c+= r= )) (a+= r=) ) )

M²=1+2M+2M²+2M³ : Iso (M ²) (M ³ ⊔ M ³ ⊔ M ² ⊔ M ² ⊔ M ⊔ M ⊔ 𝟏)
M²=1+2M+2M²+2M³  = t= M²=M³+M²+M (+= (t= (=+ M²=M³+M²+M ) (a+= (+= (a+= (+= e ) ) ) ) ) )
  where e = t= (+= (fix≃ m ) ) (s= (t= cycle+ (+= (t= (=+ (c+= r= ) ) (a+= r=) ) ) ) )

e3 : Iso (M ²) ((M ³ ⊔ M ³) ⊔ ( M ² ⊔ M ²) ⊔ (M ⊔ M) ⊔ 𝟏)
e3 = t= M²=1+2M+2M²+2M³ (s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) ) )

sM²=M² : Iso sM² (M ²)
sM²=M² = ~~ (t= e3 (s= (t= (=+ (t= (×= M²=M³+M²+M ) (s= (X+X=2X _ ) ) )  ) (t= (a+= (a+= (+= (c+= (a+= (a+= (+= (a+= (+= (c+= (a+= (c+= (a+= (a+= (+= r= ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) e) ) ))
  where e = s= (a+= (+= (+= (a+= (+= (+= (a+= r= ) ) ) ) ) ) )

M²=2M²+1v2 : Iso (M ²) ((Num 2) × M ² ⊔ 𝟏)
M²=2M²+1v2 = c× =!~ sM²=M²

sM²=M²v2 : Iso sM² (M ²)
sM²=M²v2 = ~~ M²=2M²+1v2

sM²=M²v3 : Iso sM² (M ²)
sM²=M²v3 = =+ (dr= (cong+= i×l (dr= (cong+= i×l al i+r) ) r=) ) =!= a+= (=+ (×= (fix≃ m) =!= dl= (cong+= i×r (dl ) r=) ) =!= a+= (+= (a+ ) =!= c+= (a+= (+= (a+= (+= (a+= (c+= (a+= (~~ (fix≃ m) ) ) ) ) ) ) =!= c+= (a+= (=+ (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (+= (c×= (a×) ) ) ) r=) ) =!= a+= (+= (a+= (c+= (a+= (+= (a+) =!= (a+ ~!= (=+ (c+) =!= a+= (+= (c+= (a+= (cong+= (~~ i×r) (cong+= (~~ a×) (~~ a× ) (~~ dl)) (dl ~!= (×= (~~ (fix≃ m)) =!= a×) )) ) ) ) ) ) ) ) ) ) =!= c+= (a+= (+= c+ =!= cong+= (~~ i×r) (~~ dl ) (dl ~!= ×= (~~ (fix≃ m) ) ) ) ) ) ) ) ) )  ) )

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

stuff? : ⟦ M ² ⟧ Γ₀
stuff? = {! S→M² (S0 (S0 (S0 Sλ)))  !}

hasBnode : MM → 𝔹
hasBnode (lfp (in1 tt)) = false
hasBnode (lfp (in2 (in1 (lfp x)))) = hasBnode (lfp x)
hasBnode (lfp (in2 (in2 (pr3 , pr4)))) = true


findm² : MM² → ℕ → 𝔹
findm² m² n = elem ==M² m² (List→ S→M² (allS n))

some_m² : List MM²
some_m² = take 50 (allM² 10)

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

check4 : Set
check4 = {! List→ (f ∘ preimg) (passN 5)  !} where
  f : ⟦ sM² ⟧ Γ₀ → ↑ (𝔹 ∧ (𝕄 ∧ 𝕄))
  f (in1 (in1 tt , m2)) = i (false , M²→𝕄² m2 )
  f (in1 (in2 (in1 tt) , pr4)) = i (true , M²→𝕄² pr4 )
  f (in2 tt) = o
