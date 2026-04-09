open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs renaming (_⊔_ to _+_)
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

module QADT.Examples.Demo where

𝕞 : ADT (↑ ⊥)
𝕞 = 𝟏 + (𝕍 o) + (𝕍 o) ²

MTree : ADT ⊥
MTree = μ (𝟏 + (𝕍 o) + (𝕍 o) ²)

⟦MTree⟧ : Set
⟦MTree⟧ = ⟦ MTree ⟧ Γ₀

-- Pretty printer for MTree
data prettyM : Set where
  mleaf : prettyM
  munode : prettyM → prettyM
  mbnode : prettyM → prettyM → prettyM

printM : ⟦MTree⟧ → prettyM
printM (lfp (in1 tt)) = mleaf
printM (lfp (in2 (in1 x))) = munode (printM x)
printM (lfp (in2 (in2 (x , y)))) = mbnode (printM x) (printM y)

printM⁵ : ⟦ Pow' MTree 5 ⟧ Γ₀ → prettyM ∧ (prettyM ∧ (prettyM ∧ (prettyM ∧ prettyM)))
printM⁵ (m1 , (m2 , (m3 , (m4 , m5)))) = printM m1 , (printM m2 , (printM m3 , (printM m4 , printM m5)))

readM : prettyM → ⟦MTree⟧
readM mleaf = lfp (in1 tt)
readM (munode x) = lfp (in2 (in1 (readM x)))
readM (mbnode x y) = lfp (in2 (in2 (readM x , readM y)))

-- A List of the elements of the interpreted ADT MTree
MTreeElements : List prettyM
MTreeElements = {! List→ printM (EnumADTk MTree Γ₀ EnumΓ₀ 4)  !}

powfix≃M : (n : ℕ) → Iso (Pow' MTree (succ n)) ((Pow' MTree n) + (Pow' MTree (succ n)) + (Pow' MTree (succ (succ n))))
powfix≃M zero = fix≃ 𝕞
powfix≃M (succ n) with powfix≃M n
... | r = ~~ (cong+= (~~ i×l) (+= (~~ a×) =!= ~~ dr )  (dr ~!= (=× (~~ (fix≃ 𝕞)))))

M≃M⁵ : Iso MTree (Pow' MTree 5)
M≃M⁵ = fix≃ 𝕞 =!= (+= (+= (powfix≃M 1)) =!= (+= (+= (+= (+= (powfix≃M 2)))) =!= (+= (+= (+= (+= (+= (cong+ (powfix≃M 2) (powfix≃M 3) =!= a+= (+= (a+= (+= (=+ (powfix≃M 3) =!= a+= (+= (a+= (+= (+= (+= (+= (powfix≃M 4)))))))))))))))) =!= (a+ ~!= (a+ ~!= (a+ ~!= (=+ (a+= (=+ c+ =!= a+= (+= (~~ (fix≃ 𝕞))))) =!= a+= (+= (a+ ~!= (a+ ~!= (a+ ~!= =+ (=+ (=+ c+ =!= a+) =!= a+= (+= (a+= (~~ (powfix≃M 1)))))))) =!= (a+ ~!= (a+ ~!= (=+ (=+ (a+ ~!= =+ c+ ) =!= a+= (a+= (+= (~~ (powfix≃M 1))))) =!= (+= (+= (a+ ~!= (=+ c+ =!= a+)) =!= (a+ ~!= ((=+ c+) =!= a+))) =!= a+= (+= (a+ ~!= (a+ ~!= =+ (a+= (~~ (powfix≃M 2))))) =!= (+= (+= (a+ ~!= (=+ c+ =!= a+))) =!= (a+ ~!= (a+ ~!= (=+ (a+= (~~ (powfix≃M 2))) =!= (+= (a+ ~!= =+ c+ ) =!= (a+ ~!= (=+ (~~ (powfix≃M 3)) =!= ~~ (powfix≃M 4)))))))))))))))))))))

⟦M≃M⁵⟧ : ⟦MTree⟧ ≃ ⟦ Pow' MTree 5 ⟧ Γ₀
⟦M≃M⁵⟧ = ≃⟦ M≃M⁵ ⟧ Γ₀

showIso : Set
showIso = {! zip (List→ printM (EnumADTk MTree Γ₀ EnumΓ₀ 3)) (List→ printM⁵ (List→ (_≃_.f+ ⟦M≃M⁵⟧) (EnumADTk MTree Γ₀ EnumΓ₀ 3)))  !}
