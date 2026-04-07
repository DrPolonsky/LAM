open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

module QADT.Examples.S^3=S where

Sⁿlemma : ∀ (n : ℕ) → Iso (Pow S (succ (succ n))) (Pow S (succ (succ n)) ⊔ Pow S (succ n) ⊔ Pow S n)
Sⁿlemma n = =× (fix≃ s) =!= (distrR≃ =!= (+= (i×l= (=× (fix≃ s) =!= distrR≃)) =!= (+= (+= i×l ) =!= (a+ ~!= ~~ (a+ ~!= =+ (~~ (cong+= (=× (dr= (cong+= i×l (dr= (cong+ i×l al ) ) (a+ ~!= i+r )) ) ) (=× (dr= (cong+= i×l (dr= (cong+ i×l al ) ) (a+ ~!= i+r ) ) ) ) (+= dr =!= (a+ ~!= =+ (+= (~~ i×l) =!= (dr ~!= =× (=+ (cong+= (~~ i×l) (i+r ~!= cong+ (~~ i×l) (~~ (al {a = μ s})) ) (+= (~~ dr) =!= ~~ dr )) =!= ~~ (fix≃ s)) ) ) ) )) ) ) ) ) ) )

Sⁿlemma2 : ∀ (n : ℕ) → Iso (Pow' S (succ (succ n))) (Pow' S (succ (succ n)) ⊔ Pow' S (succ n) ⊔ Pow' S n)
Sⁿlemma2 n = ×= (~~ (Pow=Pow' S (succ n) ) ) =!= ( Sⁿlemma n =!= cong+ (×= (Pow=Pow' S (succ n) ) ) (cong+ (Pow=Pow' S (succ n) ) (Pow=Pow' S n) ) )

s[S³]=S³ : Iso (subst s (S ³)) (S ³)
s[S³]=S³ = ~~ (=× (fix≃ s) =!= (dr= (+= (i×l= (Sⁿlemma2 zero ) ) ) =!= (=+ (a×= (dr= (+= (dr= (c+) ) ) ) ) =!= (a+= (+= a+ =!= (+= (+= (=+ i×l =!= (a+ ~!= (a+ ~!= =+ (a+= (~~ (Sⁿlemma2 (succ zero) ) ) ) ) )  ) ) =!= (a+ ~!= (a+ ~!= =+ (+= (~~ i×l) =!= a+= (+= c+ =!= (+= (~~ dr) =!= ~~ dr ) ) ) ) ) ) ) ) ) ) )

S→S³ : SS → ⟦ S ³ ⟧ Γ₀
S→S³ = RigFold s (S ³) s[S³]=S³

test : Set
test = {! List→ (λ {(s1 , (s2 , s3)) → (S→𝕊 s1 , (S→𝕊 s2 , S→𝕊 s3))}) (List→ S→S³ (allS 10))  !}

findS³ : ℕ → SS³ → 𝔹
findS³ n ss³ = elem (==ADT {S ³}) ss³ (List→ S→S³ (allS n) )

preimg :  SS³ → ⟦ subst s (S ³) ⟧ Γ₀
preimg s1 = _≃_.f- (≃⟦ s[S³]=S³ ⟧ Γ₀) s1

test' : Set
test' = {! preimg (lfp (in2 tt) , (lfp (in1 (in1 tt , lfp (in2 tt))) , lfp (in2 tt)))  !}

-- preimg' : (n : ℕ) → SS³ → 𝕊
-- preimg' zero s1 = so
-- preimg' (succ n) s1 with preimg s1
-- ... | i = {! preimg s1  !}

<<<<<<< HEAD
𝕊³→𝕊 : 𝕊 ∧ (𝕊 ∧ 𝕊) → 𝕊
𝕊³→𝕊 (so , (so , so)) = so
𝕊³→𝕊 (so , (so , sp s3)) = sp (𝕊³→𝕊 (so , (so , s3)))
𝕊³→𝕊 (so , (so , sq s3)) = sq (𝕊³→𝕊 (so , (so , s3)))
𝕊³→𝕊 (so , (sp s2 , so)) = {! sp   !}
𝕊³→𝕊 (so , (sq s2 , so)) = {!   !}
𝕊³→𝕊 (sp s1 , (so , so)) = {!   !}
𝕊³→𝕊 (sq s1 , (so , so)) = {!   !}
𝕊³→𝕊 (so , (sp s2 , sp s3)) = {!   !}
𝕊³→𝕊 (so , (sp s2 , sq s3)) = {!   !}
𝕊³→𝕊 (so , (sq s2 , sp s3)) = {!   !}
𝕊³→𝕊 (so , (sq s2 , sq s3)) = {!   !}
𝕊³→𝕊 (sp s1 , (so , sp s3)) = {!   !}
𝕊³→𝕊 (sp s1 , (so , sq s3)) = {!   !}
𝕊³→𝕊 (sq s1 , (so , sp s3)) = {!   !}
𝕊³→𝕊 (sq s1 , (so , sq s3)) = {!   !}
𝕊³→𝕊 (sp s1 , (sp s2 , so)) = {!   !}
𝕊³→𝕊 (sp s1 , (sq s2 , so)) = {!   !}
𝕊³→𝕊 (sq s1 , (sp s2 , so)) = {!   !}
𝕊³→𝕊 (sq s1 , (sq s2 , so)) = sq (sq {!   !} )
𝕊³→𝕊 (sp s1 , (sp s2 , sp s3)) = sp (sp (sp (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sp s1 , (sp s2 , sq s3)) = sp (sp (sq (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sp s1 , (sq s2 , sp s3)) = sp (sq (sp (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sp s1 , (sq s2 , sq s3)) = sp (sq (sq (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sq s1 , (sp s2 , sp s3)) = sq (sp (sp (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sq s1 , (sp s2 , sq s3)) = sq (sp (sq (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sq s1 , (sq s2 , sp s3)) = sq (sq (sp (𝕊³→𝕊 (s1 , (s2 , s3)))))
𝕊³→𝕊 (sq s1 , (sq s2 , sq s3)) = sq (sq (sq (𝕊³→𝕊 (s1 , (s2 , s3)))))
=======
module ManualIso where

  𝕊³→𝕊 : 𝕊 ∧ (𝕊 ∧ 𝕊) → 𝕊
  𝕊³→𝕊 (so , (so , so)) = {!   !}
  𝕊³→𝕊 (so , (so , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (so , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sp s2 , so)) = {!   !}
  𝕊³→𝕊 (so , (sp s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sp s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , so)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (so , so)) = {!   !}
  𝕊³→𝕊 (sp s1 , (so , sp s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (so , sq s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sp s2 , so)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sp s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sp s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sq s2 , so)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sq s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (sq s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (so , so)) = {!   !}
  𝕊³→𝕊 (sq s1 , (so , sp s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (so , sq s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (sp s2 , so)) = {!   !}
  𝕊³→𝕊 (sq s1 , (sp s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (sp s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (sq s2 , so)) = {!   !}
  𝕊³→𝕊 (sq s1 , (sq s2 , sp s3)) = ?
  𝕊³→𝕊 (sq s1 , (sq s2 , sq s3)) = ?
  {-
  𝕊³→𝕊 (so , (so , so)) = so
  𝕊³→𝕊 (so , (so , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (so , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sp so , so)) = sp so
  𝕊³→𝕊 (so , (sp so , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sp so , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sp (sp s2) , so)) = {!   !}
  𝕊³→𝕊 (so , (sp (sp s2) , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sp (sp s2) , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sp (sq s2) , so)) = {!   !}
  𝕊³→𝕊 (so , (sp (sq s2) , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sp (sq s2) , sq s3)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , so)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (so , (sq s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (s2 , so)) = {!   !}
  𝕊³→𝕊 (sp s1 , (s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (sp s1 , (s2 , sq s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (s2 , so)) = {!   !}
  𝕊³→𝕊 (sq s1 , (s2 , sp s3)) = {!   !}
  𝕊³→𝕊 (sq s1 , (s2 , sq s3)) = {!   !}
-}
>>>>>>> 3ac5ccabf9def41b862d8f5d5305cfe980593039
