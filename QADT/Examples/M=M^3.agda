open import Logic renaming (_×_ to _∧_; _⊔_ to _∨_)
open import Lifting
open import Datatypes
open import QADT.Functor
open import QADT.Isomorphisms
open import QADT.ADTs
open import QADT.ADT-Isomorphisms
open import Environment
open import QADT.Examples.ExampleADTs

module QADT.Examples.M=M^3 where

==M³iso : ℕ → Iso (subst m M³) (M³) → Iso (subst m M³) (M³) → 𝔹
==M³iso n im im2 = all I (List→ (λ x → ==ADT {subst m M³} (_≃_.f- (≃⟦ im ⟧ Γ₀) x) (_≃_.f- (≃⟦ im2 ⟧ Γ₀ ) x) )  (allM³ n))

m[c×M³] : List (Iso (subst m M³) (subst m M³))
m[c×M³] = List→ (λ x → substIso m x ) c×³



mM³=M³ : Iso (subst m M³) (M³)
mM³=M³ = ~~ (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (cong+= (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (+= (a×) ) ) !!) ) a× (+= (=× (fix≃ m) =!= dr= (cong+= i×l  (dr= (+= (a×= (=× (fix≃ m) =!= dr= (cong+= i×l (dr= (+= (a× ~!= =× a× ) ) ) !!) ) ) ) ) (a+ ~!= (cong+= c+ !! (a+ ~!= (a+ ~!= =+ (a+= (a+= (+= (cong+= (~~ i×l) (+= (~~ a×) =!= (dr ~!= !! ) ) (dr ~!= =× (~~ (fix≃ m) )  )) ) ) ) ) ) ) )   ) ) =!= !! )) ) (a+ ~!= (a+ ~!= (=+ (=+ (+= (cong+= (~~ i×l) (+= (~~ a×) =!= (~~ dr ) ) (dr ~!= =× (~~ (fix≃ m) ) )) ) =!= (=+ (=+ (=× (fix≃ m) =!= dr= (cong+= (i×l= (fix≃ m) ) (dr= (+= a× ) ) (a+= (+= (a+)  ) ) ) ) ) =!= a+= (a+= (+= (=+ (+= (+= c+ ) =!= (a+ ~!= (a+ ~!= =+ (a+= (cong+= (~~ i×l) (cong+= !! (~~ a×) (dr ~!= !! )) (dr ~!= =× (~~ (fix≃ m) ) )) ) ) )     ) =!= a+= (+= (a+ ~!= (a+ ~!= =+ (a+= (cong+= (~~ i×l) (cong+= !! (~~ a×) (~~ dr)) (dr ~!= =× (~~ (fix≃ m) ) )) ) ) ) =!= cong+= (~~ i×l) (cong+= !! (~~ a×) (~~ dr)) (dr ~!= =× (~~ (fix≃ m)) )) ) ) ) ) ) =!= ~~ (a+ ~!= += (!! )  )  ) ) ) ) )

c×m[c×M³] : List (Iso (subst m M³) (M³))
c×m[c×M³] = flatten (List→ (λ x → List→ (λ y → x =!= (mM³=M³ =!= y ) ) (c×³ {X = M}) ) m[c×M³] )

isoCheck : List (List 𝔹)
isoCheck = (List→ (λ x → List→ (λ y → ==M³iso 2 x y ) c×m[c×M³] ) c×m[c×M³] )

test234 : Set
test234 = {! List→ (λ x → filter not x) isoCheck  !}

M→M³ : MM → MM³
M→M³ = RigFold m M³ mM³=M³


findM³ : ℕ → MM³ → 𝔹
findM³ n mm = elem ==M³ mm (List→ M→M³ (allM n) )

someM³ : List (MM³)
someM³ = take 30 (allM³ 5)

pass : ℕ → List (MM³)
pass n = filter (findM³ n) someM³

test1 : Set
test1 = {! pass 5  !}

test : Set
test = {! List→ M³→𝕄³ (List→ M→M³ (take 100 (allM 5)))  !}
