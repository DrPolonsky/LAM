open import Relations.Relations
open import Predicates
open import Logic

module Relations.ARS-Theorems {A : Set } {R : 𝓡 A} where

open import Relations.ARS-Properties {A}
open import Relations.ARS-Propositions
open import Relations.ARS-Util
open import Relations.ARS-Base

{-This file contains formalization of the theorems of TeReSe Chapter 1-}

module Theorem1-2-2 where
    CR→NP : R isCR → R isNP
    CR→NP RisCR {x} {y} y∈NF R⁼xy with Proposition-1-1-10.i→vi (CR→confluent RisCR )  x y R⁼xy
    ... | z ,, R*xz , ε⋆ = R*xz
    ... | z ,, R*xz , (Ryy₀ ,⋆ R*y₀z) = ∅ (y∈NF Ryy₀)

    NP→UN : R isNP → R isUN
    NP→UN RisNP x∈NF y∈NF R⁼xy = NF→ε x∈NF (RisNP y∈NF R⁼xy)

    CP→UN : R isCR → R isUN
    CP→UN RisCR = NP→UN (CR→NP RisCR)
    -- The above provides i)

    lemmaii : R isWN → R isUN → R ⁼ ⊆ (R ⋆) ∘R ~R (R ⋆)
    lemmaii RisWN RisUN x y R⁼xy with RisWN x
    ... | nˣ ,, R*xnˣ , nˣ∈NF with RisWN y
    ... | nʸ ,, R*ynʸ , nʸ∈NF with RisUN nˣ∈NF nʸ∈NF (⋆~!⁼!⋆ R*xnˣ R⁼xy R*ynʸ)
    ... | refl = nʸ ,, R*xnˣ , R*ynʸ

    ii : R isWN × R isUN → R isCR
    ii (RisWN , RisUN) x {y}{z} R*xy R*xz with RisWN x
    ... | n ,, R*xn , n∈NF with Proposition-1-1-10.vi→i (lemmaii RisWN RisUN) (x ,, (R*xy , R*xz))
    ... | q ,, R*yq , R*zq  = q ,, R*yq , R*zq

    iii : subcommutative R → R isCR
    iii RisSC x R*xy R*xz = Proposition-1-1-10.v→i (λ { b c (a ,, Rab , R*ac) → f b c a Rab R*ac } ) (x ,, (R*xy , R*xz))  where
      f : (x y z : A) → R z x → (R ⋆) z y → ((R ⋆) ∘R ~R (R ⋆)) x y
      f x y .y Rzx ε⋆ = x ,, ε⋆ , (Rzx ,⋆ ε⋆)
      f x y z Rzx (Rzy₁ ,⋆ R*y₁y) with RisSC (z ,, (Rzx , Rzy₁))
      ... | d ,, R , εʳ = y ,, R ʳ!⋆ R*y₁y , ε⋆
      ... | d ,, Rʳxd , axʳ x₁ with f d y _ x₁ R*y₁y
      ... | w ,, R*dw , R*yw = w ,, (Rʳxd ʳ!⋆ R*dw ) , R*yw
