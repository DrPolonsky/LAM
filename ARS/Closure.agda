open import Relations.Relations
open import Predicates
open import Logic

module ARS.Closure {A : Set } {R : 𝓡 A} where

open import ARS.Properties {A}

open LocalProperties {R}

{-This file contains formalizations for closure under reduction -}

module UpwardClosure where
    WN⊆WN↑ : ∀ {y} → WN y → ∀ {x} → (R ⋆) x y → WN x
    WN⊆WN↑ y∈WN ε⋆ = y∈WN
    WN⊆WN↑ y∈WN (Rxz ,⋆ R*zy) with WN⊆WN↑ y∈WN R*zy
    ... | (n ,, R*zn , n∈NF) = n ,, (Rxz ,⋆ R*zn) , n∈NF

module DownwardClosure where
    SN↓⊆SN : ∀ {x} → SN x → ∀ {y} → (R ⋆) x y → SN y
    SN↓⊆SN x∈SN ε⋆ = x∈SN
    SN↓⊆SN (acc xacc) (Rxx₁ ,⋆ R*x₁y) = SN↓⊆SN (xacc _ Rxx₁) R*x₁y

    NF↓⊆NF : ∀ {x} → NF x → ∀ {y} → (R ⋆) x y → NF y
    NF↓⊆NF x∈NF ε⋆ = x∈NF
    NF↓⊆NF x∈NF (Rxx₁ ,⋆ R*x₁y) = λ _ → x∈NF Rxx₁

    UN↓⊆UN : ∀ {x} → UN x → ∀ {y} → (R ⋆) x y → UN y
    UN↓⊆UN x∈UN R*xy n∈NF z∈NF R*yn R*yz = x∈UN n∈NF z∈NF (R*xy ⋆!⋆ R*yn) (R*xy ⋆!⋆ R*yz)

    MF↓⊆MF : ∀ {x} → MF x → ∀ {y} → (R ⋆) x y → MF y
    MF↓⊆MF x∈MF R*xy z R*yz with x∈MF z (R*xy ⋆!⋆ R*yz)
    ... | R*zx  = R*zx ⋆!⋆ R*xy

    SM↓⊆SM : ∀ {x} → SM x → ∀ {y} → (R ⋆) x y → SM y
    SM↓⊆SM {x} (SMrec _ x∈rec) ε⋆ = SMrec x x∈rec
    SM↓⊆SM {y} (SMrec _ x∈rec) (Rxx₀ ,⋆ R*x₀y) = SM↓⊆SM (SMrec _ (MF↓⊆MF x∈rec (Rxx₀ ,⋆ ε⋆))) R*x₀y
    SM↓⊆SM {x} (SMacc _ x∈acc) ε⋆ = SMacc x x∈acc
    SM↓⊆SM (SMacc _ x) (Rxx₀ ,⋆ R*x₀y) = SM↓⊆SM (x _ Rxx₀) R*x₀y

open DownwardClosure public
