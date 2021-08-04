module Language.STLC.Context where

open import Data.Nat
open import Data.Empty
open import Prelude

infix  2 _∋_
infixl 4 _,_
infixr 5 _→̇_
infixl 5 _⧺_

data Typ     (ℬ : 𝓤₀ ̇) : 𝓤₀ ̇
data Context (ℬ : 𝓤₀ ̇) : 𝓤₀ ̇
data _∋_     {ℬ : 𝓤₀ ̇} : Context ℬ → Typ ℬ → 𝓤₀ ̇

private
  variable
    ℬ     : 𝓤₀ ̇
    Γ Δ Ξ : Context ℬ
    A B C : Typ ℬ
    
data Typ ℬ where
  ι   :             ℬ → Typ ℬ
  _→̇_ : Typ ℬ → Typ ℬ → Typ ℬ

data Context ℬ where
  ∅   :                     Context ℬ
  _,_ : Context ℬ → Typ ℬ → Context ℬ

data _∋_ where
  Z : Γ , A ∋ A

  S_ : Γ     ∋ A
       ---------
     → Γ , B ∋ A

length : Context ℬ → ℕ
length ∅       = 0
length (Γ , x) = suc (length Γ)

lookup : {Γ : Context ℬ} {n : ℕ} → (p : n < length Γ) → Typ ℬ
lookup {Γ = _ , A} {n = zero}  _       = A
lookup {Γ = _ , _} {n = suc n} (s≤s p) = lookup p

count : {Γ : Context ℬ} {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
count {Γ = Γ , A} {zero}  (s≤s p) = Z
count {Γ = Γ , A} {suc n} (s≤s p) = S count p

ext
  : {Γ Δ : Context ℬ}
  → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

Rename : Context ℬ → Context ℬ → 𝓤₀ ̇
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

_⧺_ : Context ℬ → Context ℬ → Context ℬ 
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , x) = Γ ⧺ Δ , x
