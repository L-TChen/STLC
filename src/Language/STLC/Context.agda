module Language.STLC.Context where

open import Data.Nat
open import Data.Empty
open import Prelude

infix  2 _∋_
infixl 4 _,_
infixr 5 _→̇_
infixl 5 _⧺_

data Typ     : 𝓤₀ ̇
data Context : 𝓤₀ ̇
data _∋_     : Context → Typ → 𝓤₀ ̇

private
  variable
    Γ Δ Ξ : Context
    A B C : Typ
    
data Typ where
  ⊥̇   : Typ
  _→̇_ : Typ → Typ → Typ

data Context where
  ∅   :                  Context
  _,_ : Context → Typ → Context

data _∋_ where
  Z : Γ , A ∋ A

  S_ : Γ     ∋ A
       ---------
     → Γ , B ∋ A

length : Context → ℕ
length ∅       = 0
length (Γ , x) = suc (length Γ)

lookup : ∀ {n} → (p : n < length Γ) → Typ
lookup {_ , A} {zero}  _       = A
lookup {_ , _} {suc n} (s≤s p) = lookup p

count : ∀ {n} → (p : n < length Γ) → Γ ∋ lookup p
count {Γ , A} {zero}  (s≤s p) = Z
count {Γ , A} {suc n} (s≤s p) = S count p

ext
  : (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

Rename : Context → Context → 𝓤₀ ̇
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

_⧺_ : Context → Context → Context
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , x) = Γ ⧺ Δ , x
