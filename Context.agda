module Context where

open import Data.Nat
open import Data.Empty

infix  4 _∋_
infixl 6 _,_
infixr 7 _→̇_
infixl 7 _⧺_

data Type    : Set
data Context : Set
data _∋_     : Context → Type → Set

private
  variable
    Γ Δ Ξ : Context
    A B C : Type
    
data Type where
  ⋆   : Type
  _→̇_ : Type → Type → Type

data Context where
  ∅   :                  Context
  _,_ : Context → Type → Context

lookup : Context → ℕ → Type
lookup (Γ , A) zero     =  A
lookup (Γ , B) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥

_⧺_ : Context → Context → Context
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , x) = Γ ⧺ Δ , x

data _∋_ where
  Z : Γ , A ∋ A

  S_ : Γ     ∋ A
       ---------
     → Γ , B ∋ A

count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅    }  _       =  ⊥-elim impossible
  where postulate impossible : ⊥

ext
  : (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
