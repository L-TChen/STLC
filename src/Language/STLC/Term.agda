module Language.STLC.Term where

open import Data.Nat
open import Relation.Nullary.Decidable

open import Language.STLC.Context public

infix  3 _⊢_
infixr 5 ƛ_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infixr 9 `_ #_

data _⊢_ (Γ : Context) : Type → Set

private
  variable
    Γ Δ            : Context
    A B C          : Type
    M N L M′ N′ L′ : Γ ⊢ A

data _⊢_ Γ where
  `_
    : Γ ∋ A
      -----
    → Γ ⊢ A
  _·_
    : Γ ⊢ A →̇ B
    → Γ ⊢ A
      -----
    → Γ ⊢ B
  ƛ_
    : Γ , A ⊢ B
      ---------
    → Γ ⊢ A →̇ B
  abort
    : ∀ A
    → Γ ⊢ ⊥̇
    → Γ ⊢ A
  
#_ : (n : ℕ) {n∈Γ : True (suc n ≤? length Γ)}
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ _ {n∈Γ} = ` count (toWitness n∈Γ)

rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)     = ` ρ x
rename ρ (M · N)   = rename ρ M · rename ρ N
rename ρ (ƛ M)     = ƛ rename (ext ρ) M
rename ρ (abort _ M) = abort _ (rename ρ M)

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : Subst Γ Δ → Subst (Γ , A) (Δ , A)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ ⊢ A 
  → Subst Γ Δ
  → Δ ⊢ A
(` x)   ⟪ σ ⟫ = σ x
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
abort _ M ⟪ σ ⟫ = abort _ (M ⟪ σ ⟫)

subst-zero : {B : Type}
  → Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z     =  N
subst-zero _ (S x) =  ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
       ---------
     → Γ ⊢ A
_[_] N M =  N ⟪ subst-zero M ⟫

infix 3 _-→_
data _-→_ {Γ} : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : (ƛ M) · N -→ M [ N ]
  ξ-ƛ
    :   M -→ M′
    → ƛ M -→ ƛ M′    
  ξ-·ₗ
    :     L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·ᵣ
    :     M -→ M′
      ---------------
    → L · M -→ L · M′
  ξ-abort
    : M -→ M′
    → abort A M -→ abort A M′

data _-↠_ {Γ A} : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M
    
  _-→⟨_⟩_
    : ∀ L   
    → L -→ M
    → M -↠ N
      -------
    → L -↠ N

infix  2 _-↠_ 
infixr 2 _-→⟨_⟩_
infix 3 _∎

_-↠⟨_⟩_ : ∀ L
  → L -↠ M → M -↠ N
  -----------------
  → L -↠ N
L -↠⟨ M ∎ ⟩  M-↠N               = M-↠N
L -↠⟨ L -→⟨ L→M′ ⟩ M′-↠M ⟩ M-↠N = L -→⟨ L→M′ ⟩ (_ -↠⟨ M′-↠M ⟩ M-↠N)

infixr 2 _-↠⟨_⟩_

ƛ-↠ : M -↠ M′
      -----------
    → ƛ M -↠ ƛ M′
ƛ-↠ (M ∎)               = ƛ M ∎
ƛ-↠ (M -→⟨ M→N ⟩ N-↠M′) = ƛ M -→⟨ ξ-ƛ M→N ⟩ ƛ-↠ N-↠M′

abort-↠ : M -↠ M′
        → abort A M -↠ abort A M′
abort-↠ (_ ∎)               = abort _ _ ∎
abort-↠ (_ -→⟨ M→N ⟩ N-↠M′) = abort _ _ -→⟨ ξ-abort M→N ⟩ abort-↠ N-↠M′

·ᵣ-↠ : N -↠ N′
  → M · N -↠ M · N′
·ᵣ-↠ {M = M} (N ∎)               = M · N ∎
·ᵣ-↠ {M = M} (N -→⟨ N→M ⟩ M-↠N′) = M · N -→⟨ ξ-·ᵣ N→M ⟩ (·ᵣ-↠ M-↠N′)

·ₗ-↠ : M -↠ M′
  → M · N -↠ M′ · N
·ₗ-↠ {M = M} {N = N} (M ∎)             = M · N ∎
·ₗ-↠ {M = M} {N = N} (M -→⟨ M→M₁ ⟩ M₁-↠M′) =
  M · N -→⟨ ξ-·ₗ M→M₁ ⟩ ·ₗ-↠ M₁-↠M′

·-↠ : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
·-↠ {M = M} {M′ = M′} {N = N} {N′ = N′} M-↠M′ N-↠N′ =
  M · N
  -↠⟨ ·ₗ-↠ M-↠M′ ⟩
   M′ · N
  -↠⟨ ·ᵣ-↠ N-↠N′ ⟩
   M′ · N′
   ∎
