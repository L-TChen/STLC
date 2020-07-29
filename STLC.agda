module STLC where

open import Relation.Nullary
open import Data.Empty
  hiding (⊥)
open import Data.Product
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum

open import Size 
open import Data.Nat

open import Context public

infix  3 _⊢_

infixr 7 _→̇_

infixr 5 ƛ_
infixl 7 _·_
infixl 8 _[_]
infixl 8 _⟪_⟫
infixr 9 ᵒ_
infix  9 `_
infix  9 #_

data Type : Set
Cxt  = Context Type
data _⊢_ Cxt : Type → Set

-- remove the following part 
variable
  n m l          : ℕ
  Γ Δ Ξ          : Context Type
  A B C          : Type
  M N L M′ N′ L′ : Γ ⊢ A
  x              : Γ ∋ A

data Type where
  ⊥   : Type
  _→̇_ : Type → Type → Type
  
------------------------------------------------------------------------------
-- Terms = typing rules
data _⊢_ Γ where
  `_ : Γ ∋ A
       -----
     → Γ ⊢ A
{-
  absurd
    : (A : Type)
    → Γ ⊢ ⊥
    → Γ ⊢ A
-}
  _·_
    : Γ ⊢ A →̇ B
    → Γ ⊢ A
      ----------
    → Γ ⊢ B

  ƛ_
    : Γ , A ⊢ B
      ---------
    → Γ ⊢ A →̇ B

#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

------------------------------------------------------------------------------
-- Terms

nat : Type → Type
nat A = (A →̇ A) →̇ A →̇ A

c₀ : ∀ {A} → ∅ ⊢ nat A
c₀ = ƛ ƛ # 0

c₁ : ∀ {A} → ∅ ⊢ nat A
c₁ = ƛ ƛ # 1 · # 0

add : ∀ {A} → ∅ ⊢ nat A →̇ nat A →̇ nat A
add = ƛ ƛ ƛ ƛ # 3 · # 1 · (# 2 · # 1 · # 0)

------------------------------------------------------------------------------
-- Parallel Substitution
-- some exercises here
Rename : Cxt → Cxt → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context Type → Context Type → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)        = ` ρ x
--rename ρ (absurd A M) = absurd A (rename ρ M)
rename ρ (M · N)    = rename ρ M · rename ρ N
rename ρ (ƛ M)      = ƛ rename (ext ρ) M

exts : Subst Γ Δ → Subst (Γ , A) (Δ , A)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ ⊢ A 
  → Subst Γ Δ
  → Δ ⊢ A
(` x)      ⟪ σ ⟫ = σ x
--(absurd A M) ⟪ σ ⟫ = absurd A (M ⟪ σ ⟫)
(M · N)    ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
(ƛ M)      ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫

------------------------------------------------------------------------------
-- Singleton Substitution
-- concrete examples needed 

subst-zero : {B : Type}
  → Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z      =  N
subst-zero _ (S x)  =  ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
       ---------
     → Γ ⊢ A
_[_] N M =  N ⟪ subst-zero M ⟫

------------------------------------------------------------------------------
-- Single-step reduction

infix 3 _-→_
data _-→_ : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : (ƛ M) · N -→ M [ N ]
{- 
  ξ-absurd
    : M -→ M′
    → absurd A M -→ absurd A M′
-}
  ξ-ƛ
    : M -→ M′
    → ƛ M -→ ƛ M′    
  ξ-·ₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·ᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′

------------------------------------------------------------------------------
-- Transitive and reflexive closure of -→ 

infix  2 _-↠_
infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_

data _-↠_ {Γ} : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M
    
  _-→⟨_⟩_
    : ∀ L
    → L -→ M
    → M -↠ N
       -------
    → L -↠ N

_-↠⟨_⟩_ : ∀ L
  → L -↠ M → M -↠ N
  -----------------
  → L -↠ N
M -↠⟨ (_ ∎) ⟩ M-↠N              = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

------------------------------------------------------------------------------
-- -↠ is a congruence (tedious, any better way?)
{-
absurd-↠ : M -↠ M′
  → absurd A M -↠ absurd A M′
absurd-↠ (M ∎)         = (absurd _ M) ∎
absurd-↠ (L -→⟨ L-→M ⟩ M-↠N) = (absurd _ L) -→⟨ ξ-absurd L-→M ⟩ absurd-↠ M-↠N
-}
ƛ-↠ : M -↠ M′ → ƛ M -↠ ƛ M′
ƛ-↠ (_ ∎)                = _ ∎
ƛ-↠ (M -→⟨ M-→M′ ⟩ M-→N) = ƛ M -→⟨ ξ-ƛ M-→M′ ⟩ (ƛ-↠ M-→N)
  
·ₗ-↠ : M -↠ M′ → M · N -↠ M′ · N
·ₗ-↠ (_ ∎)                = _ ∎ 
·ₗ-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = M · _ -→⟨ ξ-·ₗ M-→M′ ⟩ (·ₗ-↠ M-↠N)

·ᵣ-↠ : N -↠ N′ → M · N -↠ M · N′
·ᵣ-↠ (_ ∎)                = _ ∎
·ᵣ-↠ (M -→⟨ M-→M′ ⟩ M-↠N) = _ · M -→⟨ ξ-·ᵣ M-→M′ ⟩ (·ᵣ-↠ M-↠N)

-- 2+ hr up to here

------------------------------------------------------------------------------
-- Normal form

data Neutral : Γ ⊢ A → Set 
data Normal  : Γ ⊢ A → Set 

data Neutral where
  `_  : (x : Γ ∋ A)
    → Neutral (` x)
  _·_ : Neutral L
    → Normal M
    → Neutral (L · M)

data Normal where
  ᵒ_  : Neutral M → Normal M
--  absurd  : M ↑ → absurd A M ↑
  ƛ_  : Normal M  → Normal (ƛ M)

normal-soundness  : Normal M  → ¬ (M -→ M′)
neutral-soundness : Neutral M → ¬ (M -→ M′)
neutral-soundness (` x)     ()
neutral-soundness (L↓ · M↑) (ξ-·ₗ p) = neutral-soundness L↓ p
neutral-soundness (L↓ · M↑) (ξ-·ᵣ p) = normal-soundness M↑ p
normal-soundness (ᵒ M↓)              = neutral-soundness M↓
--normal-soundness (nf-absurd M↑) (ξ-absurd p) = normal-soundness M↑ p
normal-soundness (ƛ M↑)     (ξ-ƛ p)  = normal-soundness M↑ p

normal-completeness : (M : Γ ⊢ A)
  → ((N : Γ ⊢ A) → ¬ (M -→ N))
  → Normal M 
normal-completeness (` x)   M↛N = ᵒ ` x
normal-completeness (ƛ M)   M↛N with normal-completeness M ƛ-nf
  where
    ƛ-nf : ∀ N → ¬ (M -→ N)
    ƛ-nf N M-→N = M↛N (ƛ N) (ξ-ƛ M-→N)
... | M↓ = ƛ M↓
normal-completeness (L · M) M↛N with normal-completeness L ·ₗ-nf | normal-completeness M ·ᵣ-nf
  where
    ·ₗ-nf : ∀ N → ¬ (L -→ N)
    ·ₗ-nf N L-→N = M↛N (N · M) (ξ-·ₗ L-→N)
    ·ᵣ-nf : ∀ N → ¬ (M -→ N)
    ·ᵣ-nf N M-→N = M↛N (L · N) (ξ-·ᵣ M-→N)
... | ᵒ x            | M↓ = ᵒ (x · M↓)
... | ƛ_ {M = L′} L↓ | M↓ = ⊥-elim (M↛N (L′ [ M ]) β-ƛ·)

------------------------------------------------------------------------------
-- Progress

data Progress (M : Γ ⊢ A) : Set where
  step
    : M -→ N
      ----------
    → Progress M

  done : Normal M
    → Progress M

progress : (M : Γ ⊢ A)
  → Progress M
progress (` x)       = done (ᵒ ` x)
progress (ƛ M)       with progress M
... | done M↓   = done (ƛ M↓)
... | step M-→N = step (ξ-ƛ M-→N)
progress (` x · N)   with progress N
... | done M↓    = done (ᵒ (` x · M↓))
... | step N-→N′ = step (ξ-·ᵣ N-→N′)
progress ((ƛ M) · N) = step β-ƛ·
progress (LM@(L · M) · N) with progress LM
... | step LM→K    = step (ξ-·ₗ LM→K)
... | done (ᵒ LM↓) with progress N
...   | step N-→N′ = step (ξ-·ᵣ N-→N′)
...   | done N↓    = done (ᵒ (LM↓ · N↓))
