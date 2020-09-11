open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  hiding ([_])

open import Context public

infix  3 _⊢_
infixr 5 ƛ_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infixr 9 ᵒ_ `_ #_

data _⊢_ (Γ : Context) : Type → Set

variable
  Γ Δ Ξ : Context
  A B C : Type
  x     : Γ ∋ A
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

  
#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n

nat : Type → Type
nat A = (A →̇ A) →̇ A →̇ A

Rename : Context → Context → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)   = ` ρ x
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (ƛ M)   = ƛ rename (ext ρ) M

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

data _-↠_ {Γ A} : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M       -- empty list
    
  _-→⟨_⟩_
    : ∀ L          -- this can usually be inferred by the following reduction 
    → L -→ M       -- the head of a list 
    → M -↠ N       -- the tail
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
  ƛ_  : Normal M  → Normal (ƛ M)

normal-soundness  : Normal M  → ¬ (M -→ N)
neutral-soundness : Neutral M → ¬ (M -→ M′)

normal-soundness (ᵒ M↓) M→N       = neutral-soundness M↓ M→N
normal-soundness (ƛ M↓) (ξ-ƛ M→N) = normal-soundness M↓ M→N
neutral-soundness (` x) ()
neutral-soundness (L↓ · M↓) (ξ-·ₗ L→L′) = neutral-soundness L↓ L→L′
neutral-soundness (L↓ · M↓) (ξ-·ᵣ M→M′) = normal-soundness M↓ M→M′

normal-completeness
  : (M : Γ ⊢ A) → (∀ N → ¬ (M -→ N))
  → Normal M 
normal-completeness (` x) M↛ = ᵒ ` x
normal-completeness (ƛ M) ƛM↛ with normal-completeness M M↛
  where M↛ : ∀ N → ¬ (M -→ N)
        M↛ N M→N = ƛM↛ (ƛ N) (ξ-ƛ M→N)
... | M↓ = ƛ M↓
normal-completeness (M · N) MN↛ with normal-completeness M M↛ | normal-completeness N N↛
  where M↛ : ∀ M′ → ¬ (M -→ M′)
        M↛ M′ M↛ = MN↛ (M′ · N) (ξ-·ₗ M↛)
        N↛ : ∀ N′ → ¬ (N -→ N′)
        N↛ N′ N↛ = MN↛ (M · N′) (ξ-·ᵣ N↛)
... | ᵒ M↓ | N↓ = ᵒ (M↓ · N↓)
... | ƛ M↓ | N↓ = ⊥-elim (MN↛ _ β-ƛ· )

data Progress (M : Γ ⊢ A) : Set where
  step
    : M -→ N
      ----------
    → Progress M

  done : Normal M
    → Progress M

progress : (M : Γ ⊢ A) → Progress M
progress (` x)   = done (ᵒ ` x)
progress (ƛ M)   with progress M
... | step M→M′ = step (ξ-ƛ M→M′)
... | done M↓   = done (ƛ M↓)
progress (M · N) with progress M | progress N
... | step M→M′  | _         = step (ξ-·ₗ M→M′)
... | _          | step N→N′ = step (ξ-·ᵣ N→N′)
... | done (ᵒ x) | done N↓   = done (ᵒ (x · N↓))
... | done (ƛ _) | done _    = step β-ƛ·
