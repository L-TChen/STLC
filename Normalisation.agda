module Normalisation where

open import Data.Product as Prod
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum

open import STLC
open import Substitution

----------------------------------------------------------------------
-- Weak normalisation property

data WeakNeutral {Γ A} : Γ ∋ A → Γ ⊢ B → Set 
data WeakNormal  {Γ} : Γ ⊢ A → Set

data WeakNeutral {Γ A} where
  `_ : (x : Γ ∋ A)
       -------------------
     → WeakNeutral x (` x)

  _·_
    : WeakNeutral x L
    → WeakNormal M
    → WeakNeutral x (L · M)

data WeakNormal {Γ} where
  ƛ_ : WeakNormal M
       ------------
    →  WeakNormal (ƛ M)

  ᵒ_ : WeakNeutral x M
    → WeakNormal M

  _-→⟨_⟩_ : (M : Γ ⊢ A) {M′ : Γ ⊢ A}
    → M -→ M′
    → WeakNormal M′
      ------------
    → WeakNormal M
    
------------------------------------------------------------------------------
-- Lemma. Every weakly normalising term is reducible to term in normal form.

wne-soundness : WeakNeutral x M
  → ∃[ M′ ] (Neutral M′ × (M -↠ M′))
wnf-soundness : WeakNormal M
  → ∃[ M′ ] (Normal M′ × (M -↠ M′))
wne-soundness (` x)     = ⟨ ` x , ⟨ ` x , ` x ∎ ⟩ ⟩
wne-soundness (M⇓ · N⇓) with wne-soundness M⇓ | wnf-soundness N⇓
... | ⟨ M′ , ⟨ M′↓ , r₁ ⟩ ⟩ | ⟨ N′ , ⟨ N′↓ , r₂ ⟩ ⟩
  = ⟨ M′ · N′ , ⟨ M′↓ · N′↓ , ·-↠ r₁ r₂ ⟩ ⟩
wnf-soundness (ƛ M⇓)    with wnf-soundness M⇓
... | ⟨ M , ⟨ M⇓′ , r ⟩ ⟩ = ⟨ ƛ M , ⟨ ƛ M⇓′ , ƛ-↠ r ⟩ ⟩
wnf-soundness (ᵒ M⇓) with wne-soundness M⇓
... | ⟨ M , ⟨ M⇓′ , r ⟩ ⟩ = ⟨ M , ⟨ ᵒ M⇓′ , r ⟩ ⟩
wnf-soundness (M -→⟨ M-→N ⟩ N⇓) with wnf-soundness N⇓
... | ⟨ M′ , ⟨ M′⇓ , r ⟩ ⟩ = ⟨ M′ , ⟨ M′⇓ , M -→⟨ M-→N ⟩ r ⟩ ⟩

------------------------------------------------------------------------------
-- Variable renaming respects the weak normalistion property

wnf-Subst : Subst Γ Δ → Set
wnf-Subst  σ = {A : Type} → (x : _ ∋ A) → WeakNormal (σ x)

wne-rename : (ρ : Rename Γ Δ)
  → WeakNeutral x M
  → WeakNeutral (ρ x) (rename ρ M)
wnf-rename : (ρ : Rename Γ Δ)
  → WeakNormal M
  → WeakNormal (rename ρ M)
wne-rename ρ (` x)             = ` ρ x
wne-rename ρ (M · N)           = (wne-rename ρ M) · (wnf-rename ρ N)
wnf-rename ρ (ƛ M)             = ƛ (wnf-rename (ext ρ) M)
wnf-rename ρ (ᵒ x)             = ᵒ wne-rename ρ x
wnf-rename ρ (M -→⟨ M→M′ ⟩ M′) =
  rename ρ M -→⟨ rename-reduce M→M′ ⟩ (wnf-rename ρ M′)

wnf-ext-subst : {σ : Subst Γ Δ}
  → wnf-Subst σ
    ------------------------
  → wnf-Subst (exts {A = A} σ)
wnf-ext-subst wnσ Z     = ᵒ ` Z
wnf-ext-subst wnσ (S x) = wnf-rename S_ (wnσ x)

------------------------------------------------------------------------------
-- Substitution respects the weak normalisation property.

private
  variable
    σ : Subst Γ Δ

nf-Subst : Subst Γ Δ → Set
nf-Subst σ = {A : Type} → (x : _ ∋ A) → Normal (σ x)

wnf-subst
  : wnf-Subst σ
  → WeakNormal M
    ------------------
  → WeakNormal (M ⟪ σ ⟫)

wne-subst
  : wnf-Subst σ
  → WeakNeutral x M
    ------------------
  → WeakNormal (M ⟪ σ ⟫)

{-# TERMINATING #-} -- how to prove it?
wnf-app
  : WeakNormal M
  → WeakNormal N
    ----------
  → WeakNormal (M · N)

wnf-subst σ (ƛ M) = ƛ wnf-subst (wnf-ext-subst σ) M
wnf-subst σ (ᵒ M) = wne-subst σ M 
wnf-subst σ (M -→⟨ M→N ⟩ N↓) = M ⟪ _ ⟫ -→⟨ subst-reduce M→N ⟩ wnf-subst σ N↓
wne-subst σ (` x)   = σ x
wne-subst σ (M · N) = wnf-app (wne-subst σ M) (wnf-subst σ N)
wnf-app {N = N} (ƛ_ {M = M} M⇓) N⇓ =
  (ƛ M) · N -→⟨ β-ƛ· ⟩ wnf-subst wnf-σ M⇓ 
  where
    wnf-σ : wnf-Subst (subst-zero N)
    wnf-σ Z     = N⇓
    wnf-σ (S x) = ᵒ ` x
wnf-app (ᵒ M⇓) N⇓           = ᵒ (M⇓ · N⇓)
wnf-app (L -→⟨ L→M ⟩ M⇓) N⇓ = L · _ -→⟨ ξ-·ₗ L→M ⟩ wnf-app M⇓ N⇓

-- ------------------------------------------------------------------------------
-- -- Lemma. Every well-typed term M is weakly normalising

weak-normalising : (M : Γ ⊢ A) → WeakNormal M
weak-normalising (` x)   = ᵒ ` x
weak-normalising (M · N) = wnf-app (weak-normalising M) (weak-normalising N)
weak-normalising (ƛ M)   = ƛ weak-normalising M

------------------------------------------------------------------------------
-- Corollary. Every well-typed term does reduce to a normal form.

normalise : (M : Γ ⊢ A) → ∃[ N ] (Normal N × (M -↠ N))
normalise M = wnf-soundness (weak-normalising M)
