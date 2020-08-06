{-# OPTIONS --allow-unsolved-metas #-} 
module Normalisation where

open import Data.Product as Prod
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum

open import STLC
open import Substitution

----------------------------------------------------------------------
-- Weak normalisation property

infix 3 _⇓_ _⇑

data _⇓_ : (x : Γ ∋ A) → (Γ ⊢ B) → Set 
data _⇑ : Γ ⊢ A → Set

data _⇓_  where
  `_ : (x : Γ ∋ A) → x ⇓ ` x

  _·_ : x ⇓ L → M ⇑
    → x ⇓ L · M

data _⇑ where
{-
  wn-absurd : {M : Γ ⊢ ⊥}
    → M ⇑
    → absurd A M ⇑
-}
  ƛ_ : M ⇑
    --------
    → ƛ M ⇑

  ᵒ_ : {x : Γ ∋ A} {M : Γ ⊢ B}
    → x ⇓ M → M ⇑

  _-→⟨_⟩_ : (M : Γ ⊢ A) {M′ : Γ ⊢ A}
    → M -→ M′
    → M′ ⇑
    ---------
    → M  ⇑
    
⇑-Rename : Rename Γ Δ → Set
⇑-Rename ρ = {A : Type} (x : _ ∋ A) → ` (ρ x) ⇑

⇑-Subst : Subst Γ Δ → Set
⇑-Subst  σ = {A : Type} → (x : _ ∋ A) → σ x ⇑

------------------------------------------------------------------------------
-- Variable renaming respects the weak normalistion property

⇓-rename : (ρ : Rename Γ Δ)
  → x ⇓ M
  → ρ x ⇓ rename ρ M 
⇑-rename : (ρ : Rename Γ Δ)
  → M ⇑
  → rename ρ M ⇑
⇓-rename ρ (` x)           = ` ρ x
⇓-rename ρ (⇑M · ⇓N) = (⇓-rename ρ ⇑M) · (⇑-rename ρ ⇓N)
⇑-rename ρ (ƛ wnM)       = ƛ (⇑-rename (ext ρ) wnM)
--⇑-rename ρ (wn-absurd wnM)    = wn-absurd (⇑-rename ρ wnM)
⇑-rename ρ (ᵒ x)          = ᵒ ⇓-rename ρ x
⇑-rename ρ (_ -→⟨ M→M′ ⟩ wnM) = _ -→⟨ rename-reduce M→M′ ⟩ (⇑-rename ρ wnM)

⇑-ext-subst : {σ : Subst Γ Δ}
  → ⇑-Subst σ
    ------------------------
  → ⇑-Subst (exts {A = A} σ)
⇑-ext-subst wnσ Z     = ᵒ ` Z
⇑-ext-subst wnσ (S x) = ⇑-rename S_ (wnσ x)

------------------------------------------------------------------------------
-- Substitution respects the weak normalisation property.

⇑-subst : {σ : Subst Γ Δ} {A : Type} {M : Γ ⊢ A}
  → ⇑-Subst σ
  → M ⇑
  -----------------
  → M ⟪ σ ⟫ ⇑
⇓-subst : {σ : Subst Γ Δ} {A : Type} {M : Γ ⊢ A}
  → ⇑-Subst σ
  → x ⇓ M
  -----------
  → M ⟪ σ ⟫ ⇑ 
{-# TERMINATING #-} -- to be removed
⇑-app : {A B : Type} {M : Γ ⊢ A →̇ B} {N : Γ ⊢ A}
  → M ⇑ → N ⇑
    ----------
  → M · N ⇑
--⇑-subst wnσ (wn-absurd wnM)     = wn-absurd (⇑-subst wnσ wnM)
⇑-subst wnσ (ƛ wnM)       = ƛ (⇑-subst (⇑-ext-subst wnσ) wnM)
⇑-subst wnσ (ᵒ wneM)      = ⇓-subst wnσ wneM
⇑-subst wnσ (M -→⟨ M-→N ⟩ ⇑N) = M ⟪ _ ⟫ -→⟨ subst-reduce M-→N ⟩ ⇑-subst wnσ ⇑N
⇓-subst wnσ (` x)         = wnσ x
⇓-subst wnσ (wnL · wneM)  = ⇑-app (⇓-subst wnσ wnL) (⇑-subst wnσ wneM)
--⇑-app (wn-absurd wnM)      wnN  = {!!}
⇑-app {M = M} {N} (ƛ M⇑) N⇑ = (ƛ _) · N -→⟨ β-ƛ· ⟩ ⇑-subst ⇑-σ M⇑
  where
    ⇑-σ : ⇑-Subst (subst-zero N)
    ⇑-σ Z     = N⇑
    ⇑-σ (S x) = ᵒ ` x
⇑-app (ᵒ wnex)    wnN = ᵒ (wnex · wnN) 
⇑-app (_ -→⟨ x ⟩ wnM) wnN = _ -→⟨ ξ-·ₗ x ⟩ (⇑-app wnM wnN )

------------------------------------------------------------------------------
-- Lemma. Every well-typed term M is weakly normalising

weak-normalisation : (M : Γ ⊢ A) → M ⇑
weak-normalisation (` x)   = ᵒ ` x
--weak-normalisation (absurd _ M) = wn-absurd (weak-normalisation M)
weak-normalisation (M · N) = ⇑-app (weak-normalisation M)  (weak-normalisation N)
weak-normalisation (ƛ M)   = ƛ weak-normalisation M

------------------------------------------------------------------------------
-- Lemma. Every weakly normalising term does reduce to a normal form.

ne-soundness : x ⇓ M
  → ∃[ M′ ] (Neutral M′ × (M -↠ M′))
nf-soundness : M ⇑
  → ∃[ M′ ] (Normal M′ × (M -↠ M′))
ne-soundness (` x)  = ⟨ ` _ , ⟨ ` _ , (` x) ∎ ⟩ ⟩
ne-soundness (_·_ {L = L} {M = M} wneL wnM) with ne-soundness wneL | nf-soundness wnM
... | ⟨ L′ , ⟨ neL′ , p ⟩ ⟩ | ⟨ M′ , ⟨ nfM′ , q ⟩ ⟩ = ⟨ L′ · M′ , ⟨ neL′ · nfM′ ,
  L · M -↠⟨ ·ₗ-↠ p ⟩ L′ · M -↠⟨ ·ᵣ-↠ q ⟩ (L′ · M′) ∎ ⟩ ⟩
--nf-soundness (wn-absurd wnf) with nf-soundness wnf
--... | ⟨ M′ , ⟨ nfM′ , p ⟩ ⟩   = ⟨ absurd _ M′ , ⟨ nf-absurd nfM′ , absurd-↠ p ⟩ ⟩
nf-soundness (ƛ wnf) with nf-soundness wnf
... | ⟨ M′ , ⟨ nfM′ , p ⟩ ⟩   = ⟨ ƛ M′ , ⟨ ƛ nfM′ , ƛ-↠ p ⟩ ⟩
nf-soundness (ᵒ x)    with ne-soundness x
... | ⟨ M′ , ⟨ neM′ , M-↠M′ ⟩ ⟩ = ⟨ M′ , ⟨ ᵒ neM′  , M-↠M′ ⟩ ⟩
nf-soundness (_-→⟨_⟩_ M {M′} p nfM′) with nf-soundness nfM′
... | ⟨ M′′ , ⟨ nfM′′ , q ⟩ ⟩ = ⟨ M′′ , ⟨ nfM′′ , M -→⟨ p ⟩ M′ -↠⟨ q ⟩ M′′ ∎ ⟩ ⟩ 

------------------------------------------------------------------------------
-- Corollary. Every well-typed term does reduce to a normal form.

normalise : (M : Γ ⊢ A) → ∃[ N ] (Normal N × (M -↠ N))
normalise M = nf-soundness (weak-normalisation M)

------------------------------------------------------------------------------
-- Strong normalisation
