module Language.STLC.Normal where

open import Prelude

open import Language.STLC.Term

private
  variable
    Γ : Context
    A B : Typ
    M N L M′ N′ L′ : Γ ⊢ A

infix  3 _⊢ne_ _⊢nf_
infixr 9 ᵒ_ 

data _isNeutral {Γ : Context} : Γ ⊢ A → 𝓤₀ ̇ 
data _isNormal  {Γ : Context} : Γ ⊢ A → 𝓤₀ ̇ 

data _isNeutral {Γ} where
  `_  : (x : Γ ∋ A)
    → (` x) isNeutral 
  _·_ : L isNeutral
    → M isNormal
    → (L · M) isNeutral
  abort
    : M isNormal
    → (abort A M) isNeutral

data _isNormal where
  ᵒ_  : M isNeutral → M isNormal
  ƛ_  : M isNormal  → (ƛ M) isNormal

soundness-normal  : M isNormal  → ¬ (M -→ N)
soundness-neutral : M isNeutral → ¬ (M -→ M′)

soundness-normal (ᵒ M↓) M→N       = soundness-neutral M↓ M→N
soundness-normal (ƛ M↓) (ξ-ƛ M→N) = soundness-normal M↓ M→N
soundness-neutral (` x) ()
soundness-neutral (L↓ · M↓) (ξ-·ₗ L→L′)   = soundness-neutral L↓ L→L′
soundness-neutral (L↓ · M↓) (ξ-·ᵣ M→M′)   = soundness-normal M↓ M→M′
soundness-neutral (abort M) (ξ-abort red) = soundness-normal M red

completeness
  : (M : Γ ⊢ A) → (∀ N → ¬ (M -→ N))
  → M isNormal
completeness (` x) M↛ = ᵒ ` x
completeness (ƛ M) ƛM↛ with completeness M M↛
  where M↛ : ∀ N → ¬ (M -→ N)
        M↛ N M→N = ƛM↛ (ƛ N) (ξ-ƛ M→N)
... | M↓ = ƛ M↓
completeness (M · N) MN↛ with completeness M M↛ | completeness N N↛
  where M↛ : ∀ M′ → ¬ (M -→ M′)
        M↛ M′ M↛ = MN↛ (M′ · N) (ξ-·ₗ M↛)
        N↛ : ∀ N′ → ¬ (N -→ N′)
        N↛ N′ N↛ = MN↛ (M · N′) (ξ-·ᵣ N↛)
... | ᵒ M↓ | N↓ = ᵒ (M↓ · N↓)
... | ƛ M↓ | N↓ = ⊥-elim (MN↛ _ β-ƛ· )
completeness (abort _ M) aM↛ = ᵒ abort (completeness M M↛)
  where M↛ : ∀ N → ¬ (M -→ N)
        M↛ N M-→N = aM↛ (abort _ N) (ξ-abort M-→N)

data _⊢ne_ (Γ : Context) : Typ → 𝓤₀ ̇ 
data _⊢nf_ (Γ : Context) : Typ → 𝓤₀ ̇ 

data _⊢ne_ Γ where
  `_
    : (x : Γ ∋ A)
    → Γ ⊢ne A
  _·_
    : Γ ⊢ne A →̇ B
    → Γ ⊢nf A
    → Γ ⊢ne B
  abort
    : (A : Typ)
    → Γ ⊢nf ⊥̇
    → Γ ⊢ne A
data _⊢nf_ Γ where
  ᵒ_
    : Γ ⊢ne A
    → Γ ⊢nf A
  ƛ_
    : Γ , A ⊢nf B
    → Γ ⊢nf A →̇ B

↑ne_ : Γ ⊢ne A → Γ ⊢ A
↑nf_ : Γ ⊢nf A → Γ ⊢ A
↑ne (` x)     = ` x
↑ne (L · M)   = ↑ne L · (↑nf M)
↑ne abort _ M = abort _ (↑nf M)
↑nf (ᵒ M) = ↑ne M
↑nf (ƛ M) = ƛ (↑nf M)

↑nf-normal  : (M : Γ ⊢nf A) → (↑nf M) isNormal
↑ne-neutral : (M : Γ ⊢ne A) → (↑ne M) isNeutral

↑nf-normal (ᵒ M)        = ᵒ ↑ne-neutral M
↑nf-normal (ƛ M)        = ƛ ↑nf-normal M
↑ne-neutral (` x)       = ` x
↑ne-neutral (L · M)     = ↑ne-neutral L · ↑nf-normal M
↑ne-neutral (abort _ M) = abort (↑nf-normal M)

↓ne : {M : Γ ⊢ A} → M isNeutral → (Γ ⊢ne A)
↓nf : {M : Γ ⊢ A} → M isNormal  → (Γ ⊢nf A)
↓ne (` x)     = ` x
↓ne (L · M)   = ↓ne L · ↓nf M
↓ne (abort M) = abort _ (↓nf M)
↓nf (ᵒ M)     = ᵒ ↓ne M
↓nf (ƛ N)     = ƛ ↓nf N
