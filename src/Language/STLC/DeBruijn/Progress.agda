module Language.STLC.DeBruijn.Progress where

open import Prelude

open import Language.STLC.DeBruijn.Term
open import Language.STLC.DeBruijn.Normal

private
  variable
    Γ : Cxt
    A : Ty
    M N : Γ ⊢ A

data Progress (M : Γ ⊢ A) : 𝓤₀ ̇ where
  step
    : M -→ N
      ----------
    → Progress M

  done : M isNormal
    → Progress M

progress : (M : Γ ⊢ A) → Progress M
progress (` x) = done (ᵒ ` x)
progress (ƛ M)   with progress M
... | step M→M′ = step (ξ-ƛ M→M′)
... | done M↓   = done (ƛ M↓)
progress (M · N) with progress M | progress N
... | step M→M′  | _         = step (ξ-·ₗ M→M′)
... | _          | step N→N′ = step (ξ-·ᵣ N→N′)
... | done (ᵒ x) | done N↓   = done (ᵒ (x · N↓))
... | done (ƛ _) | done _    = step β-ƛ·
progress (abort _ M) with progress M
... | step M→M′  = step (ξ-abort M→M′)
... | done (ᵒ M) = done (ᵒ abort (ᵒ M))
