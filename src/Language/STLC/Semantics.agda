module Language.STLC.Semantics where

open import Prelude
open import Language.STLC.Term
open import Language.STLC.Substitution

open import Semantics.CwF

λ→ : SCwF 𝓤₀ ⊤
λ→ = record
  { Ctx   = Context ; ⋄ = ∅
  ; Sub   = λ Γ Δ → Subst Δ Γ
  ; Ty    = Typ
  ; ⟦_⟧𝓑  = λ x → ⊥̇
  ; Tm    = _⊢_
  ; _,_   = _,_
  ; ⟪_⟫_  = λ σ M → M ⟪ σ ⟫
  ; ids   = ids
  ; _⨟_   = λ σ τ → τ ⨟ σ
  ; ⟨_,_⟩ = λ { σ M Z → M ; σ M (S x) → σ x}
  ; p     = `_ ∘ S_
  ; q     = ` Z
  ; isSCwF = record
       { ctxIsPreCategory = record
         { identity = (λ f i x → f x) , λ γ i x → subst-idL (γ x) i
         ; assoc    = λ { {f = f} {g} {h} i x   → subst-assoc g f (h x) (~ i) }
         }
       ; ⋄isTerminal      = (λ { Γ () }) , ((λ {i ()}) , λ {σ i ()}) 
       ; ⟪⟫-preserves-ids = subst-idL
       ; ⟪⟫-preserves-⨟   = λ M σ τ → sym (subst-assoc σ τ M) 
       ; ctxComprehension = λ γ a → (λ i x → γ x) , refl
       ; idExt            = λ { i Z → ` Z ; i (S x) → ` (S x)}
       ; compExt          = λ { M σ₁ σ₂ i Z → M ⟪ σ₂ ⟫ ; M σ₁ σ₂ i (S x) → σ₁ x ⟪ σ₂ ⟫ }
       }
  }
