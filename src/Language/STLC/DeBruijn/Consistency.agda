module Language.STLC.DeBruijn.Consistency where

open import Prelude
open import Language.STLC.DeBruijn.Term

private
  variable
    A : Ty
    Γ : Cxt

⟦_⟧ty : Ty → 𝓤₀ ̇
⟦ ⊥̇     ⟧ty = ⊥
⟦ A →̇ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

⟦_⟧cxt : Cxt → 𝓤₀ ̇
⟦ Γ ⟧cxt = ∀ {A} → Γ ∋ A → ⟦ A ⟧ty

update : ⟦ Γ ⟧cxt → ⟦ A ⟧ty → ⟦ Γ , A ⟧cxt
update Γ a Z     = a
update Γ a (S x) = Γ x

⟦_⟧tm : Γ ⊢ A → ⟦ Γ ⟧cxt → ⟦ A ⟧ty
⟦ ` x     ⟧tm env = env x
⟦ abort _ M ⟧tm env = ⊥-elim (⟦ M ⟧tm env)
⟦ M · N   ⟧tm env = ⟦ M ⟧tm env (⟦ N ⟧tm env)
⟦ ƛ M     ⟧tm env = λ a → ⟦ M ⟧tm (update env a)

⟦_⟧ : ∅ ⊢ A → ⟦ A ⟧ty
⟦ M ⟧ = ⟦ M ⟧tm λ ()

consistency : ∅ ⊢ ⊥̇ → ⊥
consistency = ⟦_⟧
