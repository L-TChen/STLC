module Language.STLC.Consistency where

open import Data.Unit
open import Data.Empty

open import Language.STLC.Term

private
  variable
    A : Type
    Γ : Context

⟦_⟧ty : Type → Set
⟦ ⊥̇     ⟧ty = ⊥
⟦ A →̇ B ⟧ty = ⟦ A ⟧ty → ⟦ B ⟧ty

⟦_⟧cxt : Context → Set
⟦ Γ ⟧cxt = ∀ {A} → Γ ∋ A → ⟦ A ⟧ty

update : ⟦ Γ ⟧cxt → ⟦ A ⟧ty → ⟦ Γ , A ⟧cxt
update Γ a Z     = a
update Γ a (S x) = Γ x

⟦_⟧tm : Γ ⊢ A → ⟦ Γ ⟧cxt → ⟦ A ⟧ty
⟦ ` x     ⟧tm env = env x
⟦ abort _ M ⟧tm env = ⊥-elim (⟦ M ⟧tm env)
⟦ M · N   ⟧tm env = ⟦ M ⟧tm env (⟦ N ⟧tm env)
⟦ ƛ M     ⟧tm env a = ⟦ M ⟧tm (update env a)

⟦_⟧ : ∅ ⊢ A → ⟦ A ⟧ty
⟦ M ⟧ = ⟦ M ⟧tm λ ()

consistency : ∅ ⊢ ⊥̇ → ⊥
consistency = ⟦_⟧
