module Language.STLC.NormalisationByEval where

open import Function
  using (_∘_)
open import Data.Empty
open import Data.Product

open import Language.STLC.Term
open import Language.STLC.Normal

private
  variable
    Γ Δ Ξ : Context
    A B C : Type
    M N L : Γ ⊢ A

infix 3 _⊆_
data _⊆_ : (Γ Δ : Context) → Set where
  refl : Γ ⊆ Γ
  
  keep : Γ     ⊆ Δ
         -------------
       → Γ , A ⊆ Δ , A

  drop : Γ ⊆ Δ
         ---------
       → Γ ⊆ Δ , A

⊆-trans : Γ ⊆ Δ → Δ ⊆ Ξ → Γ ⊆ Ξ
⊆-trans s        refl     = s
⊆-trans refl     (keep t) = keep t
⊆-trans (keep s) (keep t) = keep (⊆-trans s t)
⊆-trans (drop s) (keep t) = drop (⊆-trans s t)
⊆-trans s        (drop t) = drop (⊆-trans s t)

embedding : Γ ⊆ Δ → Rename Γ Δ
embedding refl       = λ x → x
embedding (keep sub) = ext (embedding sub)
embedding (drop sub) x = S (embedding sub x)

weaken : Γ ⊆ Δ
  → Γ ⊢ A → Δ ⊢ A
weaken = rename ∘ embedding

rename-ne : Rename Γ Δ → Γ ⊢ne A → Δ ⊢ne A
rename-nf : Rename Γ Δ → Γ ⊢nf A → Δ ⊢nf A
rename-ne ρ (` x)       = ` ρ x
rename-ne ρ (L · M)     = rename-ne ρ L · rename-nf ρ M
rename-ne ρ (abort _ M) = abort _ (rename-nf ρ M)
rename-nf ρ (ᵒ M) = ᵒ rename-ne ρ M 
rename-nf ρ (ƛ M) = ƛ rename-nf (ext ρ) M

weaken-nf : Γ ⊆ Δ
  → Γ ⊢nf A → Δ ⊢nf A
weaken-nf = rename-nf ∘ embedding

Tyᴺ : Type → Context → Set
Tyᴺ ⊥̇       Γ = Γ ⊢nf ⊥̇ 
Tyᴺ (A →̇ B) Γ = ∀ {Δ} → Γ ⊆ Δ → Tyᴺ A Δ → Tyᴺ B Δ

data Conᴺ : Context → Context → Set where
  ∅   : Conᴺ ∅ Δ
  _,_ : Conᴺ Γ Δ → Tyᴺ A Δ → Conᴺ (Γ , A) Δ

lookupᴺ : Γ ∋ A
  → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
lookupᴺ Z     (Γ , B) = B
lookupᴺ (S x) (Γ , B) = lookupᴺ x Γ

Tyᴺₑ : Γ ⊆ Δ → Tyᴺ A Γ → Tyᴺ A Δ
Tyᴺₑ {A = ⊥̇}     sub t = weaken-nf sub t
Tyᴺₑ {A = A →̇ B} sub t = λ sub₂ aᴺ → t (⊆-trans sub sub₂) aᴺ

Conᴺₑ : Δ ⊆ Ξ → Conᴺ Γ Δ → Conᴺ Γ Ξ
Conᴺₑ sub ∅         = ∅
Conᴺₑ sub (Γᴺ , Aᴺ) = Conᴺₑ sub Γᴺ , Tyᴺₑ sub Aᴺ

Tmᴺ : Γ ⊢ A → (∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ)
Tmᴺ (` x)       Γ = lookupᴺ x Γ
Tmᴺ (L · M)     Γ = Tmᴺ L Γ refl (Tmᴺ M Γ)
Tmᴺ (ƛ M)       Γ = λ sub a → Tmᴺ M (Conᴺₑ sub Γ , a)
Tmᴺ (abort _ M) Γ = {!!}
