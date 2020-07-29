module Substitution where

open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong; cong₂; cong-app)

open import STLC hiding (_∎)

------------------------------------------------------------------------------
-- Monad Laws for Parallel Substitution
-- 
-- T. Altenkirch and B. Reus, “Monadic Presentations of Lambda Terms Using Generalized Inductive Types,” in Computer Science Logic. CSL 1999, vol. 1683, J. Flum and M. Rodriguez-Artalejo, Eds. Springer, Berlin, Heidelberg, 1999, pp. 453–468. 
-- T. Altenkirch, J. Chapman, and T. Uustalu, “Monads need not be endofunctors,” LMCS, vol. 11, no. 1, pp. 1–40, 2015.

-- A relative monad on a functor J : 𝕁 → ℂ consits of
--   1. (monad)  a map on objects T : |𝕁| → |ℂ|
--   2. (return) for any X ∈ |𝕁| a map ηₓ : JX → TX 
--   3. (bind)   for any X, Y ∈ |𝕁| and f : JX → TY, a map f* : TX → TY called the Kleisli extension of f.
-- satisfying the usual monad laws.

-- _⊢_  is a relative monad formed by
--   1. 𝕁 = Obj : Context Type
--          Mor : (ρ : {A : Type} → Γ ∋ A → Δ ∋ A)
-- 
--      equivalently, 𝕁(Γ, Δ) = Rename Γ Δ
--
--   2. ℂ = [Type, Set] (in which Type is merely a discrete category) 
-- 
--                         f : 𝒫 ⇒ 𝒬
--                     ==========================
--                     f : {A : Type} → 𝒫 A → 𝒬 A
-- 
--   3. JΓ = Γ ∋_ : Type → Set 
--      Jρ = ρ : ∀ {A} → Γ ∋ A → Δ ∋ A
-- 
--   4. T: Context Type → [Type, Set]
--                    Γ ↦ Γ ⊢_
-- 
--   5. η = `_ : Γ ∋_ ⇒ Γ ⊢_
-- 
--   6. Given σ ∈ ℂ(JΓ, TΔ) = Subst Γ Δ, we have ⟪ σ ⟫ : Γ ⊢_ ⇒ Δ ⊢_ as the Kleisli extension, i.e.
-- 
--      σ : ∀ {A} → Γ ∋ A → Δ ⊢ A
--      -----------------------------
--      ⟪ σ ⟫ : ∀ {A} → Γ ⊢ A → Δ ⊢ A

infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
(σ ⨟ τ) x = σ x ⟪ τ ⟫ 

ids : Subst Γ Γ
ids = `_

----------------------------------------------------------------------
-- Congruence rules
rename-cong : {ρ₁ ρ₂ : Rename Γ Δ}
  → (∀ {A} (x : Γ ∋ A) → ρ₁ x ≡ ρ₂ x)
  → (M : Γ ⊢ A)
  → rename ρ₁ M ≡ rename ρ₂ M
rename-cong p (` x)      = cong `_ (p x)
--rename-cong p (absurd A M) = cong (absurd A) (rename-cong p M)
rename-cong p (M · N)    =
  cong₂ _·_ (rename-cong p M) (rename-cong p N)
rename-cong p (ƛ M)      =
  cong ƛ_ (rename-cong (λ { Z → refl ; (S x) → cong S_ (p x)}) M)

subst-cong : {σ₁ σ₂ : Subst Γ Δ}
  → (∀ {A} (x : Γ ∋ A) → σ₁ x ≡ σ₂ x)
  → (M : Γ ⊢ A)
  → M ⟪ σ₁ ⟫ ≡ M ⟪ σ₂ ⟫
subst-cong p (` x)      = p x
--subst-cong p (absurd A M) = cong (absurd A) (subst-cong p M)
subst-cong p (M · N)    = cong₂ _·_ (subst-cong p M) (subst-cong p N)
subst-cong p (ƛ M)      = cong ƛ_ (subst-cong 
  (λ {Z → refl ; (S x) → cong (rename S_) (p x)}) M)

----------------------------------------------------------------------
-- Properties of ext 

ext-comp : (ρ₁ : Rename Γ Δ) (ρ₂ : Rename Δ Ξ)
  → (x : Γ , B ∋ A)
  → (ext ρ₂ ∘ ext ρ₁) x ≡ ext (ρ₂ ∘ ρ₁) x
ext-comp ρ₁ ρ₂ Z     = refl
ext-comp ρ₁ ρ₂ (S x) = refl

----------------------------------------------------------------------
-- Properties of Rename

ren : Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ

rename=subst-ren
  : {ρ : Rename Γ Δ}
  → (M : Γ ⊢ A)
  → rename ρ M ≡ M ⟪ ren ρ ⟫
rename=subst-ren (` x)      = refl
--rename=subst-ren (absurd A M) = cong (absurd A) (rename=subst-ren M)
rename=subst-ren (M · N)    =
  cong₂ _·_ (rename=subst-ren M) (rename=subst-ren N)
rename=subst-ren {ρ = ρ} (ƛ M)      = cong ƛ_ (begin
  rename (ext ρ) M
    ≡⟨ rename=subst-ren M ⟩
  M ⟪ ren (ext ρ) ⟫
    ≡⟨ subst-cong (ren-ext ρ) M ⟩
  M ⟪ exts (ren ρ) ⟫
    ∎)
  where
    open PropEq.≡-Reasoning
    ren-ext : (ρ : Rename Γ Δ)
      → ∀ {B} (x : Γ , A ∋ B) → ren (ext ρ) x ≡ exts (ren ρ) x
    ren-ext ρ Z     = refl
    ren-ext ρ (S x) = refl

rename-comp
  : (ρ₁ : Rename Γ Δ) (ρ₂ : Rename Δ Ξ)
  → {M : Γ ⊢ A}
  → rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M
rename-comp ρ₁ ρ₂ {M = ` x}      = refl
--rename-comp ρ₁ ρ₂ {M = absurd A M} = cong (absurd A) (rename-comp ρ₁ ρ₂)
rename-comp ρ₁ ρ₂ {M = M · N}    = cong₂ _·_ (rename-comp ρ₁ ρ₂) (rename-comp ρ₁ ρ₂)
rename-comp ρ₁ ρ₂ {M = ƛ M}      = cong ƛ_ (begin
  rename (ext ρ₂) (rename (ext ρ₁) M)
    ≡⟨ rename-comp (ext ρ₁) (ext ρ₂) ⟩
  rename (ext ρ₂ ∘ ext ρ₁) M
    ≡⟨ rename-cong (ext-comp ρ₁ ρ₂) M ⟩
  rename (ext (ρ₂ ∘ ρ₁))   M
  ∎)
  where open PropEq.≡-Reasoning

----------------------------------------------------------------------
-- punchIn: Weakening at any position

punchIn : ∀ A {Γ₁} Γ₂ → Rename (Γ₁ ⧺ Γ₂) (Γ₁ , A ⧺ Γ₂)
punchIn _ ∅       Z     = S Z
punchIn _ ∅       (S x) = S (S x)
punchIn _ (Δ , C) Z     = Z
punchIn _ (Δ , C) (S x) = S punchIn _ Δ x

punchesIn : ∀ Ξ → Subst Γ Δ → Subst (Γ ⧺ Ξ) (Δ ⧺ Ξ)
punchesIn ∅       σ x     = σ x
punchesIn (Ξ , C) σ Z     = ` Z
punchesIn (Ξ , C) σ (S x) = rename S_ (punchesIn Ξ σ x)

ext-punchIn=punchIn : (x : Γ ⧺ Ξ , B ∋ C)
  → ext (punchIn A Ξ) x ≡ punchIn A (Ξ , B) x
ext-punchIn=punchIn {Ξ = ∅}     Z     = refl
ext-punchIn=punchIn {Ξ = ∅}     (S x) = refl
ext-punchIn=punchIn {Ξ = Ξ , B} Z     = refl
ext-punchIn=punchIn {Ξ = Ξ , B} (S x) = refl

exts-punchesIn=punchesIn : {σ : Subst Γ Δ}
  → (x : Γ ⧺ Ξ , B ∋ A)
  → exts (punchesIn Ξ σ) x ≡ punchesIn (Ξ , B) σ x
exts-punchesIn=punchesIn Z     = refl
exts-punchesIn=punchesIn (S x) = refl

S=punchIn : (x : Γ ∋ A) → S x ≡ punchIn B ∅ x
S=punchIn Z     = refl
S=punchIn (S x) = refl

punchesIn-punchIn-comm : (σ : Subst Γ Δ)
  → (x : Γ ⧺ Ξ ∋ A)
  → punchesIn Ξ (exts σ) (punchIn B Ξ x) ≡ rename (punchIn B Ξ) (punchesIn Ξ σ x)
punchesIn-punchIn-comm {Ξ = ∅}     σ Z     = rename-cong S=punchIn (σ Z)
punchesIn-punchIn-comm {Ξ = ∅}     σ (S x) = rename-cong S=punchIn (σ (S x))
punchesIn-punchIn-comm {Ξ = Ξ , C} σ Z     = refl
punchesIn-punchIn-comm {Ξ = Ξ , C} σ (S x) = begin
  rename S_ (punchesIn Ξ (exts σ) (punchIn _ Ξ x))
    ≡⟨ cong (rename S_) (punchesIn-punchIn-comm σ x) ⟩
  rename S_ (rename (punchIn _ Ξ) (punchesIn Ξ σ x))
    ≡⟨ rename-comp (punchIn _ Ξ) S_ ⟩
  rename (S_ ∘ (punchIn _ Ξ)) (punchesIn Ξ σ x)
    ≡⟨⟩
  rename ((punchIn _ (Ξ , C)) ∘ S_) (punchesIn Ξ σ x)
    ≡⟨ sym (rename-comp S_ (punchIn _ (Ξ , C))) ⟩
  rename (punchIn _ (Ξ , C)) (rename S_ (punchesIn Ξ σ x))
    ∎
  where open PropEq.≡-Reasoning

punchIn-punchesIn-comm : (σ : Subst Γ Δ)
  → (M : Γ ⧺ Ξ ⊢ A)
  → rename (punchIn B Ξ) M ⟪ punchesIn Ξ (exts σ) ⟫
   ≡ rename (punchIn B Ξ) (M ⟪ punchesIn Ξ σ ⟫)
punchIn-punchesIn-comm σ (` x)      = punchesIn-punchIn-comm σ x
--punchIn-punchesIn-comm σ (absurd A M) = cong (absurd A) (punchIn-punchesIn-comm σ M)
punchIn-punchesIn-comm σ (M · N)    = cong₂ _·_ (punchIn-punchesIn-comm σ M) (punchIn-punchesIn-comm σ N)
punchIn-punchesIn-comm σ (ƛ M) = cong ƛ_ (begin
  rename (ext (punchIn _ _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡⟨ cong _⟪ exts (punchesIn _ (exts σ)) ⟫ (rename-cong ext-punchIn=punchIn M) ⟩
  rename (punchIn _ (_ , _)) M ⟪ exts (punchesIn _ (exts σ)) ⟫
    ≡⟨ subst-cong exts-punchesIn=punchesIn (rename (punchIn _ (_ , _)) M) ⟩
  rename (punchIn _ (_ , _)) M ⟪ punchesIn (_ , _) (exts σ) ⟫
    ≡⟨ punchIn-punchesIn-comm σ M ⟩
  rename (punchIn _ (_ , _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡⟨ rename-cong (sym ∘ ext-punchIn=punchIn) (M ⟪ punchesIn (_ , _) σ ⟫) ⟩
  rename (ext (punchIn _ _)) (M ⟪ punchesIn (_ , _) σ ⟫)
    ≡⟨ cong (rename (ext (punchIn _ _))) (subst-cong (sym ∘ exts-punchesIn=punchesIn) M) ⟩
  rename (ext (punchIn _ _)) (M ⟪ exts (punchesIn _ σ) ⟫)
    ∎)
  where open PropEq.≡-Reasoning

rename-exts : (σ : Subst Γ Δ)
  → (M : Γ ⊢ A)
  → rename (S_ {B = B}) M ⟪ exts σ ⟫ ≡ rename S_ (M ⟪ σ ⟫)
rename-exts σ M = begin
  rename S_ M ⟪ exts σ ⟫
    ≡⟨ cong _⟪ exts σ ⟫ (rename-cong S=punchIn M) ⟩
  rename (punchIn _ ∅) M ⟪ punchesIn ∅ (exts σ) ⟫
    ≡⟨ punchIn-punchesIn-comm σ M ⟩
  rename (punchIn _ ∅) (M ⟪ σ ⟫)
    ≡⟨ rename-cong (sym ∘ S=punchIn) (M ⟪ σ ⟫) ⟩
  rename S_ (M ⟪ σ ⟫)
    ∎ 
  where open PropEq.≡-Reasoning

ren-ext-comm : (ρ : Rename Γ Δ)
    → (x : Γ , B ∋ A)
    → ren (ext ρ) x ≡ exts (ren ρ) x
ren-ext-comm ρ Z     = refl
ren-ext-comm ρ (S _) = refl

----------------------------------------------------------------------
-- Monad Laws 

subst-idR : (σ : Subst Γ Δ) {x : Γ ∋ A}
  → ` x ⟪ σ ⟫ ≡ σ x
subst-idR σ = refl

subst-idL
  : (M : Γ ⊢ A)
  → M ⟪ ids ⟫ ≡ M
subst-idL (` x)      = refl
--subst-idL (absurd A M) = cong (absurd A) (subst-idL M)
subst-idL (M · N)    = cong₂ _·_    (subst-idL M) (subst-idL N)
subst-idL (ƛ_ M)     = begin
  ƛ M ⟪ exts ids ⟫ 
    ≡⟨ cong ƛ_ (subst-cong exts-ids=ids M) ⟩ 
  ƛ M ⟪ ids ⟫
    ≡⟨ cong ƛ_ (subst-idL M) ⟩
  ƛ M  ∎
  where
    open PropEq.≡-Reasoning
    exts-ids=ids : (x : Γ , A ∋ B) → (exts ids) x ≡ ids x
    exts-ids=ids Z     = refl
    exts-ids=ids (S x) = refl

subst-assoc
  : (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Ξ)
  → (M : Γ ⊢ A)
  →  M ⟪ σ₁ ⟫ ⟪ σ₂ ⟫ ≡ M ⟪ σ₁ ⨟ σ₂ ⟫
subst-assoc σ₁ σ₂ (` x)      = refl
--subst-assoc σ₁ σ₂ (absurd A M) = cong (absurd A) (subst-assoc σ₁ σ₂ M)
subst-assoc σ₁ σ₂ (M · N)    = cong₂ _·_ (subst-assoc σ₁ σ₂ M) (subst-assoc σ₁ σ₂ N)
subst-assoc σ₁ σ₂ (ƛ M)      = cong  ƛ_ (begin
  M ⟪ exts σ₁ ⟫ ⟪ exts σ₂ ⟫ 
    ≡⟨ subst-assoc (exts σ₁) (exts σ₂) M ⟩
  M ⟪ _⟪ exts σ₂ ⟫ ∘ exts σ₁ ⟫
    ≡⟨ subst-cong (exts-subst σ₁ σ₂) M ⟩
  M ⟪ exts ( _⟪ σ₂ ⟫ ∘ σ₁) ⟫
    ∎)
  where
    open PropEq.≡-Reasoning
    exts-subst : (σ₁ : Subst Γ Δ) (σ₂ : Subst Δ Ξ)
      → (x : Γ , B ∋ A) 
      → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
    exts-subst σ₁ σ₂ Z     = refl
    exts-subst σ₁ σ₂ (S x) = begin
      (exts σ₁ ⨟ exts σ₂) (S x)
        ≡⟨⟩
      rename S_ (σ₁ x) ⟪ exts σ₂ ⟫ 
        ≡⟨ rename-exts σ₂ (σ₁ x)  ⟩
      rename S_ (σ₁ x ⟪ σ₂ ⟫)
        ≡⟨⟩
      exts (σ₁ ⨟ σ₂) (S x)
        ∎

----------------------------------------------------------------------
-- 

rename-subst : (ρ : Rename Γ Δ) (σ : Subst Δ Ξ)
  → (M : Γ ⊢ A)
  →  rename ρ M ⟪ σ ⟫ ≡ M ⟪ σ ∘ ρ ⟫
rename-subst ρ σ M = begin
  (rename ρ M) ⟪ σ ⟫ 
    ≡⟨ cong _⟪ σ ⟫ (rename=subst-ren M) ⟩
  (M ⟪ ren ρ ⟫) ⟪ σ ⟫ 
    ≡⟨ subst-assoc (ren ρ) σ M ⟩
  M ⟪ ren ρ ⨟ σ ⟫
    ≡⟨⟩
  M ⟪ σ ∘ ρ ⟫
    ∎
  where open PropEq.≡-Reasoning

subst-zero-comm : (σ : Subst Γ Δ)
  → (N : Γ ⊢ B) (x : Γ , B ∋ A)
  → (exts σ ⨟ subst-zero (N ⟪ σ ⟫)) x ≡ (subst-zero N ⨟ σ) x
subst-zero-comm         σ N Z     = refl
subst-zero-comm {Γ} {Δ} σ N (S x) = begin
  (rename S_ (σ x)) ⟪ subst-zero (N ⟪ σ ⟫) ⟫ 
    ≡⟨ cong (_⟪ subst-zero (N ⟪ σ ⟫) ⟫) (rename=subst-ren (σ x)) ⟩
  σ x ⟪ ren S_ ⟫ ⟪ subst-zero (N ⟪ σ ⟫) ⟫ 
    ≡⟨ subst-assoc (ren S_) (subst-zero (N ⟪ σ ⟫)) (σ x) ⟩
  σ x ⟪ subst-zero (N ⟪ σ ⟫) ∘ S_ ⟫ 
    ≡⟨ refl ⟩
  σ x ⟪ ids ⟫ 
    ≡⟨ subst-idL (σ x) ⟩
  σ x
    ∎
  where open PropEq.≡-Reasoning

------------------------------------------------------------------------------
-- Substitution Lemma

subst-ssubst : (σ : Subst Γ Δ)
  → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
  → M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ] ≡ M [ N ] ⟪ σ ⟫ 
subst-ssubst σ M N = begin
  M ⟪ exts σ ⟫ [ N ⟪ σ ⟫ ]
    ≡⟨ subst-assoc (exts σ) (subst-zero (N ⟪ σ ⟫)) M ⟩
  M ⟪ exts σ ⨟ subst-zero (N ⟪ σ ⟫) ⟫
    ≡⟨ subst-cong (subst-zero-comm σ N) M ⟩ 
  M ⟪ subst-zero N ⨟ σ ⟫
    ≡⟨ sym (subst-assoc (subst-zero N) σ M) ⟩
  (M ⟪ subst-zero N ⟫) ⟪ σ ⟫ 
    ∎
  where open PropEq.≡-Reasoning

rename-ssubst : (ρ : Rename Γ Δ)
  → (M : Γ , A ⊢ B) (N : Γ ⊢ A)
  → rename (ext ρ) M [ rename ρ N ] ≡ rename ρ (M [ N ])
rename-ssubst ρ M N = begin
  rename (ext ρ) M [ rename ρ N ]
    ≡⟨ cong (_⟪ subst-zero (rename ρ N) ⟫) (rename=subst-ren M) ⟩
  M ⟪ ren (ext ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ cong _⟪ subst-zero (rename ρ N) ⟫ (subst-cong (ren-ext-comm ρ) M) ⟩
  M ⟪ exts (ren ρ) ⟫ ⟪ subst-zero (rename ρ N) ⟫
    ≡⟨ subst-cong (λ { Z → rename=subst-ren N ; (S x) → refl}) (M ⟪ exts (ren ρ) ⟫) ⟩
  M ⟪ exts (ren ρ) ⟫ [ N ⟪ ren ρ ⟫ ]
    ≡⟨ subst-ssubst (ren ρ) M N ⟩
  M [ N ] ⟪ ren ρ ⟫
    ≡⟨ sym (rename=subst-ren _) ⟩
  rename ρ (M [ N ])
    ∎
  where
    open PropEq.≡-Reasoning

------------------------------------------------------------------------------
-- Substitution respects reduction

rename-reduce : {ρ : Rename Γ Δ}
  → M -→ N
  → rename ρ M -→ rename ρ N
rename-reduce {ρ = ρ} (β-ƛ· {M = M} {N})
  rewrite PropEq.sym (rename-ssubst ρ M N) = β-ƛ· 
--rename-reduce (ξ-absurd M-→N) = ξ-absurd (rename-reduce M-→N)
rename-reduce (ξ-ƛ M-→N)      = ξ-ƛ (rename-reduce  M-→N)
rename-reduce (ξ-·ₗ M-→N)     = ξ-·ₗ (rename-reduce M-→N)
rename-reduce (ξ-·ᵣ M-→N)     = ξ-·ᵣ (rename-reduce M-→N)

subst-reduce : {σ : Subst Γ Δ}
  → M -→ N
  → M ⟪ σ ⟫ -→ N ⟪ σ ⟫
subst-reduce {σ = σ} (β-ƛ· {M = M} {N})
  rewrite PropEq.sym (subst-ssubst σ M N) = β-ƛ·
--subst-reduce (ξ-absurd M-→N) = ξ-absurd (subst-reduce M-→N)
subst-reduce (ξ-ƛ M-→N)  = ξ-ƛ  (subst-reduce M-→N)
subst-reduce (ξ-·ₗ M-→N) = ξ-·ₗ (subst-reduce M-→N)
subst-reduce (ξ-·ᵣ M-→N) = ξ-·ᵣ (subst-reduce M-→N)
