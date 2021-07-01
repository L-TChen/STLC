module Language.STLC.Confluence where

open import Data.Product as Prod
  renaming (_,_ to ⟨_,_⟩)

open import Language.STLC.Term
open import Language.STLC.Substitution

private
  variable
    Γ Δ            : Context
    A B C          : Type
    M N L M′ N′ L′ : Γ ⊢ A
    
------------------------------------------------------------------------------
-- Parallel reduction, see
-- M. Takahashi, “Parallel Reductions in λ-Calculus,” Inf. Comput., vol. 118, no. 1, pp. 120–127, 1995.

infix 3 _⇛_
data _⇛_  {Γ} : (M N : Γ ⊢ A) → Set where
  pvar : {x : Γ ∋ A}
       → `  x ⇛ ` x
       
  pabs
    : M ⇛ M′
      -----------
    → ƛ M ⇛ ƛ M′

  papp
    : M ⇛ M′
    → N ⇛ N′
      ----------------
    → M · N ⇛ M′ · N′
  pabort
    : M ⇛ M′
    → abort A M ⇛ abort A M′

  pbeta
    : M ⇛ M′
    → N ⇛ N′
      ----------------------
    → (ƛ M) · N ⇛ M′ [ N′ ]

------------------------------------------------------------------------------
-- Transitive and Reflexive Closure of Parallel Reduction 

infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
       --------
     → M ⇛* M
  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N
------------------------------------------------------------------------------
-- ⇛ is reflexive
par-refl : M ⇛ M
par-refl {M = ` _}     = pvar
par-refl {M = abort _ M} = pabort par-refl 
par-refl {M = ƛ _}     = pabs par-refl
par-refl {M = _ · _}   = papp par-refl par-refl

------------------------------------------------------------------------------
-- Sandwitch parallel reduction between single-step reduction and multi-step reduction
-- -→ ⊆ ⇛ ⊆ -↠

-→⊆⇛ : M -→ N → M ⇛ N
-→⊆⇛ β-ƛ·           = pbeta par-refl par-refl  
-→⊆⇛ (ξ-abort M→M′) = pabort (-→⊆⇛ M→M′)   
-→⊆⇛ (ξ-ƛ M→M′)     = pabs (-→⊆⇛ M→M′)
-→⊆⇛ (ξ-·ₗ L→L′)    = papp (-→⊆⇛ L→L′) par-refl
-→⊆⇛ (ξ-·ᵣ M→M′)    = papp par-refl    (-→⊆⇛ M→M′)

-↠⊆⇛* 
  : M -↠ N
    ------
  → M ⇛* N
-↠⊆⇛* (M ∎)          = M ∎
-↠⊆⇛* (L -→⟨ b ⟩ bs) = L ⇛⟨ -→⊆⇛ b ⟩ -↠⊆⇛* bs

⇛⊆-↠ : M ⇛ N → M -↠ N
⇛⊆-↠ pvar  = _ ∎ 
⇛⊆-↠ (pabort M⇛M′) = abort-↠ (⇛⊆-↠ M⇛M′)
⇛⊆-↠ (pbeta {M = M} {M′} {N} {N′} M⇛M′ N⇛N′) =
  (ƛ M) · N
    -↠⟨ ·-↠ (ƛ-↠ (⇛⊆-↠ M⇛M′)) (⇛⊆-↠ N⇛N′) ⟩
  (ƛ M′) · N′
    -→⟨ β-ƛ· ⟩
  M′ [ N′ ] ∎
⇛⊆-↠ (pabs M⇛N) = ƛ-↠ (⇛⊆-↠ M⇛N)
⇛⊆-↠ (papp L⇛M M⇛N) =
  _ · _
    -↠⟨ ·-↠ (⇛⊆-↠ L⇛M) (⇛⊆-↠ M⇛N) ⟩
  _ · _
    ∎

⇛*⊆-↠ : ∀{Γ A} {M N : Γ ⊢ A}
  → M ⇛* N
    ------
  → M -↠ N
⇛*⊆-↠ (M ∎)         = M ∎
⇛*⊆-↠ (L ⇛⟨ p ⟩ ps) = L -↠⟨ ⇛⊆-↠ p ⟩ ⇛*⊆-↠ ps

par-rename
  : {ρ : Rename Γ Δ}
  → M ⇛ M′
  → rename ρ M ⇛ rename ρ M′
par-rename pvar              = pvar
par-rename (pabort M⇛M′)     = pabort (par-rename M⇛M′)
par-rename (pabs M⇛M′)       = pabs (par-rename M⇛M′)
par-rename (papp M⇛M′ N⇛N′)  = papp (par-rename M⇛M′) (par-rename N⇛N′)
par-rename {Γ} {Δ} {ρ = ρ} (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
  with pbeta (par-rename {ρ = ext ρ} M⇛M′) (par-rename {ρ = ρ} N⇛N′) 
... | G rewrite rename-ssubst {Γ} {Δ} ρ M′ N′ = G

Par-Subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
Par-Subst {Γ} {Δ} σ σ′ = ∀{A} {x : Γ ∋ A} → σ x ⇛ σ′ x

par-subst-exts
  : {σ σ′ : Subst Γ Δ}
  → (Par-Subst σ σ′)
  → ∀ {A} → Par-Subst (exts {Γ} {Δ} {A} σ) (exts σ′)
par-subst-exts s {x = Z}   = pvar
par-subst-exts s {x = S x} = par-rename s

par-subst
  : {σ τ : Subst Γ Δ}
  → Par-Subst σ τ
  → M ⇛ M′
  → M ⟪ σ ⟫ ⇛ M′ ⟪ τ ⟫
par-subst σ⇛τ pvar   = σ⇛τ
par-subst σ⇛τ (pabort  M⇛M′)  = pabort (par-subst σ⇛τ M⇛M′)
par-subst σ⇛τ (papp M⇛M′ N⇛N′) =
  papp (par-subst σ⇛τ M⇛M′) (par-subst σ⇛τ N⇛N′)
par-subst σ⇛τ (pabs M⇛M′) =
  pabs (par-subst (λ {A} {x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
par-subst {σ = σ} {τ} σ⇛τ (pbeta {M′ = M′} {N′ = N′} M⇛M′ N⇛N′)
    with pbeta (par-subst {M = _} {σ = exts σ} {τ = exts τ}
                        (λ{A}{x} → par-subst-exts σ⇛τ {x = x}) M⇛M′)
               (par-subst {σ = σ} σ⇛τ N⇛N′)
... | G rewrite subst-ssubst τ M′ N′ = G

sub-par
  : M ⇛ M′
  → N ⇛ N′
  → M [ N ] ⇛ M′ [ N′ ]
sub-par {A} {Γ} {B} {M} {M′} {N} {N′} M⇛M′ N⇛N′ =
  par-subst {σ = subst-zero N} {τ = subst-zero N′} σ⇛σ′ M⇛M′
  where
    σ⇛σ′ : ∀ {A} {x : Γ , B ∋ A} → subst-zero N x ⇛ subst-zero N′ x
    σ⇛σ′ {x = Z}   = N⇛N′
    σ⇛σ′ {x = S x} = pvar
------------------------------------------------------------------------------
-- Confluence

_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(abort A M) ⁺  = abort A (M ⁺)
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ M) · N) ⁺ = M ⁺ [ N ⁺ ]
(M · N) ⁺     = M ⁺ · (N ⁺)

par-triangle : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-triangle pvar = pvar
par-triangle (pabort M⇛M′)     = pabort (par-triangle M⇛M′)
par-triangle (pbeta M⇛M′ N⇛N′) = sub-par (par-triangle M⇛M′) (par-triangle N⇛N′) 
par-triangle (pabs M⇛M′)       = pabs (par-triangle M⇛M′)
par-triangle (papp {M = ƛ _} (pabs M⇛M′) N⇛N′) =
  pbeta (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (papp {M = ` x} pvar N)        = papp (par-triangle pvar)  (par-triangle N)
par-triangle (papp {M = abort _ _} M⇛M′ N⇛N′) = papp (par-triangle M⇛M′) (par-triangle N⇛N′)
par-triangle (papp {M = L · M} LM⇛M′ N)     = papp (par-triangle LM⇛M′) (par-triangle N)
  
strip
  : M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip mn (M ∎) = ⟨ _ , ⟨ _ ∎ , mn ⟩ ⟩
strip mn (M ⇛⟨ mm' ⟩ m'n')
  with strip (par-triangle mm') m'n'
... | ⟨ L , ⟨ ll' , n'l' ⟩ ⟩ =
      ⟨ L , ⟨ (_ ⇛⟨ par-triangle mn ⟩ ll') , n'l' ⟩ ⟩

par-confluence 
  : L ⇛* M
  → L ⇛* M′
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M ⇛* N) × (M′ ⇛* N)
par-confluence {Γ}{A}{L}{.L}{N} (L ∎) L⇛*N = ⟨ N , ⟨ L⇛*N , N ∎ ⟩ ⟩
par-confluence {Γ}{A}{L}{M₁′}{M₂} (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂
    with strip L⇛M₁ L⇛*M₂
... | ⟨ N , ⟨ M₁⇛*N , M₂⇛N ⟩ ⟩
      with par-confluence M₁⇛*M₁′ M₁⇛*N
...   | ⟨ N′ , ⟨ M₁′⇛*N′ , N⇛*N′ ⟩ ⟩ =
        ⟨ N′ , ⟨ M₁′⇛*N′ , (M₂ ⇛⟨ M₂⇛N ⟩ N⇛*N′) ⟩ ⟩

confluence 
  : L -↠ M
  → L -↠ M′
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M -↠ N) × (M′ -↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (-↠⊆⇛* L↠M₁) (-↠⊆⇛* L↠M₂)
... | ⟨ N , ⟨ M₁⇛N , M₂⇛N ⟩ ⟩ = ⟨ N , ⟨ ⇛*⊆-↠ M₁⇛N , ⇛*⊆-↠ M₂⇛N ⟩ ⟩
