open import Prelude 

module Language.STLC.ExplicitSub.Term where

open import Language.STLC.Context


infix 3 _⊢ᵗ_ _⊢ˢ_
infixr 5 ƛ_
infixl 6 _·_
infixr 8 ⟪_⟫_

data _⊢ˢ_ : (Γ Δ : Context) → 𝓤₀ ̇
data _⊢ᵗ_ : (Γ : Context) → (τ : Typ) → 𝓤₀ ̇

private
  variable
    Γ Δ Ξ Θ : Context
    τ σ     : Typ
    δ γ ξ   : Γ ⊢ˢ Δ
    t u s   : Γ ⊢ᵗ τ

private
  ⟪_⟫′ : (σ : Γ ⊢ˢ Δ) → (t : Δ ⊢ᵗ τ)
    → Γ ⊢ᵗ τ
  v′    : Γ , τ ⊢ᵗ τ

exts : Γ ⊢ˢ Δ
  → Γ , τ ⊢ˢ Δ , τ 

data _⊢ˢ_ where
  id : (Γ : Context)
    → Γ ⊢ˢ Γ

  p  : Γ , τ ⊢ˢ Γ

  _,_ : (δ : Γ ⊢ˢ Δ) → (t : Γ ⊢ᵗ τ)
    → Γ ⊢ˢ Δ , τ

  _⨟_ : (δ : Γ ⊢ˢ Δ) → (ξ : Δ ⊢ˢ Ξ)
    → Γ ⊢ˢ Ξ

  ⨟-idᵣ : (δ : Γ ⊢ˢ Δ)
    → δ ⨟ id Δ ≡ δ

  ⨟-idₗ : (δ : Γ ⊢ˢ Δ)
    → id Γ ⨟ δ ≡ δ

  ⨟-assoc : δ ⨟ (γ ⨟ ξ) ≡ (δ ⨟ γ) ⨟ ξ

  ⨟-proj : (δ , t) ⨟ p ≡ δ
  
  ⨟-ext : ξ ⨟ (δ , t) ≡ ((ξ ⨟ δ) , ⟪ ξ ⟫′ t) -- ?

data _⊢ᵗ_ where
  v    : Γ , τ ⊢ᵗ τ

  ⟪_⟫_ : (σ : Γ ⊢ˢ Δ) → (t : Δ ⊢ᵗ τ)
    → Γ ⊢ᵗ τ
    
  v-id  : ⟪ id (Γ , τ) ⟫ v ≡ v

  v-ext : ⟪ δ , t ⟫ v ≡ t 

  ƛ_   : (t : Γ , σ ⊢ᵗ τ)
    → Γ ⊢ᵗ σ →̇ τ

  abs-subst :
    ⟪ δ ⟫ (ƛ t) ≡ ƛ ⟪ exts δ ⟫ t -- inductive-recursive type? 

  _·_  : (s : Γ ⊢ᵗ σ →̇ τ) → (t : Γ ⊢ᵗ σ)
    → Γ ⊢ᵗ τ

  app-subst :
    ⟪ δ ⟫ (t · s) ≡ ⟪ δ ⟫ t · ⟪ δ ⟫ s


⟪_⟫′   = ⟪_⟫_
v′     = v
exts δ = p ⨟ δ , v
