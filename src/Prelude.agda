module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )
open import Cubical.Foundations.Function     public
  using (_∘_)

import Cubical.Foundations.Prelude as CubicalPrelude 
open CubicalPrelude                          public
  using (_≡_; _[_≡_]; refl; sym; cong; cong₂; subst; funExt; ~_; PathP)
  renaming (funExt⁻ to cong-app; subst2 to subst₂)

open import Cubical.Data.Unit                public
  renaming (Unit to ⊤)
open import Cubical.Data.Empty               public
  using (⊥)
  renaming (elim to ⊥-elim)
open import Cubical.Data.Nat                 public
  using (ℕ; suc; zero)
open import Cubical.Data.Nat.Order.Recursive public
  using (_≤?_)
open import Cubical.Data.Sigma               public
  using (Σ; Σ-syntax; ∃-syntax; _×_; _,_)
  renaming (fst to proj₁; snd to proj₂)

open import Cubical.Relation.Nullary         public
  using (¬_; Dec)

variable
  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣' : Universe
  
infix  1 _̇

_̇ : (𝓤 : Universe) → _
𝓤 ̇ = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} → (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

module Eq where
  module ≡-Reasoning where
    open CubicalPrelude public
      using (_≡⟨_⟩_; _∎) 

    infix 1 begin_
    begin_ : {A : 𝓤 ̇} {x y : A}
      → x ≡ y → x ≡ y
    begin_ r = r

PathP-syntax = PathP

infix 4 PathP-syntax
syntax PathP-syntax (λ i → A) x y = x ≡ y ⦂ [ i ↦ A ]
