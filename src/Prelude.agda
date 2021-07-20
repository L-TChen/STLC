module Prelude where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          ; Set to Type
          )
open import Function                   public
  using (_∘_)

open import Data.Unit                  public
  using (⊤)
open import Data.Empty                 public
  using (⊥; ⊥-elim)
open import Data.Nat                   public
  using (ℕ; suc; zero; _≤?_)

open import Relation.Nullary           public
  using (¬_)
open import Relation.Nullary.Decidable public

import Relation.Binary.PropositionalEquality
module Eq = Relation.Binary.PropositionalEquality
open Eq public
  using (_≡_; refl; sym; cong; cong₂; cong-app)


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
