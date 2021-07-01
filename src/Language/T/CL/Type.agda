module Language.T.CL.Type where

open import Prelude

infixr 5 _`→_

data Ty : 𝓤₀ ̇ where
  `⊥    : Ty 
  `ℕ   : Ty
  _`→_ : (A B : Ty) → Ty

variable
  A B C : Ty
