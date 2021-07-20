{- Coquand, T., & Dybjer, P. (1997). Intuitionistic model constructions and normalization proofs. Mathematical Structures in Computer Science, 7(1). https://doi.org/10.1017/S0960129596002150 -}

module Language.T.CL.Term where

open import Prelude

open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Language.T.CL.Type

infix 3 _-→_ _-↛_
infixl 7 _·_ _·ₘ_

------------------------------------------------------------------------------
-- Terms

data Term : Ty → 𝓤₀ ̇ where
  K    : Term (A `→ B `→ A)
  S    : Term ((A `→ B `→ C) `→ (A `→ B) `→ A `→ C)
  _·_  : (c : Term (A `→ B)) → (a : Term A) → Term B
  `0   : Term `ℕ
  `S   : Term `ℕ → Term `ℕ
  `rec : Term C → Term (`ℕ `→ C `→ C) → Term (`ℕ `→ C)

private
  variable
    a b c d a′ b′ c′ d′ : Term A
    f g  : Term (A `→ B)
    e e′ : Term (`ℕ `→ C `→ C)

------------------------------------------------------------------------------
-- Reduction rules

data _-→_ : (M N : Term A) → 𝓤₀ ̇ where
  β-K    : K · a · b      -→ a

  β-S    : S · g · f · a  -→ (g · a) · (f · a)

  β-rec0 : `rec d e · `0   -→ d

  β-recS : `rec d e · `S a -→ e · a · (`rec d e · a)

  ξ-·ₗ   : a     -→ a′
         → a · b -→ a′ · b

  ξ-·ᵣ   : b     -→ b′
         → a · b -→ a · b′

  ξ-`S    : a    -→ a′
         → `S a -→ `S a′

  ξ-rec₁ : d -→ d′
         → `rec d e -→ `rec d′ e

  ξ-rec₂ : e -→ e′
         → `rec d e -→ `rec d e′

_-↛_ : (a b : Term A) → 𝓤₀ ̇
a -↛ b = ¬ (a -→ b)

------------------------------------------------------------------------------
-- Multi-step reduction

module -↠-Reasoning where
  infix  1 begin_
  infix  2 _-↠_ 
  infixr 2 _-→⟨_⟩_ _-↠⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  data _-↠_ {A} : (a b : Term A) → 𝓤₀ ̇ where
    _∎ : (a : Term A)
      → a -↠ a

    _-→⟨_⟩_
      : ∀ a   
      → a -→ b
      → b -↠ c
        -------
      → a -↠ c

  begin_ : a -↠ b
    → a -↠ b
  begin r = r

  _-↠⟨_⟩_ : ∀ a
    → a -↠ b
    → b -↠ c
    ---------
    → a -↠ c
  a -↠⟨ .a ∎               ⟩ b-↠c = b-↠c
  a -↠⟨ .a -→⟨ a→b ⟩ b-↠b′ ⟩ b-↠c = a -→⟨ a→b   ⟩ _ -↠⟨ b-↠b′ ⟩ b-↠c

  _≡⟨_⟩_ : ∀ a
    → a ≡ b
    → b -↠ c
    --------
    → a -↠ c
  a ≡⟨ refl ⟩ b-↠c = b-↠c

  _≡⟨⟩_ : ∀ a
    → a -↠ c
    --------
    → a -↠ c
  a ≡⟨⟩ b-↠c = b-↠c

  -↠-refl : a -↠ a
  -↠-refl {a = a} = a ∎

  -↠-·ₗ : a -↠ a′
    → a · b -↠ a′ · b
  -↠-·ₗ (a ∎)                  = a · _ ∎
  -↠-·ₗ (a -→⟨ a→a′ ⟩ a′-↠a′′) = a · _ -→⟨ ξ-·ₗ a→a′ ⟩ -↠-·ₗ a′-↠a′′

  -↠-·ᵣ : b -↠ b′
    → a · b -↠ a · b′
  -↠-·ᵣ (b ∎)                  = _ · b ∎
  -↠-·ᵣ (b -→⟨ b→b′ ⟩ b′-↠b′′) = _ · b -→⟨ ξ-·ᵣ b→b′ ⟩ -↠-·ᵣ b′-↠b′′

  -↠-`S : a -↠ a′
    → `S a -↠ `S a′
  -↠-`S (_ ∎)                  = _ ∎
  -↠-`S (a -→⟨ a→a′ ⟩ a′-↠a′′) = `S a -→⟨ ξ-`S a→a′ ⟩ -↠-`S a′-↠a′′

  -↠-rec₁ : d -↠ d′
    → `rec d e -↠ `rec d′ e
  -↠-rec₁ (_ ∎)                  = _ ∎
  -↠-rec₁ (d -→⟨ d→d′ ⟩ d′-↠d′′) = `rec d _ -→⟨ ξ-rec₁ d→d′ ⟩ -↠-rec₁ d′-↠d′′

  -↠-rec₂ : e -↠ e′
    → `rec d e -↠ `rec d e′
  -↠-rec₂ (_ ∎)                  = _ ∎
  -↠-rec₂ (e -→⟨ e→e′ ⟩ e′-↠e′′) = `rec _ e -→⟨ ξ-rec₂ e→e′ ⟩ -↠-rec₂ e′-↠e′′
open -↠-Reasoning using (_-↠_)

------------------------------------------------------------------------------
-- Irreducible terms

Nf : Term A → 𝓤₀ ̇
Nf a = ∀ {b} → a -↛ b

NF : Ty → 𝓤₀ ̇
NF A = Σ[ a ∈ Term A ] Nf a

`0ᴺ : NF `ℕ
`0ᴺ = `0 , λ ()

`Sᴺ : NF `ℕ → NF `ℕ
`Sᴺ (`n , `n↓) = `S `n , λ { (ξ-`S r) → `n↓ r}

Kᴺ : NF (A `→ B `→ A)
Kᴺ = K , λ ()

K·ᴺ : NF A → NF (B `→ A)
K·ᴺ (a , a↓) = K · a , λ { (ξ-·ᵣ r) → a↓ r}

Sᴺ : NF ((A `→ B `→ C) `→  (A `→ B) `→ A `→ C)
Sᴺ = S , λ ()

S·ᴺ : NF (A `→ B `→ C) → NF ((A `→ B) `→ A `→ C)
S·ᴺ (a , a↓) = S · a , λ { (ξ-·ᵣ r) → a↓ r}

S··ᴺ : NF (A `→ B `→ C) → NF (A `→ B) → NF (A `→ C)
S··ᴺ (a , a↓) (b , b↓) = S · a · b ,
  λ { (ξ-·ₗ (ξ-·ᵣ r)) → a↓ r ; (ξ-·ᵣ r) → b↓ r}

recᴺ : NF C → NF (`ℕ `→ C `→ C) → NF (`ℕ `→ C)
recᴺ (d , d↓) (e , e↓) =
  (`rec d e) , λ { (ξ-rec₁ r) → d↓ r ; (ξ-rec₂ r) → e↓ r}
------------------------------------------------------------------------------
-- Denotational semantics

⟦_⟧Ty : Ty → 𝓤₀ ̇
⟦ `⊥     ⟧Ty = ⊥
⟦ `ℕ     ⟧Ty = ℕ
⟦ A `→ B ⟧Ty = NF (A `→ B) × (⟦ A ⟧Ty → ⟦ B ⟧Ty)

tmOf : ⟦ A `→ B ⟧Ty → Term (A `→ B)
tmOf ((c , _) , _) = c

reifyℕ : ⟦ `ℕ ⟧Ty → NF `ℕ
reifyℕ zero    = `0ᴺ
reifyℕ (suc a) = `Sᴺ (reifyℕ a)

reify : ⟦ A ⟧Ty → NF A
reify {`ℕ}     a       = reifyℕ a
reify {A `→ B} (c , f) = c

_·ₘ_ : ⟦ A `→ B ⟧Ty → ⟦ A ⟧Ty → ⟦ B ⟧Ty
(c , f) ·ₘ q = f q

rec : {X : 𝓤₀ ̇}
  → X → (ℕ → X → X) → ℕ → X
rec d e zero    = d
rec d e (suc n) = e n (rec d e n)

⟦_⟧ : Term A → ⟦ A ⟧Ty
⟦ K        ⟧ = Kᴺ , λ p → K·ᴺ (reify p) , λ q → p 
⟦ S        ⟧ = Sᴺ , λ p → let a = reify p in
  S·ᴺ a    , λ q → let b = reify q in
  S··ᴺ a b , λ r → (p ·ₘ r) ·ₘ (q ·ₘ r)
⟦ a · b    ⟧ = ⟦ a ⟧ ·ₘ ⟦ b ⟧
⟦ `0       ⟧ = zero
⟦ `S a     ⟧ = suc ⟦ a ⟧
⟦ `rec d e ⟧ = let 𝑑 = ⟦ d ⟧; 𝑒 = ⟦ e ⟧ in
  recᴺ (reify 𝑑) (reify 𝑒) , rec 𝑑 λ x y → 𝑒 ·ₘ x ·ₘ y

------------------------------------------------------------------------------
-- Logical consistency by evaluation

consistency : ¬ Term `⊥ 
consistency = ⟦_⟧

------------------------------------------------------------------------------
-- Normalisation by evaluation

nf : (a : Term A) → NF A
nf a = reify ⟦ a ⟧

reify′ : ⟦ A ⟧Ty → Term A
reify′ = λ a → reify a .proj₁

nf′ : Term A → Term A
nf′ a = reify′ ⟦ a ⟧

------------------------------------------------------------------------------
-- Soudness of normalisation 

⟦⟧-respects-→ : a -→ a′ → ⟦ a ⟧ ≡ ⟦ a′ ⟧
⟦⟧-respects-→ β-K        = refl
⟦⟧-respects-→ β-S        = refl
⟦⟧-respects-→ β-rec0     = refl
⟦⟧-respects-→ β-recS     = refl
⟦⟧-respects-→ (ξ-·ₗ r)   rewrite ⟦⟧-respects-→ r = refl
⟦⟧-respects-→ (ξ-·ᵣ r)   rewrite ⟦⟧-respects-→ r = refl
⟦⟧-respects-→ (ξ-`S r)   rewrite ⟦⟧-respects-→ r = refl
⟦⟧-respects-→ (ξ-rec₁ r) rewrite ⟦⟧-respects-→ r = refl
⟦⟧-respects-→ (ξ-rec₂ r) rewrite ⟦⟧-respects-→ r = refl

nf-respects-→ : a -→ a′ → nf a ≡ nf a′
nf-respects-→ r rewrite ⟦⟧-respects-→ r = refl

module _ where
  open -↠-Reasoning
  nf-respects-↠ : a -↠ a′ → nf a ≡ nf a′
  nf-respects-↠ (_ ∎)          = refl
  nf-respects-↠ (_ -→⟨ r ⟩ rs) = trans (nf-respects-→ r) (nf-respects-↠ rs)

------------------------------------------------------------------------------
-- Glued values

  Gl : (A : Ty) → ⟦ A ⟧Ty → 𝓤₀ ̇
  Gl `ℕ       n = ⊤
  Gl (A `→ B) q = {p : ⟦ A ⟧Ty} → Gl A p →
    (reify′ q · reify′ p -↠ reify′ (q ·ₘ p)) × Gl B (q ·ₘ p)
  
  glued    : (a : Term A) → Gl A ⟦ a ⟧
  gluedRec : Gl (`ℕ `→ C) ⟦ `rec d e ⟧

  gluedRec {_} {d} {e} {zero}  tt = (begin
    `rec (nf′ d) (nf′ e) · `0
      -→⟨ β-rec0 ⟩
    nf′ d ∎)
    , glued d
  gluedRec {C} {d} {e} {suc n} tt = (begin
    nf′ (`rec d e) · reify′ (suc n)
      ≡⟨⟩
    `rec (nf′ d) (nf′ e) · `S (reify′ n)
      -→⟨ β-recS  ⟩
    (nf′ e) · (reify′ n) · (`rec (nf′ d) (nf′ e) · reify′ n)
      -↠⟨ -↠-·ₗ (glued e _ .proj₁) ⟩
    reify′ (⟦ e ⟧ ·ₘ n) · (`rec (nf′ d) (nf′ e) · reify′ n)
      -↠⟨ -↠-·ᵣ (gluedRec {C} {d} {e} {n} tt .proj₁) ⟩
    reify′ (⟦ e ⟧ ·ₘ n) · reify′ (⟦ `rec d e ⟧ ·ₘ n)
      -↠⟨ glued e _ .proj₂ (gluedRec {C} {d} {e} {n} tt .proj₂) .proj₁ ⟩
    reify′ (⟦ `rec d e ⟧ ·ₘ suc n) ∎)
    , glued e _ .proj₂ (gluedRec {C} {d} {e} {n} tt .proj₂) .proj₂

  glued K       x     =
    (_ ∎) , λ y → (_ -→⟨ β-K ⟩ _ ∎) , x
  glued S       {p} x =
    (_ ∎) , λ {q} y → -↠-refl , λ {r} z → (begin
      reify′ (⟦ S ⟧ ·ₘ p ·ₘ q) · reify′ r
        -→⟨ β-S ⟩
      (tmOf p · reify′ r) · (tmOf q · reify′ r)
        -↠⟨ -↠-·ₗ (x z .proj₁)  ⟩
      reify′ (p ·ₘ r) · (tmOf q · reify′ r)
        -↠⟨ -↠-·ᵣ (y z .proj₁) ⟩
      reify′ (p ·ₘ r) · reify′ (q ·ₘ r)
        -↠⟨ x z .proj₂ (y z .proj₂) .proj₁ ⟩
      reify′ (⟦ S ⟧ ·ₘ p ·ₘ q ·ₘ r) ∎ )
      , x z .proj₂ (y z .proj₂) .proj₂
  glued (c · a)    = glued c (glued a) .proj₂
  glued `0         = tt
  glued (`S a)     = tt
  glued (`rec d e) {n} = gluedRec {d = d} {e} {n}

------------------------------------------------------------------------------
-- 
  -↠-complete : (a : Term A)
    → a -↠ nf′ a
  -↠-complete K          = K ∎
  -↠-complete S          = S ∎
  -↠-complete (a · b)    = begin
    a · b
      -↠⟨ -↠-·ₗ (-↠-complete a) ⟩
    nf′ a · b
      -↠⟨ -↠-·ᵣ (-↠-complete b) ⟩
    nf′ a · nf′ b
      -↠⟨ glued a (glued b) .proj₁  ⟩
    nf′ (a · b) ∎
  -↠-complete `0         = `0 ∎
  -↠-complete (`S a)     = -↠-`S (-↠-complete a)
  -↠-complete (`rec d e) = begin
    `rec d e
      -↠⟨ -↠-rec₁ (-↠-complete d) ⟩
    `rec (nf′ d) e
      -↠⟨ -↠-rec₂ (-↠-complete e) ⟩
    `rec (nf′ d) (nf′ e) ∎

------------------------------------------------------------------------------
-- Confluency by normalisation

  triangle : a -↠ b
    → b -↠ nf′ a
  triangle {a = a} {b} r = begin
    b
      -↠⟨ -↠-complete b ⟩
    nf′ b
      ≡⟨ sym (cong proj₁ (nf-respects-↠ r)) ⟩
    nf′ a ∎

  confluence
    : a -↠ b → a -↠ b′
    → ∃[ c ] (b -↠ c) × (b′ -↠ c)
  confluence {a = a} r s = nf′ a , triangle r , triangle s
