This file is written in Markdown Literate Agda.

```
module Context where

open import Data.Empty
open import Data.Nat

```

Fixity declariton
-----------------

`infixl` stands for a left associative operator with precendence 6
therefore, `A , B , C` stands for `(A , B) , C`

```
infixl 7 _⧺_
infixl 6 _,_
infix  4 _∋_
```


Context
-------

A context is just a snoc list.  Instead of x ∷ xs, the tail is on the
left hand side.

```
data Context (Ty : Set) : Set where
  ∅   :                   Context Ty
  _,_ : Context Ty → Ty → Context Ty

private
  variable
    Ty  : Set
    A B : Ty
    Γ Δ : Context Ty
```

Membership
----------

`Γ ∋ A` means that A is a member of Γ.

There are two ways of estabilishing the judgement Γ ∋ A.

  1. `Γ , A ∋ A` for any `Γ` and `A`, as we know that `A` is in the
  0-th position.

  2. If `x : Γ ∋ A` is a proof that `A` is in `Γ`, then `Γ , B ∋ A`
     holds.

How should we name these inference rules? Note that if we interpret
the proof of `Γ ∋ A` as the position of `A` in `Γ`, then 1. should be
Z (for zero) and 2. should be S (for successor).

```
data _∋_ {Ty : Set} : Context Ty → Ty → Set where


  Z : {Γ : Context Ty} {A : Ty}
      -------------------------
    → Γ , A ∋ A


  S_ : {A B : Ty}
     → Γ     ∋ A
       ---------
     → Γ , B ∋ A
```

For example, `S Z : ∅ , A , B ∋ A` means `A` is in the first position. That is, 

```
_ : ∅ , A , B ∋ A
_ = S Z 
```

Lookup is just _‼_ in Haskell. It is partial.

```
lookup : Context Ty → ℕ → Ty
lookup (Γ , A) zero     =  A
lookup (Γ , B) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```

If `lookup Γ n` finds the element in the n-th position, then the
memberhsip proof can be produced algorithmatically. Hence we can
transform a natural number to a membership proof.

```
count : (n : ℕ) → Γ ∋ lookup Γ n
count {Γ = Γ , _} zero     =  Z
count {Γ = Γ , _} (suc n)  =  S (count n)
count {Γ = ∅    }  _        =  ⊥-elim impossible
  where postulate impossible : ⊥
```

```
_ :  ∅ , A , B ∋ A
_ = count 1

_ : ∅ , B , A ∋ A
_ = count 0
```

Shifting
--------
 
     (Aₙ , ... , A₁, A₀) 
       |    |     |   |
       ↓    ↓     ↓   ↓  
   ↦ (Aₙ , ... , A₁, A₀, B)
  
      n+1         2   1  0

```
ext : {Ty : Set} {Γ Δ : Context Ty}
  → (∀ {A : Ty} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B : Ty} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)
```

Concatenation
-------------

```
_⧺_ : Context Ty → Context Ty → Context Ty
Γ ⧺ ∅       = Γ
Γ ⧺ (Δ , x) = Γ ⧺ Δ , x
```
