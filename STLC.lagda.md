
Intrinsically-typed de Bruijn representation of simply typed lambda calculus
============================================================================

```agda
{-# OPTIONS --allow-unsolved-metas #-} 
module STLC where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Context public
```

Fixity declartion
-----------------
```agda
infix  3 _⊢_

infixr 7 _→̇_

infixr 5 ƛ_
infixl 7 _·_
infixl 8 _[_] _⟪_⟫
infixr 9 ᵒ_ `_ #_
```

Types
-----

```agda
data Type : Set where
  ⊤   : Type
  _→̇_ : Type → Type → Type

Cxt  = Context Type
```

For convenience, we use symbols

  * `A`, `B`, `C` for types
  * `Γ`, `Δ`, and `Ξ` for contexts
  * x for any proof of Γ ∋ A

In Agda, this convention can be achieved by the keyword `variable` as follows.

```agda
variable
  A B C : Type
  Γ Δ Ξ : Context Type
  x     : Γ ∋ A
```

Terms = typing rules
--------------------

First off, since the typing rules for simply typed lambda calculus are
syntax-directed, we combine the term formation rules with the typing
rules.

Therefore, the typing judgement consists of only a context `Γ` and a
`Type` with inference rules as term constructs. The collection of
terms in simply typed lambda calculus is defined as an inducitve family 
indexed by a (given) context and a type. 

```agda
data _⊢_ (Γ : Cxt) : Type → Set where
```

In our formal development we will use the position of λ to which the
bound variable refer for the name of a variable.  For example,

    λ x. λ y. y

will be represented by

    λ λ 0

This representation is called de Bruijn representation and the nubmer
is a de Bruijn index. It also makes α-equivalence an equality on
λ-terms.

Note that we have

    Γ ∋ (x : A) 
    -----------
    Γ ⊢ x : A

in our informal development where `x` is now merely a number pointing
to the position of `A` in `Γ`. We introduce a term `x` for a free
variable in `Γ` just by giving its position in the context.
Given `Γ ⊢ M : A`, the context Γ is the set of possibly free variables in `M`.

```agda
  `_ : Γ ∋ A
       -----
     → Γ ⊢ A
```
     
The definition of application is straightforward.

```agda
  _·_ : Γ ⊢ A →̇ B
      → Γ ⊢ A
        -----
      → Γ ⊢ B
```

In the informal development it takes a variable x and a term M to
form λ x. M.  Since the name of a variable does not matter at all in
our formal development λ now takes a term M only. 

Moreover, the position of a variable in the context `Γ , A` now refers
to the innermost λ. Hence our definition

```agda
  ƛ_
    : Γ , A ⊢ B
      ---------
    → Γ ⊢ A →̇ B
```

For example, ` Z : (∅ , A) ⊢ A is a variable of type A under the
context (∅ , A).  After abstraction, ƛ ` Z : ∅ ⊢ A →̇ A is an
abstraction under the empty context whose body is only a variable
refering to the variable bound by λ.

As you may have observed, this inductive family Γ ⊢ A is just
a variant of the natural deduction for propositional logic where
inference rules are viewed as term constructs.

For convenience, the following symbols denote a term.

```agda
variable
  M N L M′ N′ L′ : Γ ⊢ A
```
  
Also for convenience, we compute the proof of `Γ ∋ A` by giving its
position n (as a natural). In short, define # n as ` (count n)

```agda
#_ : (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
```

### Examples

```agda
nat : Type → Type
nat A = (A →̇ A) →̇ A →̇ A
```

Recall that the Church numberal c₀ for 0 is

    λ f x. x

In the de Bruijn representation, λ f x. x becomes

    λ λ 0

```agda
c₀ : ∀ {A} → ∅ ⊢ nat A
c₀ = ƛ ƛ # 0
```

Similarly, c₁ ≡ λ f x. f x becomes

    λ λ 1 0 

```agda
c₁ : ∀ {A} → ∅ ⊢ nat A
c₁ = ƛ ƛ # 1 · # 0
```

The addition of two Church numerals defined as

    λ n. λ m. λ f. λ x. n f (m f x)

becomes

    λ λ λ λ 3 1 (2 1 0)

```agda
add : ∀ {A} → ∅ ⊢ nat A →̇ nat A →̇ nat A
add = ƛ ƛ ƛ ƛ # 3 · # 1 · (# 2 · # 1 · # 0)
```

### Exercise

Translate the following terms in the informal development to de
Bruijn representation.

    1. (id)   λ x. x
    2. (fst)  λ x y. x
    3. (if)   λ b x y. b x y
    4. (succ) λ n. λ f x. f (n f x)

```agda
id : ∅ ⊢ A →̇ A
id = {!!}

fst : ∅ ⊢ A →̇ B →̇ A
fst = {!!}

bool : Type → Type
bool A = {!!}

if : ∅ ⊢ bool A →̇ A →̇ A →̇ A
if = {!!} 

succ : ∅ ⊢ nat A →̇ nat A
succ = {!!} 
```

Parallel Substitution
---------------------

To define substitution, it is actually easier to define substitution
for all free variable at once instead of one.

```agda
Rename : Cxt → Cxt → Set
Rename Γ Δ = ∀ {A} → Γ ∋ A → Δ ∋ A

Subst : Context Type → Context Type → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A
```

As the de Bruijn index points to the position of a λ abstraction
starting from the innermost λ, we need to increment/decrement the
number when visiting/leaving λ.

For example, substituting M for x in the following term

    x : A → A ⊢ x (λ y. y) 

becomes

    0 (λ 0) [ M / 0 ] ≡ M (λ [ M ↑ / 1 ])

where M ↑ indicates that the de Bruijn index of a free variable which
is incremented. 

Therefore, a renaming function ρ : ∀ {A} → Γ ∋ A → Δ ∋ A
becomes ext ρ : ∀ {A B} → Γ , B ∋ A → Δ , B ∋ A where B is the type of
argument when visiting an abstraction λ.

```agda
rename : Rename Γ Δ
  → (Γ ⊢ A)
  → (Δ ⊢ A)
rename ρ (` x)   = ` ρ x
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (ƛ M)   = ƛ rename (ext ρ) M
```

Similarly, we proceed with a substitution σ : ∀ {A} → Γ ∋ A → Δ ⊢ A.
Note that

    rename S_ : ∀ {A} → Γ ∋ A → Γ , B ∋ A

merely enlarges the context and increments the de Bruijn index for
every Γ ∋ A.

```agda
exts : Subst Γ Δ → Subst (Γ , A) (Δ , A)
exts σ Z     = ` Z
exts σ (S p) = rename S_ (σ p)

_⟪_⟫
  : Γ ⊢ A 
  → Subst Γ Δ
  → Δ ⊢ A
(` x)   ⟪ σ ⟫ = σ x
(M · N) ⟪ σ ⟫ = M ⟪ σ ⟫ · N ⟪ σ ⟫
(ƛ M)   ⟪ σ ⟫ = ƛ M ⟪ exts σ ⟫
```

Singleton Substitution
----------------------

Finally, the ususal singleton substitution

    _[ M / x₀ ] : Γ , B ⊢ A → Γ ⊢ B 

is a special instance of parallel substitution as it suffices to
define a substitution

    σ : ∀ {A} → Γ , B ∋ A → Γ ∋ A 

for free variables. 

```agda
subst-zero : {B : Type}
  → Γ ⊢ B
  → Subst (Γ , B) Γ
subst-zero N Z      =  N
subst-zero _ (S x)  =  ` x

_[_] : Γ , B ⊢ A
     → Γ ⊢ B
       ---------
     → Γ ⊢ A
_[_] N M =  N ⟪ subst-zero M ⟫
```

### Example

```agda
_ : ∀ {A} → ∅ ⊢ nat A
_ = e [ c₀ ]
  where
    e : ∅ , B ⊢ B
    e = # 0
```

Single-step reduction
---------------------

In our informal development -→β is defined only for beta-redex
followed by one-step full β-reduction. These two rules can be combined
altogether.

```agda
infix 3 _-→_
data _-→_ {Γ} : (M N : Γ ⊢ A) → Set where
  β-ƛ·
    : (ƛ M) · N -→ M [ N ]

  ξ-ƛ
    : M -→ M′
    → ƛ M -→ ƛ M′    
  ξ-·ₗ
    : L -→ L′
      ---------------
    → L · M -→ L′ · M
  ξ-·ᵣ
    : M -→ M′
      ---------------
    → L · M -→ L · M′
```

Reduction sequence of -→ 
--------------------------------------

The reduction sequence M -↠ N from M to N is just a list of reductions
such that the RHS of a head reduction must be the LHS of the tail of
reductions.

```agda
data _-↠_ {Γ A} : (M N : Γ ⊢ A) → Set where
  _∎ : (M : Γ ⊢ A)
    → M -↠ M       -- empty list
    
  _-→⟨_⟩_
    : ∀ L          -- this can usually be inferred by the following reduction 
    → L -→ M       -- the head of a list 
    → M -↠ N       -- the tail
      -------
    → L -↠ N

infix  2 _-↠_ _∎
infixr 2 _-→⟨_⟩_
```

Viewing -↠ as a relation (a binary predicate), we can see that -↠ is
reflexive by definition.

```agda
-↠-refl : M -↠ M
-↠-refl {M = M} = M ∎
```

The relation -↠ is also transitive in the sense that

    if L -↠ M and M -↠ N then L -↠ N

the proof itself is in fact the concatenation of two lists.

```agda
_-↠⟨_⟩_ : ∀ L
  → L -↠ M → M -↠ N
  -----------------
  → L -↠ N
M -↠⟨ M ∎               ⟩ M-↠N  = M-↠N
L -↠⟨ L -→⟨ L-↠M ⟩ M-↠N ⟩ N-↠N′ = L -→⟨ L-↠M ⟩ (_ -↠⟨ M-↠N ⟩ N-↠N′)

infixr 2 _-↠⟨_⟩_
```

### Exercise

Show that -↠ is a congruence. That is, show the following lemmas.

```agda
ƛ-↠ : M -↠ M′
      -----------
    → ƛ M -↠ ƛ M′
ƛ-↠ (M ∎)               = ƛ M ∎
ƛ-↠ (L -→⟨ L-→M ⟩ M-↠N) = ƛ L -→⟨ ξ-ƛ L-→M ⟩ ƛ-↠ M-↠N
  
·-↠ : M -↠ M′
    → N -↠ N′
    → M · N -↠ M′ · N′
·-↠ = ?
```

Normal form
-----------

Recall that a term M is in normal form if M --̸→ N for any N.

A syntactical characterisation of being in normal form is

    λ x₀ x₁ ⋯ xₙ. x N₀ N₁ N₂ ⋯ Nₘ  
    │             ╰── Neutral ─╯│  
    ╰──────── Normal ───────────╯  

where x is a variable (which need not be bound at all) and Nᵢ's are
all in normal form. This characterisation is defined as two inductive
families mutually as follows.

```agda
data Neutral : Γ ⊢ A → Set 
data Normal  : Γ ⊢ A → Set 

data Neutral where
  `_  : (x : Γ ∋ A)
    → Neutral (` x)
  _·_ : Neutral L
    → Normal M
    → Neutral (L · M)

data Normal where
  ᵒ_  : Neutral M → Normal M
  ƛ_  : Normal M  → Normal (ƛ M)
```

The soundness of characterisation is proved by induction on the
derivation of Normal M (resp. Neutral M) and if necessary on M -→ M.

The completeness is trickier as we will need to analyse the induction
hypothesis further.

Proofs are left as an exercise for you.

### Exercise.

```agda
normal-soundness  : Normal M  → ¬ (M -→ M′)
neutral-soundness : Neutral M → ¬ (M -→ M′)

normal-completeness : (M : Γ ⊢ A)
  → ((N : Γ ⊢ A) → ¬ (M -→ N))
  → Normal M 

neutral-soundness = {!!}

normal-soundness  = {!!}

normal-completeness (` x)   M↛N = {!!}
normal-completeness (ƛ M)   M↛N = {!!}
normal-completeness (L · M) M↛N with normal-completeness L ·ₗ-nf | normal-completeness M ·ᵣ-nf
  where
    ·ₗ-nf : ∀ N → ¬ (L -→ N)
    ·ₗ-nf N L-→N = M↛N (N · M) (ξ-·ₗ L-→N)
    ·ᵣ-nf : ∀ N → ¬ (M -→ N)
    ·ᵣ-nf N M-→N = M↛N (L · N) (ξ-·ᵣ M-→N)
... | ᵒ x            | M↓ = {!!}
... | ƛ_ {M = L′} L↓ | M↓ = ⊥-elim {!!}
```

Preservation
------------

Preservation theorem is trivial in this formal development, since

  M -→ N

is an inductive family indexed by two terms of the same type.

Progress
--------

Progress theorem state that every well-typed term M is either

  1. in normal form or
  2. reducible

so we introduce a predicate `Progress` over well-typed terms M for
this statement.

```agda
data Progress (M : Γ ⊢ A) : Set where
  step
    : M -→ N
      ----------
    → Progress M

  done : Normal M
    → Progress M
```

Progress theorm is proved by induction on the derviation of Γ ⊢ M : A
in the informal development so that foramlly it is merely an induction
on M : Γ ⊢ A.

```agda
progress : (M : Γ ⊢ A)
  → Progress M
progress (` x)       = {!!}
progress (ƛ M)       = {!!}
progress (` x · N)   = {!!}
progress ((ƛ M) · N) = {!!}
progress (LM@(L · M) · N) with progress LM
... | step LM→K    = step (ξ-·ₗ LM→K)
... | done (ᵒ LM↓) with progress N
...   | step N-→N′ = step (ξ-·ᵣ N-→N′)
...   | done N↓    = done (ᵒ (LM↓ · N↓))
```
