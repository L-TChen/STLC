module Semantics.CwF where

open import Prelude
  hiding (_,_)

record IsPreCategory (Obj : 𝓤 ̇) (Mor : Obj → Obj → 𝓤 ̇)
  (_•_ : {X Y Z : Obj} → Mor Y Z → Mor X Y → Mor X Z)
  (id : {X : Obj} → Mor X X) : 𝓤  ̇ where 

  field
    identity : {X : Obj}
      → ({Y : Obj} (f : Mor X Y) → id • f ≡ f) × ({Y : Obj} (f : Mor X Y) → f • id ≡ f)
    assoc    : {A B C D : Obj} {f : Mor A B} {g : Mor B C} {h : Mor C D}
      → h • (g • f) ≡ (h • g) • f

  identityₗ : {X Y : Obj} (f : Mor X Y) → id • f ≡ f
  identityₗ = proj₁ identity

  identityʳ : {X Y : Obj} (f : Mor X Y) → f • id ≡ f
  identityʳ = proj₂ identity
  
  Terminal : Obj → 𝓤 ̇
  Terminal ⊤ = Σ[ ◇ ∈ (∀ X → Mor X ⊤) ] (◇ ⊤ ≡ id {⊤}) × ({X Y : Obj} (f : Mor X Y) → ◇ Y • f ≡ ◇ X)

record PreCategory 𝓤 : 𝓤 ⁺ ̇ where
  field
    Obj           : 𝓤 ̇
    Mor           : Obj → Obj → 𝓤 ̇
    _•_           : {X Y Z : Obj} → Mor Y Z → Mor X Y → Mor X Z
    id            : {X : Obj} → Mor X X
    isPreCategory : IsPreCategory Obj Mor _•_ id

  open IsPreCategory isPreCategory public

open PreCategory

record IsFunctor (𝓒 𝓓 : PreCategory 𝓤)
  (F : 𝓒 .Obj → 𝓓 .Obj) (fmap : {X Y : 𝓒 .Obj} → 𝓒 .Mor X Y → 𝓓 .Mor (F X) (F Y)) : 𝓤 ̇ where
  field
    identity-preservation : {X : 𝓒 .Obj}
      → fmap {X} (id 𝓒) ≡ 𝓓 .id
    ∘-preservation        : {X Y Z : 𝓒 .Obj} (f : 𝓒 .Mor X Y) (g : 𝓒 .Mor Y Z)
      → fmap (_•_  𝓒 g f) ≡ (_•_ 𝓓) (fmap g) (fmap f)

------------------------------------------------------------------------------
-- Simply-typed Categories with Families

record IsSCwF 
  (Ctx   : 𝓤 ̇) (Sub : Ctx → Ctx → 𝓤 ̇) (⋄ : Ctx) 
  (ids   : ∀ {Γ    } → Sub Γ Γ)
  (_⨟_   : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Γ Θ → Sub Δ Θ)
  (Ty    : 𝓤 ̇)
  (Tm    : Ctx → Ty → 𝓤 ̇)
  (⟪_⟫_  : ∀ {Γ Δ A} → Sub Δ Γ → Tm Γ A → Tm Δ A)
  (_,_   : Ctx → Ty → Ctx)
  (⟨_,_⟩ : ∀ {Γ Δ A} → Sub Δ Γ → Tm Δ A → Sub Δ (Γ , A))
  (p     : ∀ {Γ A  } → Sub (Γ , A) Γ)
  (q     : ∀ {Γ A  } → Tm (Γ , A) A)
  : 𝓤 ⁺ ̇ where
  field
    ctxIsPreCategory : IsPreCategory Ctx Sub (λ g f → f ⨟ g) ids
    ⋄isTerminal      : IsPreCategory.Terminal ctxIsPreCategory ⋄
    ⟪⟫-preserves-ids : {Γ : Ctx} {A : Ty}
      → (t : Tm Γ A) → ⟪ ids ⟫ t ≡ t
    ⟪⟫-preserves-⨟   : {Γ Δ Θ : Ctx} {A : Ty} → (t : Tm Γ A) →
      (γ : Sub Δ Γ) → (δ : Sub Θ Δ) → ⟪ δ ⨟ γ ⟫ t ≡ ⟪ δ ⟫ ⟪ γ ⟫ t
    ctxComprehension : {Γ Δ : Ctx} {A : Ty}
      → (γ : Sub Δ Γ) (a : Tm Δ A)
      → (⟨ γ , a ⟩ ⨟ p ≡ γ) × (⟪ ⟨ γ , a ⟩ ⟫ q ≡ a)
    idExt   : {Γ : Ctx}   {A : Ty} → ⟨ p {Γ} {A} , q ⟩ ≡ ids
    compExt : {Γ Δ : Ctx} {A : Ty} (a : Tm Γ A) (γ : Sub Γ Δ) (δ : Sub Δ Γ)
      → δ ⨟ ⟨ γ , a ⟩ ≡ ⟨ δ ⨟ γ , ⟪ δ ⟫ a ⟩

  private
    variable
      Γ Δ : Ctx

  ◇ : {Γ : Ctx} → Sub Γ ⋄
  ◇ {Γ} = ⋄isTerminal .proj₁ Γ

  ids◇ : ◇ ≡ ids
  ids◇ = ⋄isTerminal .proj₂ .proj₁

  ◇-⨟ : (γ : Sub Γ Δ) → γ ⨟ ◇ ≡ ◇
  ◇-⨟ γ = ⋄isTerminal .proj₂ .proj₂ γ


record SCwF 𝓤 (𝓑 : 𝓤 ̇) : 𝓤 ⁺ ̇ where
  field
    Ctx    : 𝓤 ̇
    ⋄      : Ctx
    Sub    : Ctx → Ctx → 𝓤 ̇
    Ty     : 𝓤 ̇
    ⟦_⟧𝓑   : 𝓑 → Ty
    Tm     : Ctx → Ty → 𝓤 ̇
    _,_    : Ctx → Ty → Ctx
    ⟪_⟫_   : ∀ {Γ Δ A} → Sub Δ Γ → Tm Γ A → Tm Δ A
    ids    : ∀ {Γ    } → Sub Γ Γ
    _⨟_    : ∀ {Γ Δ Θ} → Sub Δ Γ → Sub Γ Θ → Sub Δ Θ
    ⟨_,_⟩  : ∀ {Γ Δ A} → Sub Γ Δ → Tm Γ A  → Sub Γ (Δ , A)
    p      : ∀ {Γ A  } → Sub (Γ , A) Γ
    q      : ∀ {Γ A}   → Tm (Γ , A) A
    isSCwF : IsSCwF Ctx Sub ⋄ ids _⨟_ Ty Tm ⟪_⟫_ _,_ ⟨_,_⟩ p q

  open IsSCwF isSCwF public

  infixl 6 _,_
  infixr 7 ⟪_⟫_

module SCwFMorphisms 𝓤 B (𝓒 𝓓 : SCwF 𝓤 B) where

  open SCwF 𝓒 renaming
    ( Ctx  to Ctx₁ ; ⋄ to ⋄₁ ; Sub to Sub₁ ; _⨟_ to _⨟₁_
    ; Ty   to Ty₁
    ; ⟦_⟧𝓑 to ⟦_⟧𝓑₁
    ; Tm   to  Tm₁
    ; ⟪_⟫_ to infixr 6 ⟪_⟫₁_
    ; _,_  to _,₁_ ; p to p₁ ; q to q₁
    )

  open SCwF 𝓓 renaming
    ( Ctx  to Ctx₂ ; ⋄ to ⋄₂ ; Sub to Sub₂ ; _⨟_ to _⨟₂_
    ; ⟦_⟧𝓑 to ⟦_⟧𝓑₂
    ; Ty   to Ty₂
    ; Tm   to  Tm₂
    ; ⟪_⟫_ to infixr 6 ⟪_⟫₂_
    ; _,_  to _,₂_ ; p to p₂ ; q to q₂
    )

  record IsMorphism (F : Ctx₁ → Ctx₂)
    (map : {Γ Δ : Ctx₁} → Sub₁ Γ Δ → Sub₂ (F Γ) (F Δ))
    (σTy : Ty₁ → Ty₂)
    (σTm : {Γ : Ctx₁} {A : Ty₁} → Tm₁ Γ A → Tm₂ (F Γ) (σTy A)) : 𝓤 ̇ where
    field
      ⋄-preservation : F ⋄₁ ≡ ⋄₂
      ⨟-preservation : {Γ Δ Θ : Ctx₁} → (γ : Sub₁ Γ Δ) (δ : Sub₁ Δ Θ)
        → map (γ ⨟₁ δ) ≡ map γ ⨟₂ map δ
      ⟪⟫-preservation : {Γ Δ : Ctx₁} {A : Ty₁} → (γ : Sub₁ Γ Δ) → (t : Tm₁ Δ A)
        → σTm (⟪ γ ⟫₁ t) ≡ ⟪ map γ ⟫₂ σTm t
      ,-preservation : {Γ : Ctx₁} {A : Ty₁}
        → F (Γ ,₁ A) ≡ (F Γ ,₂ σTy A)
      p-preservation : {Γ : Ctx₁} {A : Ty₁}
        → map p₁ ≡ p₂ ⦂ [ i ↦ Sub₂ (,-preservation {Γ} {A} i) (F Γ) ]
      q-preservation : {Γ : Ctx₁} {A : Ty₁}
        → σTm q₁ ≡ q₂ ⦂ [ i ↦ Tm₂ (,-preservation {Γ} {A} i) (σTy A) ]

------------------------------------------------------------------------------
-- Categories with Families

record IsCwF 
  (Ctx    : 𝓤 ̇) (Sub : Ctx → Ctx → 𝓤 ̇) (⋄ : Ctx) 
  (ids    : {Γ : Ctx} → Sub Γ Γ) (_⨟_   : {Γ Δ Θ : Ctx} → Sub Δ Γ → Sub Γ Θ → Sub Δ Θ)
  (Ty     : Ctx → 𝓤 ̇)
  (Tm     : (Γ : Ctx) → Ty Γ → 𝓤 ̇)
  (⟪_⟫ᵗʸ_ : {Γ Δ : Ctx}
    → Sub Δ Γ → Ty Γ → Ty Δ)
  (⟪_⟫_   : {Γ Δ : Ctx} {A : Ty Γ}
    → (γ : Sub Δ Γ) → Tm Γ A → Tm Δ (⟪ γ ⟫ᵗʸ A))
  (_,_    : (Γ : Ctx) → Ty Γ → Ctx)
  (p      : {Γ : Ctx} {A : Ty Γ} → Sub (Γ , A) Γ)
  (q      : {Γ : Ctx} {A : Ty Γ} → Tm  (Γ , A) (⟪ p ⟫ᵗʸ A))
  (⟨_,_⟩  : {Γ Δ : Ctx} {A : Ty Γ} → (γ : Sub Δ Γ) → Tm Δ (⟪ γ ⟫ᵗʸ A) → Sub Δ (Γ , A))
  : 𝓤 ⁺ ̇ where
  open Eq.≡-Reasoning

  field
    ctxIsPreCategory : IsPreCategory Ctx Sub (λ g f → f ⨟ g) ids
    ⋄isTerminal      : IsPreCategory.Terminal ctxIsPreCategory ⋄

    ⟪⟫ᵗʸ-preserves-ids : {Γ : Ctx} {A : Ty Γ}
      → ⟪ ids ⟫ᵗʸ A ≡ A
    ⟪⟫-preserves-ids : {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A)
      → (⟪ ids ⟫ t) ≡ t ⦂ [ i ↦ Tm Γ (⟪⟫ᵗʸ-preserves-ids {Γ} {A} i) ]

    ⟪⟫ᵗʸ-preserves-⨟   : {Γ Δ Θ : Ctx} {A : Ty Δ} (γ : Sub Γ Δ) (δ : Sub Θ Γ)
      → ⟪ δ ⨟ γ ⟫ᵗʸ A ≡ ⟪ δ ⟫ᵗʸ ⟪ γ ⟫ᵗʸ A
    ⟪⟫-preserves-⨟   : {Γ Δ Θ : Ctx} {A : Ty Δ} (γ : Sub Γ Δ)  (δ : Sub Θ Γ) (t : Tm Δ A)
      → ⟪ δ ⨟ γ ⟫ t ≡ ⟪ δ ⟫ ⟪ γ ⟫ t ⦂ [ i ↦ Tm Θ (⟪⟫ᵗʸ-preserves-⨟ {Γ} {Δ} {Θ} {A} γ δ i) ]
    ctxComprehension₁ : {Γ Δ : Ctx} {A : Ty Γ} 
      → (γ : Sub Δ Γ) (a : Tm Δ (⟪ γ ⟫ᵗʸ A))
      → ⟨ γ , a ⟩ ⨟ p ≡ γ

  ⟪⟫-with-comprhension : {Γ Δ : Ctx} {A : Ty Γ} (γ : Sub Δ Γ) (a : Tm Δ (⟪ γ ⟫ᵗʸ A))
    → ⟪ ⟨ γ , a ⟩ ⟫ᵗʸ ⟪ p ⟫ᵗʸ A ≡ ⟪ γ ⟫ᵗʸ A
  ⟪⟫-with-comprhension {Γ} {Δ} {A} γ a = begin
    ⟪ ⟨ γ , a ⟩ ⟫ᵗʸ (⟪ p ⟫ᵗʸ A)
      ≡⟨ sym (⟪⟫ᵗʸ-preserves-⨟ p ⟨ γ , a ⟩) ⟩
    ⟪ ⟨ γ , a ⟩ ⨟ p ⟫ᵗʸ A
      ≡⟨ cong (⟪_⟫ᵗʸ A) (ctxComprehension₁ γ a) ⟩
    ⟪ γ ⟫ᵗʸ A ∎

  field
    ctxComprehension₂ : {Γ Δ : Ctx} {A : Ty Γ} 
      → (γ : Sub Δ Γ) (a : Tm Δ (⟪ γ ⟫ᵗʸ A))
      → ⟪ ⟨ γ , a ⟩ ⟫ q ≡ a ⦂ [ i ↦ Tm Δ (⟪⟫-with-comprhension γ a i) ]
    idExt   : {Γ   : Ctx} {A : Ty Γ}
      → ⟨ p {Γ} {A} , q ⟩ ≡ ids
    compExt : {Γ Δ : Ctx} {A : Ty Δ} (γ : Sub Γ Δ) (a : Tm Γ (⟪ γ ⟫ᵗʸ A)) (δ : Sub Δ Γ)
      → δ ⨟ ⟨ γ , a ⟩ ≡
        ⟨ δ ⨟ γ , subst (λ B → Tm Δ B) (sym (⟪⟫ᵗʸ-preserves-⨟ γ δ)) (⟪ δ ⟫ a) ⟩

  ⟨⟩ : (Γ : Ctx) → Sub Γ ⋄
  ⟨⟩ = proj₁ ⋄isTerminal

record CwF 𝓤 : 𝓤 ⁺ ̇ where
  field
    Ctx    : 𝓤 ̇
    Sub    : Ctx → Ctx → 𝓤 ̇
    ⋄      : Ctx 
    ids    : {Γ : Ctx} → Sub Γ Γ
    _⨟_    : {Γ Δ Θ : Ctx} → Sub Δ Γ → Sub Γ Θ → Sub Δ Θ
    Ty     : Ctx → 𝓤 ̇
    Tm     : (Γ     : Ctx) → Ty Γ → 𝓤 ̇
    ⟪_⟫ᵗʸ_ : {Γ Δ   : Ctx} → Sub Δ Γ → Ty Γ → Ty Δ
    ⟪_⟫_   : {Γ Δ   : Ctx} {A : Ty Γ} → (γ : Sub Δ Γ) → Tm Γ A → Tm Δ (⟪ γ ⟫ᵗʸ A)
    _,_    : (Γ     : Ctx) → Ty Γ → Ctx
    p      : {Γ     : Ctx} {A : Ty Γ} → Sub (Γ , A) Γ
    q      : {Γ     : Ctx} {A : Ty Γ} → Tm  (Γ , A) (⟪ p ⟫ᵗʸ A)
    ⟨_,_⟩  : {Γ Δ   : Ctx} {A : Ty Γ} → (γ : Sub Δ Γ) → Tm Δ (⟪ γ ⟫ᵗʸ A) → Sub Δ (Γ , A)
    isCwF  : IsCwF Ctx Sub ⋄ ids _⨟_ Ty Tm ⟪_⟫ᵗʸ_ ⟪_⟫_ _,_ p q ⟨_,_⟩

  open IsCwF isCwF public

  infixl 6 _,_
  infixr 7 ⟪_⟫ᵗʸ_ ⟪_⟫_
