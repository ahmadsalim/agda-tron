module TRON.Semantics where

import Level

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool as Bool hiding (_∧_; _∨_; if_then_else_) renaming (Bool to 𝔹; _≟_ to _≟B_)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product
open import Data.Sum as Sum
open import Data.Maybe as Maybe hiding (Any)
open import Data.List as List
open import Data.List.Any as Any
open import Data.String renaming (_≟_ to _≟S_)

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality

open import Category.Monad

open import Function

open import Util
open DecEq ⦃ ... ⦄
open import TRON.Syntax

module Concrete (structure : Static.Structure) where
  open Static
  open Structure structure
  open Dynamic structure
  open PartialFunctions
  open FSet

  record Instance : Set where
    constructor mk-inst
    field
      loc : ℕ

  data Value : Set where
    ⏚   : Value
    «_»  : FSet Instance → Value

  private
    «»-injective : ∀ {os os′} → « os » ≡ « os′ » → os ≡ os′
    «»-injective refl = refl

  -- TODO Move
  instance
    ℕ-deceq : DecEq ℕ
    ℕ-deceq = record { _≟_ = _≟ℕ_ }

  instance
    Instance-deceq : DecEq Instance
    Instance-deceq = record { _≟_ = _≟I_ }
      where _≟I_ : (x y : Instance) → Dec (x ≡ y)
            mk-inst x ≟I mk-inst y with (x ≟ y)
            mk-inst x ≟I mk-inst .x | yes refl = yes refl
            mk-inst x ≟I mk-inst y  | no  x≢y  = no (λ mk-instx≢mk-insty → x≢y (mk-inst-inj mk-instx≢mk-insty))
              where mk-inst-inj : ∀ {x y} → mk-inst x ≡ mk-inst y → x ≡ y
                    mk-inst-inj refl = refl

  instance
    Value-deceq : DecEq Value
    Value-deceq = record { _≟_ = _≟V_ }
      where _≟V_ : (x y : Value) → Dec (x ≡ y)
            ⏚ ≟V ⏚ = yes refl
            ⏚ ≟V « os » = no (λ ())
            « os » ≟V ⏚ = no (λ ())
            « os » ≟V « os′ » with (os ≟ os′)
            « os » ≟V « .os » | yes refl = yes refl
            « os » ≟V « os′ » | no os≢os′ = no (λ «os»≡«os′» → os≢os′ («»-injective «os»≡«os′»))

  _∖⊥_ : Value → FSet Instance → Value
  ⏚ ∖⊥ os′ = « os′ »
  « os » ∖⊥ os′ = « os FSets.∖ os′ »

  ⋓⊥ : FSet Value → Maybe (FSet Instance)
  ⋓⊥ vs with (Any.any (⏚ ≟_) (elements vs))
  ⋓⊥ vs | yes ⏚∈vs = nothing
  ⋓⊥ vs | no  ⏚∉vs = just (FSets.⋓ (FSets.map/≡ vs (λ { (‹ ⏚ › ⦃ ⏚∈vs ⦄) → ⊥-elim-irr (⏚∉vs ⏚∈vs) ; ‹ « os » › → os })))

  Store : Set
  Store = Var ⇀ Value

  Heap : Set
  Heap = Instance ⇀ FSet.Element fields ⇀ Value

  TypeEnv : Set
  TypeEnv = Instance ⇀ FSet.Element classes

  infix 1 _∣_∣_

  record Memory : Set where
    constructor _∣_∣_
    field
      σ : Store
      h : Heap
      Γ : TypeEnv

  ValidStore : (μ : Memory) → Set
  ValidStore (σ ∣ h ∣ Γ) = ∀ {x os} → σ · x ≡ « os » → os FSets.⊆ dom h

  ValidHeapLinks : (μ : Memory) → Set
  ValidHeapLinks (σ ∣ h ∣ Γ) = ∀ {o f os} → h · o · f ≡ « os » → os FSets.⊆ dom h

  TypedHeapInstances : (μ : Memory) → Set
  TypedHeapInstances (σ ∣ h ∣ Γ) = dom h FSets.≈ dom Γ

  TypedHeapLinks : (μ : Memory) (links-valid : ValidHeapLinks μ) (dom·h≈dom·Γ : TypedHeapInstances μ) → Set
  TypedHeapLinks (σ ∣ h ∣ Γ) links-valid (dom·h⊆dom·Γ , dom·Γ⊆dom·h) =
    ∀ {c} {o : Element (dom h)} {f c′ os} →
        Γ · (FSets.coe dom·h⊆dom·Γ o) ≡ c →
        ref c f ≡ c′ →
        Σ-inst (Element.value f FSets.∈ dom (h · o)) -- f is instantiated
          (∀ (h·o·f≡os : h · o · ‹ Element.value f › ≡ « os ») (o′ : Element os) -- all elements have a type which is a subset of the expected one
          → (Γ · FSets.coe (FSets.⊆-trans {ys = dom Γ} (links-valid h·o·f≡os) dom·h⊆dom·Γ) o′) gen⋆ c′)

  CompleteHeapLinks : (μ : Memory) (dom·h≈dom·Γ : TypedHeapInstances μ) → Set
  CompleteHeapLinks (σ ∣ h ∣ Γ) (dom·h⊆dom·Γ , dom·Γ⊆dom·h) =
    ∀ {c} {o : Element (dom h)} →
      Γ · (FSets.coe dom·h⊆dom·Γ o) ≡ c →
      dom (h · o) FSets.≈ class-fields c

  record IsWellformed (μ : Memory) : Set₁ where
    open Memory μ public
    field
      store-valid          : ValidStore μ
      heap-instances-typed : TypedHeapInstances μ
      heap-links-valid     : ValidHeapLinks μ
      heap-links-complete  : CompleteHeapLinks μ heap-instances-typed
      heap-links-typed     : TypedHeapLinks μ heap-links-valid heap-instances-typed

    private
      contains : Element (dom h) → Element (dom h) → Set
      contains o o′ = Σ[ f ∈ Element (dom (h · o)) ] (∀ {os} → ((h · o · f) ≡ « os ») → containment (Element.value f) ≡ ✦ × (Element.value o′ FSets.∈ os))

      contains⋆ : Element (dom h) → Element (dom h) → Set
      contains⋆ o o′ = o Closures.⟨ contains ⟩* o′

    field
      containment-acyclic       : ∀ {o o′} → contains⋆ o o′ → contains⋆ o′ o → ⊥
      containment-unique-inst   : ∀ {o o′ o″} → contains o′ o → contains o″ o → o′ ≡ o″
      containment-unique-field  : ∀ {o o′} → (o′-c-o₁ o′-c-o₂ : contains o′ o) → proj₁ o′-c-o₁ ≡ proj₁ o′-c-o₂

    _contains_ _contains⋆_ : Element (dom h) → Element (dom h) → Set -- Due to Agda bug
    _contains_ = contains
    _contains⋆_ = contains⋆

  𝔣𝔦-σ : Store → FSet Instance
  𝔣𝔦-σ σ = FSets.⋓ (FSets.map/≡ (dom σ) (λ x → case σ · x of λ { ⏚ → FSets.∅ ; « os » → os }))

  𝔣𝔦-h : Heap → FSet Instance
  𝔣𝔦-h h = dom h FSets.∪ FSets.⋓ (FSets.map/≡ (dom h) (λ o → FSets.⋓ (FSets.map/≡ (dom (h · o)) (λ f → case h · o · f of λ { ⏚ → FSets.∅ ; « os » → os }))))

  𝔣𝔦-Γ : TypeEnv → FSet Instance
  𝔣𝔦-Γ Γ = dom Γ

  𝔣𝔦 : Memory → FSet Instance
  𝔣𝔦 (σ ∣ h ∣ Γ) = 𝔣𝔦-σ σ FSets.∪ 𝔣𝔦-h h FSets.∪ 𝔣𝔦-Γ Γ

  infix 0 _fresh_

  _fresh_ : Instance → Memory → Set
  o fresh μ = ∀ (o′ : Element (𝔣𝔦 μ)) → o ≢ Element.value o′

  infix 0 _,_⇓𝓔_

  data _,_⇓𝓔_ : SetExpr → Store → FSet Instance → Set where
    ⇓𝓔-var : ∀ {x σ os} →
              ⦃ x∈dom·σ : x FSets.∈ dom σ ⦄ →
              σ · ‹ x › ≡ « os » →
              ------------------------------------
              ‹ x › , σ ⇓𝓔 os

    ⇓𝓔-∅   : ∀ {σ} →
              --------------------
              ∅ , σ ⇓𝓔 FSets.∅

    ⇓𝓔-∪   : ∀ {e₁ e₂ σ os₁ os₂} →
              e₁ , σ ⇓𝓔 os₁ →
              e₂ , σ ⇓𝓔 os₂ →
              -------------------------------
              e₁ ∪ e₂ , σ ⇓𝓔 os₁ FSets.∪ os₂

    ⇓𝓔-∩   : ∀ {e₁ e₂ σ os₁ os₂} →
              e₁ , σ ⇓𝓔 os₁ →
              e₂ , σ ⇓𝓔 os₂ →
              --------------------------------
              e₁ ∩ e₂ , σ ⇓𝓔 os₁ FSets.∩ os₂

    ⇓𝓔-∖   : ∀ {e₁ e₂ σ os₁ os₂} →
              e₁ , σ ⇓𝓔 os₁ →
              e₂ , σ ⇓𝓔 os₂ →
              -------------------------------
              e₁ ∖ e₂ , σ ⇓𝓔 os₁ FSets.∖ os₂


  infix 0 _,_⇓𝓑_

  data _,_⇓𝓑_ : BoolExpr → Store → 𝔹 → Set where
    ⇓𝓑-⊆ : ∀ {e₁ e₂ σ os₁ os₂} →
              e₁ , σ ⇓𝓔 os₁ →
              e₂ , σ ⇓𝓔 os₂ →
              ------------------------------------
              e₁ ⊆ e₂ , σ ⇓𝓑 ⌊ os₁ FSets.?⊆ os₂ ⌋
    ⇓𝓑-⊈ : ∀ {e₁ e₂ σ os₁ os₂} →
              e₁ , σ ⇓𝓔 os₁ →
              e₂ , σ ⇓𝓔 os₂ →
              ------------------------------------
              e₁ ⊈ e₂ , σ ⇓𝓑 not ⌊ os₁ FSets.?⊆ os₂ ⌋
    ⇓𝓑-∧  : ∀ {b₁ b₂ σ t₁ t₂} →
              b₁ , σ ⇓𝓑 t₁ →
              b₂ , σ ⇓𝓑 t₂ →
              ------------------------------------
              b₁ ∧ b₂ , σ ⇓𝓑 t₁ Bool.∧ t₂
    ⇓𝓑-∨  : ∀ {b₁ b₂ σ t₁ t₂} →
              b₁ , σ ⇓𝓑 t₁ →
              b₂ , σ ⇓𝓑 t₂ →
              ------------------------------------
              b₁ ∨ b₂ , σ ⇓𝓑 t₁ Bool.∨ t₂

  data matching : FSet Instance → Element classes → TypeEnv → FSet Instance → Set where
    []    : ∀ {c Γ} →
              --------------------------------
              matching FSets.∅ c Γ FSets.∅
    _∷⟨_⟩_ : ∀ {o os [o]∪os os′ c Γ} → ⦃ o∈dom·Γ : o FSets.∈ dom Γ ⦄ →
              (Γ · ‹ o ›) gen⋆ c →
              FSets.[ o ]⊎ os ≈ [o]∪os →
              matching os c Γ os′ →
              ------------------------------------
              matching [o]∪os c Γ (os′ FSets.◀ o)
    _∷¬⟨_⟩_ : ∀ {o os [o]∪os os′ c Γ} → ⦃ o∈dom·Γ : o FSets.∈ dom Γ ⦄ →  ¬ ((Γ · ‹ o ›) gen⋆ c) → FSets.[ o ]⊎ os ≈ [o]∪os →  matching os c Γ os′ → matching [o]∪os c Γ os′


  data children : FSet Instance → Heap → FSet Instance → Set where
    []  : ∀ {h} →
            ------------------------------------
            children FSets.∅ h FSets.∅
    _∷⟨_⟩_ : ∀ {o os [o]∪os h os′ os″} → .⦃ o∈dom·h : o FSets.∈ dom h ⦄ →
              let fs✦ , irr fs✦⊆dom·h·o = FSets.filter (dom (h · ‹ o ›)) (λ f → ⌊ containment (Element.value f) ≟ ✦ ⌋)
              in ⋓⊥ (FSets.map/≡ fs✦ (λ f → h · ‹ o › ⦃ o∈dom·h ⦄ · FSets.coe fs✦⊆dom·h·o f)) ≡ just os′ →
                 FSets.[ o ]⊎ os ≈ [o]∪os →
                 children os h os″ →
                 ------------------------------------
                 children [o]∪os h (os′ FSets.∪ os″)

  data matching⋆ : FSet Instance → Element classes → Heap → TypeEnv → FSet Instance → Set where
    []    : ∀ {c h Γ} →
              --------------------------------
              matching⋆ FSets.∅ c h Γ FSets.∅
    _∷⟨_⟩_ : ∀ {os os′ os″ osᶜ c h Γ} →
                matching os c Γ os′ →
                children os h osᶜ →
                matching⋆ osᶜ c h Γ os″ →
                ------------------------------------
                matching⋆ os c h Γ (os′ FSets.∪ os″)

  infix 0 _,_⇓𝓜_

  data _,_⇓𝓜_ : MatchExpr → Memory → FSet Instance → Set where
    ⇓𝓜-⌈⌉ : ∀ {e σ h Γ os} →
                e , σ ⇓𝓔 os →
              ------------------------
                ⌈ e ⌉ , σ ∣ h ∣ Γ ⇓𝓜 os
    ⇓𝓜-match  : ∀ {e c σ h Γ os os′} →
                    e , σ ⇓𝓔 os →
                    matching os c Γ os′ →
                    ----------------------------
                    e match c , σ ∣ h ∣ Γ ⇓𝓜 os′
    ⇓𝓜-match⋆ : ∀ {e c σ h Γ os os′} →
                    e , σ ⇓𝓔 os →
                    matching⋆ os c h Γ os′ →
                    -------------------------
                    e match⋆ c , σ ∣ h ∣ Γ ⇓𝓜 os′

  disown : FSet Instance → Heap → Heap
  disown os h = h ⟪ dom h ∥ (λ o → Element.value o ↦ h · o ⟪ dom (h · o) ∥ (λ f → Element.value f ↦ (h · o · f) ∖⊥ os) ⟫) ⟫

  mutual
    infix 0 _↤_⊢_,_⇓𝓢-each_

    data _↤_⊢_,_⇓𝓢-each_ : Var → FSet Instance → Statement → Memory → Memory → Set where
      ⇓𝓢-each-∅ : ∀ {x s μ} →
                  ------------------------------
                  x ↤ FSets.∅ ⊢ s , μ ⇓𝓢-each μ
      ⇓𝓢-each-⊎ : ∀ {x s o os′ os σ h Γ μ″ μ′} →
                  FSets.[ o ]⊎ os′ ≈ os →
                  s , σ ⟪ x ↦ « FSets.[ o ] » ⟫ ∣ h ∣ Γ ⇓𝓢 μ″ →
                  x ↤ os′ ⊢ s , μ″ ⇓𝓢-each μ′ →
                  ------------------------------
                  x ↤ os ⊢ s , σ ∣ h ∣ Γ ⇓𝓢-each μ′

    infix 0 _,_⇓𝓢_

    data _,_⇓𝓢_ : Statement → Memory → Memory → Set where
      ⇓𝓢-skip : ∀ {μ} →
                  --------------
                  skip , μ ⇓𝓢 μ
      ⇓𝓢-︔    : ∀ {s₁ s₂ μ μ″ μ′} →
                s₁ , μ  ⇓𝓢 μ″ →
                s₂ , μ″ ⇓𝓢 μ′ →
                ----------------
                s₁ ︔ s₂ , μ ⇓𝓢 μ′
      ⇓𝓢-≔₁  : ∀ {x e os σ h Γ} →
                e , σ ⇓𝓔 os →
                ---------------------------------------------
                x ≔₁ e , σ ∣ h ∣ Γ ⇓𝓢 σ ⟪ x ↦ « os » ⟫ ∣ h ∣ Γ
      ⇓𝓢-≔₂  : ∀ {x e f o σ h Γ} →
                e , σ ⇓𝓔 FSets.[ o ] →
                ⦃ o∈dom·h : o FSets.∈ dom h ⦄ →
                ⦃ f∈dom·h·o : f FSets.∈ dom (h · ‹ o ›) ⦄ →
                -------------------------------------------------------------------------
                x ≔₂ e ﹒ f , σ ∣ h ∣ Γ ⇓𝓢 σ ⟪ x ↦ h · ‹ o › · ‹ f › ⦃ f∈dom·h·o ⦄ ⟫ ∣ h ∣ Γ
      ⇓𝓢-≔₃  : ∀ {x c σ h Γ o′} →
                o′ fresh σ ∣ h ∣ Γ →
              -----------------------------------------------------------------------------------------------------------------------------------
                x ≔₃ new c , σ ∣ h ∣ Γ ⇓𝓢 σ ⟪ x ↦ « FSets.[ o′ ] » ⟫ ∣ h ⟪ o′ ↦ ⊙ ⟪ class-fields c ∥ (λ f → Element.value f ↦ ⏚) ⟫ ⟫ ∣ Γ ⟪ o′ ↦ c ⟫
      ⇓𝓢-≔₄  : ∀ {e₁ f e₂ o os σ h h′ Γ} →
                  e₁ , σ ⇓𝓔 FSets.[ o ] →
                  ⦃ o∈dom·h : o FSets.∈ dom h ⦄ →
                  e₂ , σ ⇓𝓔 os →
                  ⦃ f∈dom·h·o : f FSets.∈ dom (h · ‹ o ›) ⦄ →
                  h′ ≅ h ⟪ o ↦ h · ‹ o › ⟪ f ↦ « os » ⟫  ⟫           if containment f ≡ ↝
                    ∣ disown os h ⟪ o ↦ h · ‹ o › ⟪ f ↦ « os » ⟫ ⟫   otherwise →
                -------------------------------------------------------------------------
                  e₁ ﹒ f ≔₄ e₂ , σ ∣ h ∣ Γ ⇓𝓢 σ ∣ h′ ∣ Γ
      ⇓𝓢-if₁  : ∀ {b s₁ s₂ σ h Γ μ′} →
                b , σ ⇓𝓑 true →
                s₁ , σ ∣ h ∣ Γ ⇓𝓢 μ′ →
                --------------------------------------
                if b then s₁ else s₂ , σ ∣ h ∣ Γ ⇓𝓢 μ′
      ⇓𝓢-if₂  : ∀ {b s₁ s₂ σ h Γ μ′} →
                b , σ ⇓𝓑 false →
                s₂ , σ ∣ h ∣ Γ ⇓𝓢 μ′ →
                -------------------------------------
                if b then s₁ else s₂ , σ ∣ h ∣ Γ ⇓𝓢 μ′
      ⇓𝓢-foreach : ∀ {x me s os μ μ′} →
                  me , μ ⇓𝓜 os →
                  x ↤ os ⊢ s , μ ⇓𝓢-each μ′ →
                  --------------------------------------
                  foreach x inn me do s , μ ⇓𝓢 μ′
      ⇓𝓢-fix₁    : ∀ {e s σ h Γ os σ′ h′ Γ′ os′} →
                  e , σ ⇓𝓔 os →
                  s , σ ∣ h ∣ Γ ⇓𝓢 σ′ ∣ h′ ∣ Γ′ →
                  e , σ′ ⇓𝓔 os′ →
                  os FSets.≈ os′ →
                  ------------------------------------
                  fix e do s , σ ∣ h ∣ Γ ⇓𝓢 σ′ ∣ h′ ∣ Γ′
      ⇓𝓢-fix₂    : ∀ {e s σ h Γ os σ′ h′ Γ′ σ″ h″ Γ″ os″} →
                    e , σ ⇓𝓔 os →
                    s , σ ∣ h ∣ Γ ⇓𝓢 σ″ ∣ h″ ∣ Γ″ →
                    e , σ″ ⇓𝓔 os″ →
                    os FSets.≉ os″ →
                    fix e do s , σ″ ∣ h″ ∣ Γ″ ⇓𝓢 σ′ ∣ h′ ∣ Γ′ →
                    ------------------------------------------
                    fix e do s , σ ∣ h ∣ Γ ⇓𝓢 σ′ ∣ h′ ∣ Γ′


  open IsWellformed

  .𝓔-instance·validity : ∀ {e os} σ h Γ → ValidStore (σ ∣ h ∣ Γ) → e , σ ⇓𝓔 os → os FSets.⊆ dom h
  𝓔-instance·validity σ h Γ σ-valid (⇓𝓔-var σ·x≡os) = σ-valid σ·x≡os
  𝓔-instance·validity σ h Γ σ-valid ⇓𝓔-∅    =  FSets.∅-least {as = dom h}
  𝓔-instance·validity σ h Γ σ-valid (⇓𝓔-∪ {os₁ = os₁} {os₂ = os₂} 𝓔₁ 𝓔₂) =
     FSets.∪-⊆ os₁ os₂ (dom h) (𝓔-instance·validity σ h Γ σ-valid 𝓔₁) (𝓔-instance·validity σ h Γ σ-valid 𝓔₂)
  𝓔-instance·validity σ h Γ σ-valid (⇓𝓔-∩ {os₁ = os₁} {os₂ = os₂} 𝓔₁ 𝓔₂) =
     FSets.∩-⊆₁ os₁ os₂ (dom h) (𝓔-instance·validity σ h Γ σ-valid 𝓔₁)
  𝓔-instance·validity σ h Γ σ-valid (⇓𝓔-∖ {os₁ = os₁} {os₂ = os₂} 𝓔₁ 𝓔₂) =
     FSets.∖-⊆ os₁ os₂ (dom h) (𝓔-instance·validity σ h Γ σ-valid 𝓔₁)

  .store-update-validity : ∀ x os σ h Γ → (σ-valid : ValidStore (σ ∣ h ∣ Γ)) → os FSets.⊆ dom h → ValidStore (σ ⟪ x ↦ « os » ⟫ ∣ h ∣ Γ)
  store-update-validity x os σ h Γ σ-valid os⊆dom·h {y} {os′} σ⟪x↦os⟫·y≡os′ «os′» rewrite (update-lookup₁ σ x « os ») = {!p!}
    where open PartialFunctions
          open _⇀_ σ

  .𝓢-wellformedness·preservation : ∀ {s μ μ′} → IsWellformed μ → s , μ ⇓𝓢 μ′ → IsWellformed μ′
  𝓢-wellformedness·preservation μ-wf ⇓𝓢-skip = μ-wf
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-︔ 𝓢₁ 𝓢₂) = 𝓢-wellformedness·preservation (𝓢-wellformedness·preservation μ-wf 𝓢₁) 𝓢₂
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-≔₁ {x = x} {e = e} {os = os} {σ = σ} {h = h} {Γ = Γ} 𝓔) = record
                                                  { store-valid = {!!} -- store-update-validity x os σ h Γ (store-valid {σ ∣ h ∣ Γ} μ-wf) (𝓔-instance·validity {e} {os} σ h Γ (store-valid {σ ∣ h ∣ Γ} μ-wf) 𝓔)
                                                  ; heap-instances-typed = heap-instances-typed μ-wf
                                                  ; heap-links-valid = heap-links-valid μ-wf
                                                  ; heap-links-complete = heap-links-complete μ-wf
                                                  ; heap-links-typed = heap-links-typed μ-wf
                                                  ; containment-acyclic = containment-acyclic μ-wf
                                                  ; containment-unique-inst = λ {o o′ o″} → containment-unique-inst μ-wf {o} {o′} {o″}
                                                  ; containment-unique-field = λ {o o′} → containment-unique-field μ-wf {o} {o′}
                                                  }
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-≔₂ x₁) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-≔₃ x₁) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-≔₄ x x₁ x₂) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-if₁ x 𝓢) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-if₂ x 𝓢) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-foreach x₁ x₂) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-fix₁ x 𝓢 x₁ x₂) = {!!}
  𝓢-wellformedness·preservation μ-wf (⇓𝓢-fix₂ x 𝓢 x₁ x₂ 𝓢₁) = {!!}
