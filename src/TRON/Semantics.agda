module TRON.Semantics where

import Level

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool as Bool hiding (_∧_; _∨_) renaming (Bool to 𝔹; _≟_ to _≟B_)
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

module PartialFunctions where
  infixr 2 _⇀_
  record _⇀_ {α} {β} (A : Set α) (B : Set β) : Set (α Level.⊔ β) where
    constructor lift
    infixl 6 _·_
    field
      dom : FSet A
      _·_ : FSet.Element dom → B
  open _⇀_ public

  ⊙ : ∀{α β} {A : Set α} {B : Set β} → A ⇀ B
  ⊙ = lift FSets.∅ (λ { (FSet.Element.‹ a › ⦃ a∈∅ ⦄) → ⊥-elim-irr (FSets.∅-empty a∈∅) })

  infix 1 _↦_
  _↦_ : ∀ {α β} {A : Set α} {B : Set β} → A → B → A × B
  _↦_ = _,_

  infix 2 _⟪_⟫

  _⟪_⟫ : ∀ {α β} {A : Set α} ⦃ decEqA : DecEq A ⦄ {B : Set β} (f : A ⇀ B) (upd : A × B) → A ⇀ B
  _⟪_⟫ {B = B} (lift dom _·_) (arg , newval) = lift (dom FSets.◀ arg) _·′_
    where _·′_ : FSet.Element (dom FSets.◀ arg) → B
          _·′_ el with (FSet.Element.value el ≟ arg)
          _·′_ el | yes valel≡arg = newval
          _·′_ el | no  valel≢arg with (FSets.◀-exact arg dom el)
          _·′_ el | no  valel≢arg | inj₁ el′ = _·_ el′
          _·′_ el | no  valel≢arg | inj₂ valel≡arg = ⊥-elim (valel≢arg valel≡arg)

  infix 2 _⟪_∥_⟫

  _⟪_∥_⟫ : ∀ {α β γ} {A : Set α} {B : Set β}  ⦃ decEqB : DecEq B ⦄  {C : Set γ} (f : B ⇀ C)  (as : FSet A) (upd : FSet.Element as → B × C) → B ⇀ C
  f ⟪ as ∥ upd ⟫ = FSets.fold as f (λ a _ _ _ f′ → f′ ⟪ proj₁ (upd a) ↦ proj₂ (upd a) ⟫)


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

  record IsWellformed (μ : Memory) : Set₁ where
    open Memory μ public
    field
      stack-valid          : ∀ {x os} → σ · x ≡ « os » → os FSets.⊆ dom h
      heap-instances-typed : dom h FSets.≈ dom Γ
      heap-links-valid     : ∀ {o f os} → h · o · f ≡ « os » → os FSets.⊆ dom h

    domh⊆domΓ : dom h FSets.⊆ dom Γ
    domh⊆domΓ = proj₁ heap-instances-typed

    domΓ⊆domh : dom Γ FSets.⊆ dom h
    domΓ⊆domh = proj₂ heap-instances-typed

    field
      heap-links-complete  : ∀ {c} {o : Element (dom h)} →
                               Γ · (FSets.coe domh⊆domΓ o) ≡ c →
                               dom (h · o) FSets.≈ class-fields c
      heap-links-typed     : ∀ {c} {o : Element (dom h)} {f c′ os}
                              → Γ · (FSets.coe domh⊆domΓ o) ≡ c → ref c f ≡ c′
                              → Σ-inst (Element.value f FSets.∈ dom (h · o)) -- f is instantiated
                                  (∀ (h·o·f≡os : h · o · ‹ Element.value f › ≡ « os ») (o′ : Element os) -- all elements have a type which is a subset of the expected one
                                       → (Γ · FSets.coe (FSets.⊆-trans {ys = dom Γ} (heap-links-valid h·o·f≡os) domh⊆domΓ) o′) gen⋆ c′)

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
              o′ fresh (σ ∣ h ∣ Γ) →
             -----------------------------------------------------------------------------------------------------------------------------------
              x ≔₃ new c , σ ∣ h ∣ Γ ⇓𝓢 σ ⟪ x ↦ « FSets.[ o′ ] » ⟫ ∣ h ⟪ o′ ↦ ⊙ ⟪ class-fields c ∥ (λ f → Element.value f ↦ ⏚) ⟫ ⟫ ∣ Γ ⟪ o′ ↦ c ⟫
