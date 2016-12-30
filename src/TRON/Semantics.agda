module TRON.Semantics where

import Level

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool as Bool hiding (_∧_; _∨_) renaming (Bool to 𝔹; _≟_ to _≟B_)
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product
open import Data.Sum as Sum
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.String renaming (_≟_ to _≟S_)

open import Relation.Nullary
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

  _[_↦_] : ∀ {α β} {A : Set α} ⦃ decEqA : DecEq A ⦄ {B : Set β} (f : A ⇀ B) (arg : A) (newval : B) → (A ⇀ B)
  _[_↦_] {B = B} (lift dom _·_) arg newval = lift (dom FSets.◀ arg) _·′_
    where _·′_ : FSet.Element (dom FSets.◀ arg) → B
          _·′_ el with (FSet.Element.value el ≟ arg)
          _·′_ el | yes valel≡arg = newval
          _·′_ el | no  valel≢arg with (FSets.◀-exact arg dom el)
          _·′_ el | no  valel≢arg | inj₁ el′ = _·_ el′
          _·′_ el | no  valel≢arg | inj₂ valel≡arg = ⊥-elim (valel≢arg valel≡arg)

module Concrete (structure : Static.Structure) where
  open Static
  open Structure structure
  open Dynamic structure
  open PartialFunctions
  open FSet

  record Instance : Set where
    constructor mk-inst
    field
      value : ℕ

  -- TODO Move
  instance
    decEqℕ : DecEq ℕ
    decEqℕ = record { _≟_ = _≟ℕ_ }

  instance
    decEqInstance : DecEq Instance
    decEqInstance = record { _≟_ = _≟I_ }
      where _≟I_ : (x y : Instance) → Dec (x ≡ y)
            mk-inst x ≟I mk-inst y with (x ≟ y)
            mk-inst x ≟I mk-inst .x | yes refl = yes refl
            mk-inst x ≟I mk-inst y  | no  x≢y  = no (λ mk-instx≢mk-insty → x≢y (mk-inst-inj mk-instx≢mk-insty))
              where mk-inst-inj : ∀ {x y} → mk-inst x ≡ mk-inst y → x ≡ y
                    mk-inst-inj refl = refl

  instance
    decEqString : DecEq String
    decEqString = record { _≟_ = _≟S_ }

  Store : Set
  Store = Var ⇀ FSet Instance

  Heap : Set
  Heap = Instance ⇀ FSet.Element fields ⇀ FSet Instance

  TypeEnv : Set
  TypeEnv = Instance ⇀ FSet.Element classes

  record Memory : Set where
    constructor _∣_∣_
    field
      σ : Store
      h : Heap
      Γ : TypeEnv

  record IsWellformed (μ : Memory) : Set₁ where
    open Memory μ public
    field
      stack-valid          : ∀ {x} → σ · x FSets.⊆ dom h
      heap-instances-typed : dom h FSets.≈ dom Γ
      heap-links-valid     : ∀ {o f} → h · o · f FSets.⊆ dom h

    domh⊆domΓ : dom h FSets.⊆ dom Γ
    domh⊆domΓ = proj₁ heap-instances-typed

    domΓ⊆domh : dom Γ FSets.⊆ dom h
    domΓ⊆domh = proj₂ heap-instances-typed

    field
      heap-links-typed     : ∀ c (o : Element (dom h)) cnt f c′
                              → Γ · (FSets.coe domh⊆domΓ o) ≡ c → ref c f ≡ (c′ , cnt)
                              → Σ-inst (f FSets.∈ dom (h · o)) -- f is instantiated
                                  (∀ (o′ : Element (h · o · ‹ f ›)) -- all elements have a type which is a subset of the expected one
                                      → (Γ · FSets.coe (FSets.⊆-trans {ys = dom Γ} heap-links-valid domh⊆domΓ) o′) gen⋆ c′)

    private
      contains : Element (dom h) → Element (dom h) → Set
      contains o o′ = Σ[ f ∈ Element (dom (h · o)) ] (proj₂ (ref (Γ · FSets.coe domh⊆domΓ o) (Element.value f)) ≡ ✦ × (Element.value o′ FSets.∈ (h · o · f)))

      contains⋆ : Element (dom h) → Element (dom h) → Set
      contains⋆ o o′ = o Closures.⟨ contains ⟩* o′

    field
      containment-acyclic       : ∀ {o o′} → contains⋆ o o′ → contains⋆ o′ o → ⊥
      containment-unique-inst   : ∀ {o o′ o″} → contains o′ o → contains o″ o → o′ ≡ o″
      containment-unique-field  : ∀ {o o′} → (o′-c-o₁ o′-c-o₂ : contains o′ o) → proj₁ o′-c-o₁ ≡ proj₁ o′-c-o₂

    _contains_ _contains⋆_ : Element (dom h) → Element (dom h) → Set -- Due to Agda bug
    _contains_ = contains
    _contains⋆_ = contains⋆

  module _ where
    open RawMonad {Level.zero} Maybe.monad

    infix 0 _,_⇓𝓔_

    data _,_⇓𝓔_ : SetExpr → Store → FSet Instance → Set where
      ⇓𝓔-var : ∀ {var σ} →
               ⦃ var∈dom·σ : var FSets.∈ dom σ ⦄ →
               ------------------------------------
               ‹ var › , σ ⇓𝓔 σ · ‹ var ›

      ⇓𝓔-∅   : ∀ {σ} →
               --------------------
                ∅ , σ ⇓𝓔 FSets.∅

      ⇓𝓔-∪   : ∀ {e₁ e₂ σ os₁ os₂} →
                e₁ , σ ⇓𝓔 os₁ →
                e₂ , σ ⇓𝓔 os₂ →
               ---------------------
                e₁ ∪ e₂ , σ ⇓𝓔 os₁ FSets.∪ os₂

      ⇓𝓔-∩   : ∀ {e₁ e₂ σ os₁ os₂} →
                e₁ , σ ⇓𝓔 os₁ →
                e₂ , σ ⇓𝓔 os₂ →
                ---------------------
                e₁ ∩ e₂ , σ ⇓𝓔 os₁ FSets.∩ os₂

      ⇓𝓔-∖   : ∀ {e₁ e₂ σ os₁ os₂} →
                e₁ , σ ⇓𝓔 os₁ →
                e₂ , σ ⇓𝓔 os₂ →
                ---------------------
                e₁ ∖ e₂ , σ ⇓𝓔 os₁ FSets.∖ os₂


    infix 0 _,_⇓𝓑_

    data _,_⇓𝓑_ : BoolExpr → Store → 𝔹 → Set where
      ⇓𝓑-⊆ : ∀ {e₁ e₂ σ os₁ os₂} →
               e₁ , σ ⇓𝓔 os₁ →
               e₂ , σ ⇓𝓔 os₂ →
               os₁ FSets.⊆ os₂ →
               e₁ ⊆ e₂ , σ ⇓𝓑 {!!}

    {-

    𝓑⟦_⟧ : BoolExpr → Store → Maybe 𝔹
    𝓑⟦ e₁ Dynamic.⊆ e₂ ⟧ σ = {!!}
    𝓑⟦ e₁ Dynamic.⊈ e₂ ⟧ σ = {!!}
    𝓑⟦ b₁ Dynamic.∨ b₂ ⟧ σ = 𝓑⟦ b₁ ⟧ σ >>= λ t₁ →
                             𝓑⟦ b₂ ⟧ σ >>= λ t₂ →
                              return (t₁ Bool.∧ t₂)
    𝓑⟦ b₁ Dynamic.∧ b₂ ⟧ σ = {!!}
    -}
