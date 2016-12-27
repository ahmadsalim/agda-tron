module TRON.Semantics where

import Level

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Util
open import TRON.Syntax

infixr 2 _⇀_

record _⇀_ {α} {β} (A : Set α) (B : Set β) : Set (α Level.⊔ β) where
  constructor lift
  infixl 6 _·_
  field
    dom : FSet A
    _·_ : FSet.Element dom → B

module Concrete (structure : Static.Structure) where
  open Static
  open Structure structure
  open Dynamic structure
  open _⇀_
  open FSet

  record Instance : Set where
    constructor mk-inst
    field
      value : ℕ

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
