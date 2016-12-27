module Util where

import Level
open import Data.Empty
open import Data.Product
open import Data.List as List hiding ([_])
open import Data.List.Any as Any

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq


Σ-inst : ∀ {α π} (A : Set α) → (P : ⦃ a : A ⦄ → Set π) → Set (α Level.⊔ π)
Σ-inst A P = Σ[ a ∈ A ] P ⦃ a ⦄

private
  there-injective : ∀ {α} {π} {A : Set α} {x : A} {P : A → Set π} {xs : List A} {x-any y-any : Any P xs} → there {x = x} x-any ≡ there y-any → x-any ≡ y-any
  there-injective refl = refl

module Closures where
  data _⟨_⟩⁇_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []   : x ⟨ _r_ ⟩⁇ x
    [_] : ∀ {y : A} → x r y → x ⟨ _r_ ⟩⁇ y

  data _⟨_⟩*_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []  : x ⟨ _r_ ⟩* x
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩* z

  data _⟨_⟩⁺_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩⁺ z

record FSet {α} (A : Set α) : Set α where
  constructor mk-set

  private
    module Memb = Membership (PropEq.setoid A)

  field
    elements : List A
    .elements-set : ∀ {e} (e∈elements₁ e∈elements₂ : e Memb.∈ elements) → e∈elements₁ ≡ e∈elements₂

  record Element : Set α where
    constructor ‹_›
    field
      value : A
      ⦃ value∈elements ⦄ : value Memb.∈ elements

record DecEq {α} (A : Set α) : Set (Level.suc α) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
open DecEq ⦃ ... ⦄

module FSets where
  open FSet

  fromList : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ → List A → FSet A
  fromList [] = mk-set [] (λ ())
  fromList (x ∷ xs) with (fromList xs)
  fromList (x ∷ xs) | mk-set elements elements-set with (Any.any (x ≟_) elements)
  fromList (x ∷ xs) | mk-set elements elements-set | yes x∈elements = mk-set elements elements-set
  fromList {A = A} (x ∷ xs) | mk-set elements elements-set | no ¬x∈elements = mk-set (x ∷ elements) x∷elements-set
    where module AMemb = Membership (PropEq.setoid A)
          .x∷elements-set : ∀ {y : A} (y∈x∷elements₁ y∈x∷elements₂ : y AMemb.∈ x ∷ elements) → y∈x∷elements₁ ≡ y∈x∷elements₂
          x∷elements-set (here refl) (here refl) = refl
          x∷elements-set (here refl) (there x∈elements₂) = ⊥-elim (¬x∈elements x∈elements₂)
          x∷elements-set (there x∈elements₁) (here refl) = ⊥-elim (¬x∈elements x∈elements₁)
          x∷elements-set (there y∈elements₁) (there y∈elements₂) = cong there (elements-set y∈elements₁ y∈elements₂)

  toList : ∀ {α} {A : Set α} → FSet A → List A
  toList = elements

  quot-map : ∀ {α β} {A : Set α} {B : Set β}  ⦃ decEqB : DecEq B ⦄ → (A → B) → FSet A → FSet B
  quot-map {α} {β} {A} {B} ⦃ decEqB ⦄ f (mk-set elements elements-set) = fromList (List.map f elements)

  _∈_ : ∀ {α} {A : Set α} → A → FSet A → Set α
  _∈_ {A = A} a as = a AMemb.∈ elements as
    where module AMemb = Membership (PropEq.setoid A)

  infix 4 _⊆_ _≈_
  _⊆_ _≈_ : ∀ {α} {A : Set α} → FSet A → FSet A → Set α
  as ⊆ as′ = ∀ (a : FSet.Element as) → Element.value a ∈ as′
  as ≈ as′ = as ⊆ as′ × as′ ⊆ as

  coe : ∀ {α} {A : Set α} {as as′ : FSet A} → as ⊆ as′ → Element as → Element as′
  coe as⊆as′ a = ‹ Element.value a › ⦃ as⊆as′ a ⦄

  ⊆-refl : ∀ {α} {A : Set α} {xs : FSet A} → xs ⊆ xs
  ⊆-refl = λ a → Element.value∈elements a

  ⊆-trans : ∀ {α} {A : Set α} {xs ys zs : FSet A} → xs ⊆ zs → zs ⊆ ys → xs ⊆ ys
  ⊆-trans xs⊆zs zs⊆ys = λ a → zs⊆ys (coe xs⊆zs a)

  ≈-refl : ∀ {α} {A : Set α} {xs : FSet A} → xs ≈ xs
  ≈-refl = ⊆-refl , ⊆-refl

  ≈-sym  : ∀ {α} {A : Set α} {xs ys : FSet A} → xs ≈ ys → ys ≈ xs
  ≈-sym (xs⊆ys , ys⊆xs) = ys⊆xs , xs⊆ys

  ≈-trans : ∀ {α} {A : Set α} {xs ys zs : FSet A} → xs ≈ zs → zs ≈ ys → xs ≈ ys
  ≈-trans {xs = xs} {ys = ys} {zs = zs} (xs⊆zs , zs⊆xs) (zs⊆ys , ys⊆zs) =
    ⊆-trans {ys = ys} xs⊆zs zs⊆ys , ⊆-trans {ys = xs} ys⊆zs zs⊆xs
