module TRON.Syntax where

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (_∨_ to _lor_; _∧_ to _land_; if_then_else_ to 𝔹-elim)
open import Data.String
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.All
open import Data.Product
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
module Elem = Membership-≡

module Static where
  record Class : Set where
    constructor _class
    field
      name : String

  record Field : Set where
    constructor _f
    field
      name : String

  data Containment : Set where
    ✦ ↝ : Containment

  record RawStructure : Set₁ where
    field
      classes : List Class
      fields : List Field
      _ref⟨_⟩_ : (c : Class) ⦃ c∈classes : c Elem.∈ classes ⦄ → (cnt : Containment) → (f : Field) → ⦃ f∈fields : f Elem.∈ fields ⦄ → Set
      _gen_  : ∀ c ⦃ c∈classes : c Elem.∈ classes ⦄ c′ ⦃ c′∈classes : c′ Elem.∈ classes ⦄ → Set

    data _gen⋆_ (c : Class) ⦃ c∈classes : c Elem.∈ classes ⦄ : (c′ : Class) ⦃ c′∈classes : c′ Elem.∈ classes ⦄  → Set where
      instance
        [] : c gen⋆ c
        _∷_ : ∀ {c′} ⦃ c′∈classes : c′ Elem.∈ classes ⦄ c″ ⦃ c″∈classes : c″ Elem.∈ classes ⦄ → c gen c″ → c″ gen⋆ c′ → c gen⋆ c′

  record Structure : Set₁ where
    field
      rawStructure : RawStructure
    open RawStructure rawStructure public
    field
      .classes-set      : ∀ c → (c∈classes₁ : c Elem.∈ classes) (c∈classes₂ : c Elem.∈ classes) → c∈classes₁ ≡ c∈classes₂
      .fields-set       : ∀ f → (f∈fields₁ : f Elem.∈ fields) (f∈fields₂ : f Elem.∈ fields) → f∈fields₁ ≡ f∈fields₂
      .gen-acyclic      : ∀ c ⦃ c∈classes : c Elem.∈ classes ⦄ c′ ⦃ c′∈classes : c′ Elem.∈ classes ⦄ → c gen⋆ c′ → c′ gen⋆ c → ⊥
      .ref-gen          : ∀ c c′ ⦃ c∈classes : c Elem.∈ classes ⦄ ⦃ c′∈classes : c′ Elem.∈ classes ⦄ cnt f ⦃ f∈fields : f Elem.∈ fields ⦄ →
                          c gen⋆ c′ → c′ ref⟨ cnt ⟩ f → c ref⟨ cnt ⟩ f
      .ref-cnt-disjoint : ∀ c ⦃ c∈classes : c Elem.∈ classes ⦄ f ⦃ f∈fields : f Elem.∈ fields ⦄ → c ref⟨ ✦ ⟩ f → c ref⟨ ↝ ⟩ f → ⊥

module Dynamic (structure : Static.Structure) where
  open Static
  open Structure structure

  record Var : Set where
    constructor _v
    field
      name : String

  data SetExpr : Set where
    ‹_› : (var : String) → SetExpr
    ∅   : SetExpr
    _∪_ _∩_ _∖_ : (e₁ e₂ : SetExpr) → SetExpr

  data BoolExpr : Set where
    _⊆_ _⊈_ : (e₁ e₂ : SetExpr) → BoolExpr
    _∨_ _∧_  : (b₁ b₂ : BoolExpr) → BoolExpr

  infix 6 _⊆_ _⊈_ _≃_ _≄_
  infixl 4 _∧_
  infixl 2 _∨_

  _≃_ _≄_ : (e₁ e₂ : SetExpr) → BoolExpr
  e₁ ≃ e₂ = e₁ ⊆ e₂ ∧ e₂ ⊆ e₁
  e₁ ≄ e₂ = e₁ ⊈ e₂ ∨ e₂ ⊈ e₁

  data MatchExpr : Set where
    ⌈_⌉     : (e : SetExpr) → MatchExpr
    _match_ _match⋆_ : (e : SetExpr) (c : Class) ⦃ c∈classes : c Elem.∈ classes ⦄ → MatchExpr

  -- Purely for syntax
  record New : Set where
    constructor new_
    field
      class : Class
      ⦃ class∈classes ⦄ : class Elem.∈ classes

  data Statement : Set where
    skip          : Statement
    _︔_            : (s₁ s₂ : Statement) → Statement
    _≔₁_          : (var : Var) (e : SetExpr) → Statement
    _≔₂_﹒_         : (var : Var) (e : SetExpr) (f : Field) ⦃ f∈fields : f Elem.∈ fields ⦄ → Statement
    _≔₃_          : (var : Var) (en : New) → Statement
    _﹒_≔₄_         : (e₁ : SetExpr) (f : Field) ⦃ f∈fields : f Elem.∈ fields ⦄ (e₂ : SetExpr) → Statement
    if_then_else_ : (b : BoolExpr) (s₁ s₂ : Statement) → Statement
    foreach_∈_do_ : (var : Var) (me : MatchExpr) (s : Statement) → Statement
    fix_do_       : (e : SetExpr) (s : Statement) → Statement
