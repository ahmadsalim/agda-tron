module TRON.Syntax where

import Level
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (_∨_ to _lor_; _∧_ to _land_; if_then_else_ to 𝔹-elim)
open import Data.String
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Util

module Static where
  record Class : Set where
    constructor _cls
    field
      name : String

  record Field : Set where
    constructor _fld
    field
      name : String

  data Containment : Set where
    ✦ ↝ : Containment

  record RawStructure : Set₁ where
    field
      classes : FSet Class
      fields : FSet Field
      ref    : (c : FSet.Element classes) (f : FSet.Element fields) → FSet.Element classes × Containment
      _gen_  : ∀ (c c′ : FSet.Element classes) → Set

    _gen⋆_ : (c c′ : FSet.Element classes) → Set
    c gen⋆ c′ = c Closures.⟨ _gen_ ⟩* c′

  record Structure : Set₁ where
    field
      rawStructure : RawStructure
    open RawStructure rawStructure public
    field
      .gen-acyclic      : ∀ c c′ → c gen⋆ c′ → c′ gen⋆ c → ⊥
      .ref-gen          : ∀ c c′ c″ cnt f → c gen⋆ c′ → ref c′ f ≡ (c″ , cnt) → ref c f ≡ (c″ , cnt)

module Dynamic (structure : Static.Structure) where
  open Static
  open Structure structure

  record Var : Set where
    constructor _var
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
    _match_ _match⋆_ : (e : SetExpr) (c : FSet.Element classes) → MatchExpr

  -- Purely for syntax
  record New : Set where
    constructor new_
    field
      class : FSet.Element classes

  data Statement : Set where
    skip          : Statement
    _︔_            : (s₁ s₂ : Statement) → Statement
    _≔₁_          : (var : Var) (e : SetExpr) → Statement
    _≔₂_﹒_         : (var : Var) (e : SetExpr) (f : FSet.Element fields) → Statement
    _≔₃_          : (var : Var) (en : New) → Statement
    _﹒_≔₄_         : (e₁ : SetExpr) (f : FSet.Element fields) (e₂ : SetExpr) → Statement
    if_then_else_ : (b : BoolExpr) (s₁ s₂ : Statement) → Statement
    foreach_∈_do_ : (var : Var) (me : MatchExpr) (s : Statement) → Statement
    fix_do_       : (e : SetExpr) (s : Statement) → Statement
