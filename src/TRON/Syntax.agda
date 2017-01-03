module TRON.Syntax where

import Level
open import Data.Unit
open import Data.Empty
open import Data.Bool renaming (_∨_ to _lor_; _∧_ to _land_; if_then_else_ to 𝔹-elim)
open import Data.String
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Util

module Static where
  Class = String
  Field = String

  data Containment : Set where
    ✦ ↝ : Containment

  instance
    deceq-containment : DecEq Containment
    deceq-containment = record { _≟_ = _≟C_ }
      where _≟C_ : (cnt₁ cnt₂ : Containment) → Dec (cnt₁ ≡ cnt₂)
            ✦ ≟C ✦ = yes refl
            ✦ ≟C ↝ = no (λ ())
            ↝ ≟C ✦ = no (λ ())
            ↝ ≟C ↝ = yes refl

  record RawStructure : Set₁ where
    field
      classes      : FSet Class
      fields       : FSet Field
      class-fields : FSet.Element classes → FSet (FSet.Element fields)
      ref          : (c : FSet.Element classes) (f : FSet.Element (class-fields c)) → FSet.Element classes
      containment  : (f : FSet.Element fields) → Containment
      _gen_        : ∀ (c c′ : FSet.Element classes) → Set
      _?gen_       : ∀ (c c′ : FSet.Element classes) → Dec (c gen c′)

    _gen⋆_ : (c c′ : FSet.Element classes) → Set
    c gen⋆ c′ = c Closures.⟨ _gen_ ⟩* c′

    open FSets

    _?gen⋆_ : (c c′ : FSet.Element classes) → Dec (c gen⋆ c′)
    c ?gen⋆ c′ = c Closures.?⟨ _?gen_ ⟩* c′

  record Structure : Set₁ where
    field
      rawStructure : RawStructure
    open RawStructure rawStructure public
    field
      .gen-acyclic        : ∀ {c c′} → c gen⋆ c′ → c′ gen⋆ c → ⊥
      .class-fields-gen   : ∀ {c c′ f} → c gen⋆ c′ → f FSets.∈ class-fields c′ → f FSets.∈ class-fields c
      .ref-gen            : ∀ {c c′ c″ f} → (c<:c′ : c gen⋆ c′) → ref c′ f ≡ c″ → ref c (FSet.‹ FSet.Element.value f › ⦃ class-fields-gen c<:c′ (FSet.Element.value∈elements f) ⦄) ≡ c″

module Dynamic (structure : Static.Structure) where
  open Static
  open Structure structure

  Var = String

  data SetExpr : Set where
    ‹_› : (var : Var) → SetExpr
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

  infix 4 _≔₁_ _≔₂_﹒_ _≔₃_ _﹒_≔₄_

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
