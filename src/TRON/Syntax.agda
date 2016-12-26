module TRON.Syntax where

open import Level
open import Data.Unit
open import Data.Bool renaming (_∨_ to _lor_; _∧_ to _land_; if_then_else_ to 𝔹-elim)
open import Data.String
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.All
open import Data.Product
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
module Elem = Membership-≡

-- Static

record Class : Set where
  constructor _class
  field
    name : String

record Field : Set where
  constructor _f
  field
    name : String

data Ownership : Set where
  ✦ : Ownership
  ↝ : Ownership

private -- TODO move to some better lace
  map-compose : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {f : B → C} {g : A → B} (xs : List A) →
    List.map f (List.map g xs) ≡ List.map (λ x → f (g x)) xs
  map-compose [] = refl
  map-compose {f = f} {g = g} (x ∷ xs) rewrite (map-compose {f = f} {g = g} xs) = refl

  zip-∈ : ∀ {α} {A : Set α} (xs : List A) → Σ[ ys ∈ (List (Σ[ x ∈ A ] (x Elem.∈ xs))) ] (xs ≡ List.map proj₁ ys)
  zip-∈ [] = [] , refl
  zip-∈ (x ∷ xs) with (zip-∈ xs)
  zip-∈ {α} (x ∷ xs) | xs-∈ , xs-∈≡xs = (x , here refl) ∷ List.map (λ { (y , y∈xs) → y , there y∈xs }) xs-∈ ,
    cong (λ xs → x ∷ xs) (trans xs-∈≡xs (sym (map-compose xs-∈)))

record Structure : Set₁ where
  constructor structure
  field
    classes : List Class
    fields : List Field
    _ref⟨_⟩_ : Class → Ownership → Field → Bool
    _gen_  : ∀ c c′ ⦃ c∈classes : c Elem.∈ classes ⦄ ⦃ c′∈classes : c′ Elem.∈ classes ⦄ → Set

  data _gen⋆_ (c : Class) : (c′ : Class) → Set where
    instance
      [] : ⦃ c∈classes : c Elem.∈ classes ⦄ → c gen⋆ c
      _∷_ : ∀ {c′ c″} ⦃ c∈classes : c Elem.∈ classes ⦄ ⦃ c″∈classes : c″ Elem.∈ classes ⦄ → c gen c″ → c″ gen⋆ c′ → c gen⋆ c′

IsUnique : ∀ {α} {A : Set α} → List A → Set α
IsUnique xs = IsUnique′ [] xs
  where IsUnique′ : ∀ {α} {A : Set α} → List A → List A → Set α
        IsUnique′ xs [] = Lift ⊤
        IsUnique′ xs (y ∷ ys) = y Elem.∉ xs × IsUnique′ (y ∷ xs) ys

-- Dynamic

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
  ⌈_⌉     : SetExpr → MatchExpr
  _match_ _match⋆_ : SetExpr → Class → MatchExpr

-- Purely for syntax
record New : Set where
  constructor new_
  field
    class : Class

data Statement : Set where
  skip          : Statement
  _︔_            : (s₁ s₂ : Statement) → Statement
  _≔₁_          : (var : Var) (e : SetExpr) → Statement
  _≔₂_﹒_         : (var : Var) (e : SetExpr) (f : Field) → Statement
  _≔₃_          : (var : Var) (en : New) → Statement
  _﹒_≔₄_         : (e₁ : SetExpr) (f : Field) (e₂ : SetExpr) → Statement
  if_then_else_ : (b : BoolExpr) (s₁ s₂ : Statement) → Statement
  foreach_∈_do_ : (var : Var) (me : MatchExpr) (s : Statement) → Statement
  fix_do_       : (e : SetExpr) (s : Statement) → Statement
