module Util where

import Level
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.String as String renaming (_≟_ to _≟S_) hiding (setoid; fromList; toList)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List as List hiding ([_]; map; filter)
open import Data.List.Any as Any hiding (map)
open import Data.List.All as All hiding (map)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq hiding ([_])
open import Function


infixl 0 _≅_if_∣_otherwise

_≅_if_∣_otherwise : ∀ {α π} {A : Set α} (res : A) (then : A) (cond : Set π) (else : A) → Set (α Level.⊔ π)
a ≅ a₁ if cond ∣ a₂ otherwise = cond × a ≡ a₁ ⊎ ¬ cond × a ≡ a₂


-- From effectfully on IRC
record Irr {α} (A : Set α) : Set α where
  constructor irr
  field
    .proof : A

Σ-inst : ∀ {α π} (A : Set α) → (P : ⦃ a : A ⦄ → Set π) → Set (α Level.⊔ π)
Σ-inst A P = Σ[ a ∈ A ] P ⦃ a ⦄

record DecEq {α} (A : Set α) : Set (Level.suc α) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
open DecEq ⦃ ... ⦄

instance
  decEqString : DecEq String
  decEqString = record { _≟_ = _≟S_ }

record Finite {α} (A : Set α) : Set (Level.suc α) where
  field
    inhabitants : List A
  open Membership (PropEq.setoid A)
  field
    .inhabitants-enumerate : ∀ (a : A) → a ∈ inhabitants
open Finite ⦃ ... ⦄

private
  there-injective : ∀ {α π} {A : Set α} {x : A} {P : A → Set π} {xs : List A} {x-any y-any : Any P xs} → there {x = x} x-any ≡ there y-any → x-any ≡ y-any
  there-injective refl = refl

  ∷-injective₁ : ∀ {α} {A : Set α} {a a′ : A} {as as′ : List A} → (a∷as≡a′∷as′ : _≡_ {α} {List A} (a ∷ as) (a′ ∷ as′)) → a ≡ a′
  ∷-injective₁ refl = refl

  ∷-injective₂ : ∀ {α} {A : Set α} {a a′ : A} {as as′ : List A} → (a∷as≡a′∷as′ : _≡_ {α} {List A} (a ∷ as) (a′ ∷ as′)) → as ≡ as′
  ∷-injective₂ refl = refl

  here≢there : ∀ {α π} {A : Set α} {x : A} {P : A → Set π} {xs : List A} {px : P x} {any : Any P xs} → here px ≡ there any → ⊥
  here≢there ()

module _ {α} {A : Set α} where
  open Membership (PropEq.setoid A)

  instance
    here-∈ : ∀ {x xs} → x ∈ x ∷ xs
    here-∈ = here refl

    there-∈ : ∀ {x y xs} → x ∈ xs → x ∈ y ∷ xs
    there-∈ x∈xs = there x∈xs

module Closures where
  data _⟨_⟩⁇_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []   : x ⟨ _r_ ⟩⁇ x
    [_] : ∀ {y : A} → x r y → x ⟨ _r_ ⟩⁇ y

  _?⟨_⟩⁇_ : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ (x : A) {_r_ : A → A → Set α} (_?r_ : ∀ (x y : A) → Dec (x r y)) (y : A) → Dec (x ⟨ _r_ ⟩⁇ y)
  x ?⟨ _?r_ ⟩⁇ y with (x ≟ y)
  x ?⟨ _?r_ ⟩⁇ .x | yes refl = yes []
  x ?⟨ _?r_ ⟩⁇ y  | no x≢y with (x ?r y)
  x ?⟨ _?r_ ⟩⁇ y  | no x≢y | yes xry = yes [ xry ]
  x ?⟨ _?r_ ⟩⁇ y  | no x≢y | no ¬xry = no (?-⊥ x≢y ¬xry)
    where ?-⊥ : ∀ {α} {A : Set α} {x y : A} {_r_ : A → A → Set α} → (x≢y : x ≢ y) → (¬xry : ¬ (x r y)) → (xr⁇y : x ⟨ _r_ ⟩⁇ y) → ⊥
          ?-⊥ x≢y ¬xry [] = x≢y refl
          ?-⊥ x≢y ¬xry [ xry ] = ¬xry xry

  data _⟨_⟩*_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []  : x ⟨ _r_ ⟩* x
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩* z


  data _⟨_⟩⁺_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩⁺ z

  postulate -- TODO Implement
    _?⟨_⟩*_ : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ ⦃ finiteA : Finite A ⦄ (x : A) {_r_ : A → A → Set α} (_?r_ : ∀ (x y : A) → Dec (x r y)) (y : A) → Dec (x ⟨ _r_ ⟩* y)
    _?⟨_⟩⁺_ : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ ⦃ finiteA : Finite A ⦄ (x : A) {_r_ : A → A → Set α} (_?r_ : ∀ (x y : A) → Dec (x r y)) (y : A) → Dec (x ⟨ _r_ ⟩⁺ y)

IsSet : ∀ {α} {A : Set α} (xs : List A) → Set α
IsSet {α} {A} xs = ∀ {x} (x∈xs₁ x∈xs₂ : x AMemb.∈ xs) → x∈xs₁ ≡ x∈xs₂
  where module AMemb = Membership (PropEq.setoid A)

record FSet {α} (A : Set α) : Set α where
  constructor mk-set

  private
    module Memb = Membership (PropEq.setoid A)

  field
    elements : List A
    .elements-set : IsSet elements

  record Element : Set α where
    constructor ‹_›
    field
      value : A
      .⦃ value∈elements ⦄ : value Memb.∈ elements

module FSets where
  open FSet

  private
    module _ {α} {A : Set α} where
      open Membership (PropEq.setoid A)
      .element-extend-set : ∀ {x : A} {elements : List A} (x∉elements : x ∉ elements) (elements-set : IsSet elements) →
                           IsSet (x ∷ elements)
      element-extend-set x∉elements elements-set (here refl) (here refl) = refl
      element-extend-set x∉elements elements-set (here refl) (there x∈x∷elements₂) = ⊥-elim (x∉elements x∈x∷elements₂)
      element-extend-set x∉elements elements-set (there x∈x∷elements₁) (here refl) = ⊥-elim (x∉elements x∈x∷elements₁)
      element-extend-set x∉elements elements-set (there y∈x∷elements₁) (there y∈x∷elements₂) = cong there (elements-set y∈x∷elements₁ y∈x∷elements₂)

      .element-remove-set : ∀ {x : A} {elements : List A} (x∷elements-set : IsSet (x ∷ elements)) → IsSet elements
      element-remove-set x∷elements-set e∈elements₁ e∈elements₂ = there-injective (x∷elements-set (there e∈elements₁) (there e∈elements₂))

    mk-set-injective : ∀ {α} {A : Set α} {as as′ : List A} .{as-set : IsSet as} .{as′-set : IsSet as′} → mk-set as as-set ≡ mk-set as′ as′-set → as ≡ as′
    mk-set-injective refl = refl

    cong-mk-set : ∀ {α} {A : Set α} {as as′ : List A} {as-set : IsSet as} {as′-set : IsSet as′} → as ≡ as′ → mk-set as as-set ≡ mk-set as′ as′-set
    cong-mk-set refl = refl

  instance
    fset-deceq : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ → DecEq (FSet A)
    fset-deceq {α} {A} = record { _≟_ = λ as as′ → ≟FS (elements as) (elements as′) (elements-set as) (elements-set as′) }
      where open FSet
            ≟FS : ∀ (as as′ : List A) .(as-set : IsSet as) .(as′-set : IsSet as′) → Dec (mk-set as as-set ≡ mk-set as′ as′-set)
            ≟FS [] [] as-set as′-set = yes refl
            ≟FS [] (a′ ∷ as′) as-set as′-set = no (λ ())
            ≟FS (a ∷ as) [] as-set as′-set = no (λ ())
            ≟FS (a ∷ as) (a′ ∷ as′) as-set as′-set with (a ≟ a′)
            ≟FS (a ∷ as) (.a ∷ as′) as-set as′-set | yes refl with (≟FS as as′ (element-remove-set as-set) (element-remove-set as′-set))
            ≟FS (a ∷ as) (.a ∷ .as) as-set as′-set | yes refl | yes refl = yes refl
            ≟FS (a ∷ as) (.a ∷ as′) as-set as′-set | yes refl | no  as≢as′ = no (λ set·as≡set·as′ → as≢as′ (cong-mk-set (∷-injective₂ (mk-set-injective set·as≡set·as′))))
            ≟FS (a ∷ as) (a′ ∷ as′) as-set as′-set | no a≢a′ = no (λ set·as≡set·as′ → a≢a′ (∷-injective₁ (mk-set-injective set·as≡set·as′)))

    postulate
      element-deceq : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ {as : FSet A} → DecEq (FSet.Element as)

    private
      element-inhabitants : ∀ {α} {A : Set α} (as : List A) .(as-set : IsSet as) → List (FSet.Element (mk-set as as-set))
      element-inhabitants [] []-set = []
      element-inhabitants (a ∷ as) a∷as-set with (element-inhabitants as (element-remove-set a∷as-set))
      ... | inhabitants-as = ‹ a › ∷ List.map (λ { ‹ a › → ‹ a › }) inhabitants-as

      postulate -- TODO proof
        .element-inhabitants-enumerate : ∀ {α} {A : Set α} (as : List A) .(as-set : IsSet as) (a : FSet.Element (mk-set as as-set)) →
                                            let open Membership (setoid (Element (mk-set as as-set)))
                                            in a ∈ (element-inhabitants as as-set)

    element-finite : ∀ {α} {A : Set α} {as : FSet A} → Finite (FSet.Element as)
    element-finite {α} {A} {as} = record {
      inhabitants = element-inhabitants (FSet.elements as) (FSet.elements-set as) ;
      inhabitants-enumerate = element-inhabitants-enumerate (FSet.elements as) (FSet.elements-set as) }

  _∈_ _∉_ : ∀ {α} {A : Set α} → A → FSet A → Set α
  _∈_ {A = A} a as = a AMemb.∈ elements as
    where module AMemb = Membership (PropEq.setoid A)
  _∉_ a as = a ∈ as → ⊥

  infix 4 _⊆_ _≈_
  _⊆_ _≈_ : ∀ {α} {A : Set α} → FSet A → FSet A → Set α
  as ⊆ as′ = ∀ (a : FSet.Element as) → Element.value a ∈ as′
  as ≈ as′ = as ⊆ as′ × as′ ⊆ as

  coe : ∀ {α} {A : Set α} {as as′ : FSet A} → .(as ⊆ as′) → Element as → Element as′
  coe as⊆as′ a = ‹ Element.value a › ⦃ as⊆as′ a ⦄

  .⊆-refl : ∀ {α} {A : Set α} {xs : FSet A} → xs ⊆ xs
  ⊆-refl = λ a → Element.value∈elements a

  .⊆-trans : ∀ {α} {A : Set α} {xs ys zs : FSet A} → xs ⊆ zs → zs ⊆ ys → xs ⊆ ys
  ⊆-trans xs⊆zs zs⊆ys = λ a → zs⊆ys (coe xs⊆zs a)

  .≈-refl : ∀ {α} {A : Set α} {xs : FSet A} → xs ≈ xs
  ≈-refl = ⊆-refl , ⊆-refl

  .≈-sym  : ∀ {α} {A : Set α} {xs ys : FSet A} → xs ≈ ys → ys ≈ xs
  ≈-sym (xs⊆ys , ys⊆xs) = ys⊆xs , xs⊆ys

  .≈-trans : ∀ {α} {A : Set α} {xs ys zs : FSet A} → xs ≈ zs → zs ≈ ys → xs ≈ ys
  ≈-trans {xs = xs} {ys = ys} {zs = zs} (xs⊆zs , zs⊆xs) (zs⊆ys , ys⊆zs) =
    ⊆-trans {ys = ys} xs⊆zs zs⊆ys , ⊆-trans {ys = xs} ys⊆zs zs⊆xs

  .⊆-∈ : ∀ {α} {A : Set α} {as′ as : FSet A} (as′⊆as : as′ ⊆ as) {a : A} (a∈as′ : a ∈ as′) → a ∈ as
  ⊆-∈ as′⊆as {a = a} a∈as′ = as′⊆as (‹ a › ⦃ a∈as′ ⦄)

  .⊆-∉ : ∀ {α} {A : Set α} {as′ as : FSet A} (as′⊆as : as′ ⊆ as) {a : A} (a∉as : a ∉ as) → a ∉ as′
  ⊆-∉ {as′ = as′} {as = as} as′⊆as {a = a} a∉as a∈as′ = a∉as (⊆-∈ {as′ = as′} {as = as} as′⊆as {a = a} a∈as′)

  _?∈_ : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ (a : A) (as : FSet A) → Dec (a ∈ as)
  a ?∈ as = Any.any (a ≟_) (elements as)

  _?⊆_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as′ as : FSet A) → Dec (as′ ⊆ as)
  _?⊆_ as′ as with (All.all (_?∈ as) (elements as′))
  _?⊆_ {α} {A} as′ as | yes all∣as′⊆as = yes (⊆-✓ (elements as′) (elements-set as′) as all∣as′⊆as)
    where ⊆-✓ : ∀ (as′-elements : List A) .(as′-elements-set : IsSet as′-elements) (as : FSet A)
                   (all∣as′⊆as : All (_∈ as) as′-elements) (a : FSet.Element (mk-set as′-elements as′-elements-set)) → Element.value a ∈ as
          ⊆-✓ .[] as′-elements-set as₁ [] (‹ _ › ⦃ () ⦄)
          ⊆-✓ .(a′ ∷ as′-elements′) as′-elements-set as₁ (_∷_ {x = a′} {xs = as′-elements′} a′∈as all∣as′⊆as₁) a with (Element.value a ≟ a′)
          ⊆-✓ _ as′-elements-set as (a∈as ∷ all∣as′⊆as₁) ‹ _ › | yes refl = a∈as
          ⊆-✓ .(a′ ∷ as′-elements′) as′-elements-set as (_∷_ {x = a′} {xs = as′-elements′} a′∈as all∣as′⊆as₁)  a       | no a≢a′ =
            ⊆-✓ as′-elements′ (element-remove-set as′-elements-set) as all∣as′⊆as₁
               (‹ Element.value a › ⦃ case Element.value∈elements a of (λ { (here a≡a′) → ⊥-elim (a≢a′ a≡a′) ; (there a∈elements′) → a∈elements′ }) ⦄)
  _?⊆_ {α} {A} as′ as | no ¬all|as′⊆as = no (λ as′⊆as → ¬all|as′⊆as (as′⊆as⇒all|as′⊆as (elements as′) (elements-set as′) as as′⊆as))
    where as′⊆as⇒all|as′⊆as : ∀ (elements-as′ : List A) .(elements-set-as′ : IsSet elements-as′) (as : FSet A)
                                (as′⊆as : mk-set elements-as′ elements-set-as′ ⊆ as) → All (_∈ as) elements-as′
          as′⊆as⇒all|as′⊆as [] elements-as′-set as as′⊆as = []
          as′⊆as⇒all|as′⊆as (a ∷ as′) elements-as′-set as as′⊆as =
            as′⊆as (‹ a › ⦃ here refl ⦄) ∷ as′⊆as⇒all|as′⊆as as′ (element-remove-set elements-as′-set) as
                (λ a′ → as′⊆as (‹ Element.value a′ › ⦃ there (Element.value∈elements a′) ⦄ ))

  _◀_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as : FSet A) (a : A) → FSet A
  as ◀ a with (a ?∈ as)
  as ◀ a | yes a∈as = as
  mk-set elements elements-set ◀ a | no a∉as = mk-set (a ∷ elements) (element-extend-set a∉as elements-set)

  ◀-extending : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ (a : A) (as : FSet A) → FSet.Element (as ◀ a)
  ◀-extending a as with (a ?∈ as)
  ◀-extending a as | yes a∈as = ‹ a › ⦃ a∈as ⦄
  ◀-extending a as | no  a∉as = ‹ a › ⦃ here refl ⦄

  ◀-retaining : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (a : A) (as : FSet A) (a′ : FSet.Element as) → FSet.Element (as ◀ a)
  ◀-retaining a as a′ with (a ?∈ as)
  ◀-retaining a as a′ | yes a∈as = a′
  ◀-retaining a as (‹ value › ⦃ value∈as ⦄) | no a∉as = ‹ value › ⦃ there value∈as ⦄

  ◀-exact : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (a : A) (as : FSet A) → (el : FSet.Element (as ◀ a)) → Element as ⊎ Element.value el ≡ a
  ◀-exact a as el with (a ?∈ as)
  ◀-exact a as el                        | yes a∈as = inj₁ el
  ◀-exact a as ‹ value ›                 | no  a∉as with (a ≟ value)
  ◀-exact a as ‹ .a ›                    | no a∉as | yes refl = inj₂ refl
  ◀-exact a as (‹ value › ⦃ value∈a◀as ⦄) | no a∉as | no a≢value =
    inj₁ (‹ value › ⦃ case value∈a◀as of λ { (here a≡value) → ⊥-elim (a≢value (sym a≡value)) ; (there value∈as) → value∈as} ⦄)

  _∖¹_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as : FSet A) (a : A) → FSet A
  _∖¹_ {α} {A} as a with (a ?∈ as)
  _∖¹_ {α} {A} as a | yes a∈as = rem (elements as) (elements-set as) a a∈as
    where module AMemb = Membership (PropEq.setoid A)
          rem : (elems : List A) .(elems-set : IsSet elems) (a : A) (a∈elems : a AMemb.∈ elems) → FSet A
          rem .(a ∷ elems′) elems-set a (here {xs = elems′} refl) = mk-set elems′ (element-remove-set elems-set)
          rem .(x ∷ elems′) elems-set a (there {x = x} {xs = elems′} a∈elems) = rem elems′ (element-remove-set elems-set) a a∈elems ◀ x
  _∖¹_ {α} {A} as a | no  a∉as = as

  element-extend : ∀ {α} {A : Set α} (a : A) (as : FSet A) .(a∉as : a ∉ as) → FSet A
  element-extend a as a∉as = mk-set (a ∷ elements as) (element-extend-set a∉as (elements-set as))

  ∅  : ∀ {α} {A : Set α} → FSet A
  ∅ = mk-set [] (λ ())

  ∅-empty : ∀ {α} {A : Set α} {a : A} → a ∉ ∅
  ∅-empty ()

  ∅-least : ∀ {α} {A : Set α} {as : FSet A} → ∅ ⊆ as
  ∅-least (‹ a › ⦃ () ⦄)

  [_] : ∀ {α} {A : Set α} (a : A) → FSet A
  [ a ] = element-extend a ∅ (λ ())

  _∪_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (xs ys : FSet A) → FSet A
  xs ∪ ys = foldr (λ x xs′∪ys → xs′∪ys ◀ x) ys (elements xs)

  _∩_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (xs ys : FSet A) → FSet A
  xs ∩ ys = foldr (λ x xs′∩ys → case Any.any (x ≟_) (elements ys) of λ { (yes x∈ys) → xs′∩ys ◀ x ; (no x∉ys) → xs′∩ys } ) ∅ (elements xs)

  _∖_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (xs ys : FSet A) → FSet A
  xs ∖ ys = foldr (λ y xs′∖ys → xs′∖ys ∖¹ y) xs (elements ys)

  fromList : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ → List A → FSet A
  fromList [] = mk-set [] (λ ())
  fromList (x ∷ xs) with (fromList xs)
  fromList (x ∷ xs) | mk-set elements elements-set with (Any.any (x ≟_) elements)
  fromList (x ∷ xs) | mk-set elements elements-set | yes x∈elements = mk-set elements elements-set
  fromList {A = A} (x ∷ xs) | mk-set elements elements-set | no x∉elements = mk-set (x ∷ elements) (element-extend-set x∉elements elements-set)

  toList : ∀ {α} {A : Set α} → FSet A → List A
  toList = elements

  map/≡ : ∀ {α β} {A : Set α} {B : Set β} ⦃ decEqB : DecEq B ⦄ → (A → B) → FSet A → FSet B
  map/≡ f as = fromList (List.map f (elements as))

  fold : ∀ {α π} {A : Set α} {P : FSet A → Set π} →
    P ∅ → (∀ (a : A) (as : FSet A) .(a∉as : a ∉ as) (pas : P as) → P (element-extend a as a∉as)) → (as : FSet A) → P as
  fold {α} {π} {A} {P} p∅ p◀ (mk-set elements elements-set) = fold′ elements elements-set
    where fold′ : ∀ (elements : List A) .(elements-set : IsSet elements) → P (mk-set elements elements-set)
          fold′ [] []-set = p∅
          fold′ (e ∷ elements) e∷elements-set =
            p◀ e (mk-set elements (element-remove-set e∷elements-set))
                 (λ e∈elements → here≢there (e∷elements-set (here refl) (there e∈elements)))
                 (fold′ elements (element-remove-set e∷elements-set))

  filter : ∀ {α} {A : Set α} → (p : A → Bool) → FSet A → FSet A
  filter {α} {A} p as = proj₁ (fold {P = λ as → Σ[ as′ ∈ FSet A ] (Irr (as′ ⊆ as))}
                                    (∅ , irr (∅-least {as = ∅}))
                                    (λ { a as₁ a∉as₁ (as′ , as′⊆as₁)  →
                                          if p a
                                          then (let as″ = mk-set (a ∷ elements as′) (element-extend-set (⊆-∉ {as = as₁} (Irr.proof as′⊆as₁) a∉as₁) (elements-set as′))
                                                in as″ , irr {A = (a′ : Element as″) → Element.value a′ ∈ element-extend a as₁ a∉as₁ }
                                                             (λ a′ → case Element.value∈elements a′ of λ {
                                                                        (here a′≡a) → here a′≡a;
                                                                        (there a′∈as′) → there (Irr.proof as′⊆as₁ (‹ Element.value a′ › ⦃ a′∈as′ ⦄))
                                                                     }))
                                          else as′ , irr (λ a′ → there (Irr.proof as′⊆as₁ a′)) }) as)


  data _≢∅ {α} {A : Set α} : FSet A → Set (Level.suc α) where
    instance
      ok! : ∀ {a as} .{a∷as-set : IsSet (a ∷ as)} → mk-set (a ∷ as) a∷as-set ≢∅

  [_]⊎_≈_ : ∀ {α} {A : Set α} (a : A) (as : FSet A) (as′ : FSet A) → Set α
  [ a ]⊎ as ≈ as′ = Σ[ a∉as ∈ a ∉ as ] element-extend a as a∉as ≈ as′

  ⋓ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (xss : FSet (FSet A)) → FSet A
  ⋓ = fold ∅ (λ a ass a∉ass as′ → a ∪ as′)

  ⋒ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (xss : FSet (FSet A)) ⦃ xss≢∅ : xss ≢∅ ⦄ → FSet A
  ⋒ _ ⦃ ok! {a} {as} {a∷as-set} ⦄ = fold a (λ a ass a∉ass as′ → a ∩ as′) (mk-set as (element-remove-set a∷as-set))
