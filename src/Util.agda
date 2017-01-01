module Util where

import Level
open import Data.Bool hiding (_≟_)
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)
open import Data.List as List hiding ([_]; map; filter)
open import Data.List.Any as Any hiding (map)
open import Data.List.All as All hiding (map)

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
open import Function

record Irr {α} (A : Set α) : Set α where
  constructor irr
  field
    .proof : A

Σ-inst : ∀ {α π} (A : Set α) → (P : ⦃ a : A ⦄ → Set π) → Set (α Level.⊔ π)
Σ-inst A P = Σ[ a ∈ A ] P ⦃ a ⦄

private
  there-injective : ∀ {α π} {A : Set α} {x : A} {P : A → Set π} {xs : List A} {x-any y-any : Any P xs} → there {x = x} x-any ≡ there y-any → x-any ≡ y-any
  there-injective refl = refl

  here≢there : ∀ {α π} {A : Set α} {x : A} {P : A → Set π} {xs : List A} {px : P x} {any : Any P xs} → here px ≡ there any → ⊥
  here≢there ()

module Closures where
  data _⟨_⟩⁇_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []   : x ⟨ _r_ ⟩⁇ x
    [_] : ∀ {y : A} → x r y → x ⟨ _r_ ⟩⁇ y

  data _⟨_⟩*_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    []  : x ⟨ _r_ ⟩* x
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩* z

  data _⟨_⟩⁺_ {α} {A : Set α} (x : A) (_r_ : A → A → Set α) : A → Set α where
    _∷_ : ∀ {y z : A} → x r y → y ⟨ _r_ ⟩* z → x ⟨ _r_ ⟩⁺ z

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

record DecEq {α} (A : Set α) : Set (Level.suc α) where
  field
    _≟_ : (x y : A) → Dec (x ≡ y)
open DecEq ⦃ ... ⦄

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

  _∈?_ : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ (a : A) (as : FSet A) → Dec (a ∈ as)
  a ∈? as = Any.any (a ≟_) (elements as)

  _⊆?_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as′ as : FSet A) → Dec (as′ ⊆ as)
  _⊆?_ as′ as with (All.all (_∈? as) (elements as′))
  _⊆?_ {α} {A} as′ as | yes all∣as′⊆as = yes (⊆-✓ (elements as′) (elements-set as′) as all∣as′⊆as)
    where ⊆-✓ : ∀ (as′-elements : List A) .(as′-elements-set : IsSet as′-elements) (as : FSet A)
                   (all∣as′⊆as : All (_∈ as) as′-elements) (a : FSet.Element (mk-set as′-elements as′-elements-set)) → Element.value a ∈ as
          ⊆-✓ .[] as′-elements-set as₁ [] (‹ _ › ⦃ () ⦄)
          ⊆-✓ .(a′ ∷ as′-elements′) as′-elements-set as₁ (_∷_ {x = a′} {xs = as′-elements′} a′∈as all∣as′⊆as₁) a with (Element.value a ≟ a′)
          ⊆-✓ _ as′-elements-set as (a∈as ∷ all∣as′⊆as₁) ‹ _ › | yes refl = a∈as
          ⊆-✓ .(a′ ∷ as′-elements′) as′-elements-set as (_∷_ {x = a′} {xs = as′-elements′} a′∈as all∣as′⊆as₁)  a       | no a≢a′ =
            ⊆-✓ as′-elements′ (element-remove-set as′-elements-set) as all∣as′⊆as₁
               (‹ Element.value a › ⦃ case Element.value∈elements a of (λ { (here a≡a′) → ⊥-elim (a≢a′ a≡a′) ; (there a∈elements′) → a∈elements′ }) ⦄)
  _⊆?_ {α} {A} as′ as | no ¬all|as′⊆as = no (λ as′⊆as → ¬all|as′⊆as (as′⊆as⇒all|as′⊆as (elements as′) (elements-set as′) as as′⊆as))
    where as′⊆as⇒all|as′⊆as : ∀ (elements-as′ : List A) .(elements-set-as′ : IsSet elements-as′) (as : FSet A)
                                (as′⊆as : mk-set elements-as′ elements-set-as′ ⊆ as) → All (_∈ as) elements-as′
          as′⊆as⇒all|as′⊆as [] elements-as′-set as as′⊆as = []
          as′⊆as⇒all|as′⊆as (a ∷ as′) elements-as′-set as as′⊆as =
            as′⊆as (‹ a › ⦃ here refl ⦄) ∷ as′⊆as⇒all|as′⊆as as′ (element-remove-set elements-as′-set) as
                (λ a′ → as′⊆as (‹ Element.value a′ › ⦃ there (Element.value∈elements a′) ⦄ ))

  _◀_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as : FSet A) (a : A) → FSet A
  as ◀ a with (a ∈? as)
  as ◀ a | yes a∈as = as
  mk-set elements elements-set ◀ a | no a∉as = mk-set (a ∷ elements) (element-extend-set a∉as elements-set)

  ◀-extending : ∀ {α} {A : Set α} ⦃ deceqA : DecEq A ⦄ (a : A) (as : FSet A) → FSet.Element (as ◀ a)
  ◀-extending a as with (a ∈? as)
  ◀-extending a as | yes a∈as = ‹ a › ⦃ a∈as ⦄
  ◀-extending a as | no  a∉as = ‹ a › ⦃ here refl ⦄

  ◀-retaining : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (a : A) (as : FSet A) (a′ : FSet.Element as) → FSet.Element (as ◀ a)
  ◀-retaining a as a′ with (a ∈? as)
  ◀-retaining a as a′ | yes a∈as = a′
  ◀-retaining a as (‹ value › ⦃ value∈as ⦄) | no a∉as = ‹ value › ⦃ there value∈as ⦄

  ◀-exact : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (a : A) (as : FSet A) → (el : FSet.Element (as ◀ a)) → Element as ⊎ Element.value el ≡ a
  ◀-exact a as el with (a ∈? as)
  ◀-exact a as el                        | yes a∈as = inj₁ el
  ◀-exact a as ‹ value ›                 | no  a∉as with (a ≟ value)
  ◀-exact a as ‹ .a ›                    | no a∉as | yes refl = inj₂ refl
  ◀-exact a as (‹ value › ⦃ value∈a◀as ⦄) | no a∉as | no a≢value =
    inj₁ (‹ value › ⦃ case value∈a◀as of λ { (here a≡value) → ⊥-elim (a≢value (sym a≡value)) ; (there value∈as) → value∈as} ⦄)

  _∖¹_ : ∀ {α} {A : Set α} ⦃ decEqA : DecEq A ⦄ (as : FSet A) (a : A) → FSet A
  _∖¹_ {α} {A} as a with (a ∈? as)
  _∖¹_ {α} {A} as a | yes a∈as = rem (elements as) (elements-set as) a a∈as
    where module AMemb = Membership (PropEq.setoid A)
          rem : (elems : List A) .(elems-set : IsSet elems) (a : A) (a∈elems : a AMemb.∈ elems) → FSet A
          rem .(a ∷ elems′) elems-set a (here {xs = elems′} refl) = mk-set elems′ (element-remove-set elems-set)
          rem .(x ∷ elems′) elems-set a (there {x = x} {xs = elems′} a∈elems) = rem elems′ (element-remove-set elems-set) a a∈elems ◀ x
  _∖¹_ {α} {A} as a | no  a∉as = as

  ∅  : ∀ {α} {A : Set α} → FSet A
  ∅ = mk-set [] (λ ())

  ∅-empty : ∀ {α} {A : Set α} {a : A} → a ∉ ∅
  ∅-empty ()

  ∅-least : ∀ {α} {A : Set α} {as : FSet A} → ∅ ⊆ as
  ∅-least (‹ a › ⦃ () ⦄)

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

  map : ∀ {α β} {A : Set α} {B : Set β} ⦃ decEqB : DecEq B ⦄ → (A → B) → FSet A → FSet B
  map f as = fromList (List.map f (elements as))

  fold : ∀ {α π} {A : Set α} {P : FSet A → Set π} →
    P ∅ → (∀ (a : A) (as : FSet A) .(a∉as : a ∉ as) (pas : P as) → P (mk-set (a ∷ elements as) (element-extend-set a∉as (elements-set as)))) → (as : FSet A) → P as
  fold {α} {π} {A} {P} p∅ p◀ (mk-set elements elements-set) = fold′ elements elements-set
    where fold′ : ∀ (elements : List A) .(elements-set : IsSet elements) → P (mk-set elements elements-set)
          fold′ [] []-set = p∅
          fold′ (e ∷ elements) e∷elements-set =
            p◀ e (mk-set elements (element-remove-set e∷elements-set))
                 (λ e∈elements → here≢there (e∷elements-set (here refl) (there e∈elements)))
                 (fold′ elements (element-remove-set e∷elements-set))

  filter : ∀ {α} {A : Set α} → (p : A → Bool) → FSet A → FSet A
  filter p (mk-set elements elements-set) = proj₁ (filter′ p elements elements-set)
    where filter′ : ∀ {α} {A : Set α} (p : A → Bool) (as : List A) .(as-set : IsSet as) → Σ[ as′ ∈ FSet A ] (Irr (as′ ⊆ mk-set as as-set))
          filter′ p [] as-set = ∅ , irr (∅-least {as = mk-set [] as-set})
          filter′ p (a ∷ as) a∷as-set with p a | filter′ p as (element-remove-set a∷as-set)
          filter′ p (a ∷ as) a∷as-set | false | as′ , as′⊆as = as′ , irr (λ a′ → there (Irr.proof as′⊆as a′))
          filter′ p (a ∷ as) a∷as-set | true  | mk-set elements-as′ elements-as′-set , as′⊆as =
              mk-set (a ∷ elements-as′)
                     (element-extend-set (λ a∈as′ →
                        let a∈as = Irr.proof as′⊆as (‹ a › ⦃ a∈as′ ⦄) in here≢there (a∷as-set (here refl) (there a∈as))) elements-as′-set) ,
                 irr (λ a′ → case Element.value∈elements a′ of λ {
                                  (here a′≡a) → here a′≡a;
                                  (there a′∈as′) → there (Irr.proof as′⊆as (‹ Element.value a′ › ⦃ a′∈as′ ⦄)) })
