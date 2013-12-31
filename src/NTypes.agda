{-# OPTIONS --without-K #-}
module NTypes where

open import Equivalence
open import FunExt
open import GroupoidStructure
open import NTypes.Contractible
open import PathOperations
open import Transport
open import Types

isProp : ∀ {a} → Set a → Set _
isProp A = (x y : A) → x ≡ y

isSet : ∀ {a} → Set a → Set _
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

set→id-prop : ∀ {a} {A : Set a} →
  isSet A → {x y : A} → isProp (x ≡ y)
set→id-prop A-set = A-set _ _

id-prop→set : ∀ {a} {A : Set a} →
  ({x y : A} → isProp (x ≡ y)) → isSet A
id-prop→set f _ _ = f

prop-eq : ∀ {a b} {A : Set a} {B : Set b} → A ≃ B → isProp A → isProp B
prop-eq (f , (g , α) , (h , β)) A-prop x y =
  tr id
    ( ap (λ z → z ≡ f (g y)) (α x)
    · ap (λ z → x ≡ z)       (α y)
    )
    (ap f (A-prop (g x) (g y)))

-- Levels.
is-[_-2]-type : ℕ → ∀ {a} → Set a → Set a
is-[ n -2]-type = ind (λ _ → Set _ → Set _)
  (λ _ r A → (x y : A) → r (x ≡ y))
  isContr
  n

prop→-1-type : ∀ {a} {A : Set a} →
  isProp A → is-[ 1 -2]-type A
prop→-1-type {A = A} A-prop x y
  = A-prop x y
  , path
  where
  split-path : {x y : A} (p : x ≡ y) →
    A-prop x y ≡ p · A-prop y y
  split-path = J
    (λ x y p → A-prop x y ≡ p · A-prop y y)
    (λ _ → refl) _ _

  path : {x y : A} (p : x ≡ y) → A-prop x y ≡ p
  path = J
    (λ x y p → A-prop x y ≡ p)
    (λ x → split-path (A-prop x x ⁻¹) · p⁻¹·p (A-prop x x))
    _ _

n-type-suc : ∀ n {a} {A : Set a} →
  is-[ n -2]-type A → is-[ suc n -2]-type A
n-type-suc n = ind
  (λ n → ∀ {A} → is-[ n -2]-type A → is-[ suc n -2]-type A)
  (λ _ r h x y → r (h x y))
  (λ     h → prop→-1-type λ x y → π₂ h x ⁻¹ · π₂ h y)
  n

-- From lectures.
prop→set : ∀ {a} {A : Set a} →
  isProp A → isSet A
prop→set A-prop x y p q = lem p · lem q ⁻¹
  where
  g : _
  g = A-prop x

  lem : (p : x ≡ y) → p ≡ g x ⁻¹ · g y
  lem p
    = id·p p ⁻¹
    · ap (λ z → z · p)
      (p⁻¹·p (g x)) ⁻¹
    · p·q·r (g x ⁻¹) (g x) p ⁻¹
    · ap (λ z → g x ⁻¹ · z)
      ( tr-post x p (g x) ⁻¹
      · dap g p
      )

isProp-is-prop : ∀ {a} {A : Set a} →
  isProp (isProp A)
isProp-is-prop f g =
  funext λ x →
  funext λ y →
  prop→set f _ _ (f x y) (g x y)

isSet-is-prop : ∀ {a} {A : Set a} →
  isProp (isSet A)
isSet-is-prop f g =
  funext λ x →
  funext λ y →
  funext λ p →
  funext λ q →
  prop→set (f x y) _ _ (f x y p q) (g x y p q)
