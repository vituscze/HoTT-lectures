{-# OPTIONS --without-K #-}
module HomotopyTypes where

open import Equivalence
open import PathOperations
open import Types

isProp : ∀ {a} → Set a → Set _
isProp A = (x y : A) → x ≡ y

isSet : ∀ {a} → Set a → Set _
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

set→id-prop : ∀ {a} {A : Set a} →
  isSet A → {x y : A} → isProp (x ≡ y)
set→id-prop A-set p q = A-set _ _ p q

id-prop→set : ∀ {a} {A : Set a} →
  ({x y : A} → isProp (x ≡ y)) → isSet A
id-prop→set f _ _ p q = f p q

prop-eq : ∀ {a b} {A : Set a} {B : Set b} → A ≃ B → isProp A → isProp B
prop-eq (f , (g , α) , (h , β)) A-prop x y =
  tr id
    ( ap (λ z → z ≡ f (g y)) (α x)
    · ap (λ z → x ≡ z)       (α y)
    )
    (ap f (A-prop (g x) (g y)))
