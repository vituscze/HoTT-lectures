{-# OPTIONS --without-K #-}
module Homotopy where

open import GroupoidStructure
open import PathOperations
open import Types

infix  1 _∼_

_∼_ : ∀ {a b} {A : Set a} {B : Set b}
  (f g : A → B) → Set _
f ∼ g = ∀ x → f x ≡ g x

naturality : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
  (f g : A → B) (H : f ∼ g) (p : x ≡ y) →
  H x · ap g p ≡ ap f p · H y
naturality f g H = J
  (λ x y p → H x · ap g p ≡ ap f p · H y)
  (λ _ → p·id _) _ _
