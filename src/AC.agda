{-# OPTIONS --without-K #-}
module AC {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} where

open import Equivalence
open import FunExt
open import Types

left : Set _
left = (x : A) → Σ (B x) λ y → C x y

right : Set _
right = Σ ((x : A) → B x) λ f → (x : A) → C x (f x)

to : left → right
to f = π₁ ∘ f , π₂ ∘ f

from : right → left
from f x = π₁ f x , π₂ f x

AC∞ : right ≃ left
AC∞
  = from
  , (to , λ _ → refl)
  , (to , λ _ → refl)
