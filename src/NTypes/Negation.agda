{-# OPTIONS --without-K #-}
module NTypes.Negation where

open import FunExt
open import NTypes
open import Types

¬-isProp : ∀ {a} {A : Set a} → isProp (¬ A)
¬-isProp x y = funext λ _ → 0-elim _ (x _)
