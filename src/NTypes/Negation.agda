{-# OPTIONS --without-K #-}
module NTypes.Negation where

open import FunExt
open import NTypes
open import Types

¬-isProp : ∀ {a} {A : Set a} → isProp (¬ A)
¬-isProp ¬a _ = funext λ a → 0-elim (¬a a)
