{-# OPTIONS --without-K #-}
module NTypes.DoubleNegation where

open import FunExt
open import NTypes
open import Types

¬¬-prop : ∀ {a} {A : Set a} → isProp ((A → ⊥) → ⊥)
¬¬-prop x y = funext λ _ → 0-elim _ (x _)
