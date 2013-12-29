{-# OPTIONS --without-K #-}
module HomotopyTypes.DoubleNegation where

open import FunExt
open import HomotopyTypes
open import Types

¬¬-prop : ∀ {a} {A : Set a} → isProp ((A → ⊥) → ⊥)
¬¬-prop x y = funext λ _ → 0-elim _ (x _)
