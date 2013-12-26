{-# OPTIONS --without-K #-}
module HomotopyTypes.Contractible where

open import Types

isContr : ∀ {a} → Set a → Set _
isContr A = Σ A λ x → (y : A) → x ≡ y
