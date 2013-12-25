{-# OPTIONS --without-K #-}
module HomotopyTypes where

open import Types

isSet : ∀ {a} → Set a → Set _
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q
