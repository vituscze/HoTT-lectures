{-# OPTIONS --without-K #-}
module Univalence where

open import Equivalence
open import Types

postulate
  ua : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → (A ≡ B) ≃ (A ≃ B)
