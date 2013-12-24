{-# OPTIONS --without-K #-}
module PathStructure.Empty where

open import Equivalence
open import Types

split-path : {x y : ⊥} → x ≡ y → ⊥
split-path p = J (λ _ _ _ → ⊥) id _ _ p

merge-path : {x y : ⊥} → ⊥ → x ≡ y
merge-path = 0-elim _

split-merge-eq : {x y : ⊥} → (x ≡ y) ≃ ⊥
split-merge-eq
  = split-path
  , (merge-path , λ b → 0-elim _ b)
  , (merge-path , λ p → J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (λ b → 0-elim _ b) _ _ p)
