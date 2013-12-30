{-# OPTIONS --without-K #-}
module PathStructure.Empty where

open import Equivalence
open import Types

split-path : {x y : ⊥} → x ≡ y → ⊥
split-path = J (λ _ _ _ → ⊥) id _ _

merge-path : {x y : ⊥} → ⊥ → x ≡ y
merge-path = 0-elim

split-merge-eq : {x y : ⊥} → (x ≡ y) ≃ ⊥
split-merge-eq
  = split-path
  , (merge-path , λ b → 0-elim b)
  , (merge-path , J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (λ b → 0-elim b) _ _)
