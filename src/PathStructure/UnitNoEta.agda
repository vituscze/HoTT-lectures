{-# OPTIONS --without-K #-}
module PathStructure.UnitNoEta where

open import Equivalence
open import Types

split-path : {x y : Unit} → x ≡ y → Unit
split-path _ = tt

merge-path : {x y : Unit} → Unit → x ≡ y
merge-path _ = 1-elim
  (λ x → ∀ y → x ≡ y)
  (1-elim (λ y → tt ≡ y) refl) _ _

split-merge-eq : {x y : Unit} → (x ≡ y) ≃ Unit
split-merge-eq
  = split-path
  , (merge-path , 1-elim (λ x → tt ≡ x) refl)
  , (merge-path , J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (1-elim
        (λ x → merge-path {x} {x} (split-path {x} {x} refl) ≡ refl)
        refl)
      _ _)
