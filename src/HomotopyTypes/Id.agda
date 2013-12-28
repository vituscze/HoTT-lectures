{-# OPTIONS --without-K #-}
module HomotopyTypes.Id where

open import GroupoidStructure
open import HomotopyTypes
open import PathOperations
open import Types

-- This should also be derivable from hLevel-suc from
-- HomotopyTypes.HLevel module.
Id-isSet : ∀ {a} {A : Set a} {x y : A} →
  isSet A → isSet (x ≡ y)
Id-isSet {x = x} {y = y} A-set p q pp qq
  = path pp ⁻¹ · path qq
  where
  split-path : {p q : x ≡ y} (pp : p ≡ q) →
    A-set _ _ p q ≡ pp · A-set _ _ q q
  split-path pp = J
    (λ p q pp → A-set _ _ p q ≡ pp · A-set _ _ q q)
    (λ _ → refl) _ _ pp

  path : {p q : x ≡ y} (pp : p ≡ q) →
    A-set _ _ p q ≡ pp
  path pp = J
    (λ p q pp → A-set _ _ p q ≡ pp)
    (λ p → split-path (A-set _ _ p p ⁻¹) · p⁻¹·p (A-set _ _ p p))
    _ _ pp
