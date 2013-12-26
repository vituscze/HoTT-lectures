module HomotopyTypes.Product where

open import HomotopyTypes
open import PathOperations
open import PathStructure.Product
open import Types

×-isSet : ∀ {a b} {A : Set a} {B : Set b} →
  isSet A → isSet B → isSet (A × B)
×-isSet A-set B-set x y p q
  = split-eq p ⁻¹
  · ap (λ y → ap₂ _,_ y (ap π₂ p))
    (A-set _ _ (ap π₁ p) (ap π₁ q))
  · ap (λ y → ap₂ _,_ (ap π₁ q) y)
    (B-set _ _ (ap π₂ p) (ap π₂ q))
  · split-eq q
  where
  split-eq : (p : x ≡ y) → ap₂ _,_ (ap π₁ p) (ap π₂ p) ≡ p
  split-eq = π₂ (π₂ (π₂ split-merge-eq))
