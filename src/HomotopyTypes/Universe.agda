{-# OPTIONS --without-K #-}
module HomotopyTypes.Universe where

open import Equivalence
open import HomotopyTypes
open import PathOperations
open import PathStructure.Coproduct
open import Types
open import Univalence

Bool : Set
Bool = ⊤ ⊎ ⊤

not : Bool → Bool
not = case (λ _ → Bool) (λ _ → inr _) (λ _ → inl _)

not-not : ∀ x → not (not x) ≡ x
not-not = case
  (λ x → not (not x) ≡ x)
  (λ _ → refl) (λ _ → refl)

Bool-eq₁ : Bool ≃ Bool
Bool-eq₁ = ≡→eq refl

Bool-eq₂ : Bool ≃ Bool
Bool-eq₂
  = not
  , (not , not-not)
  , (not , not-not)

nope : Bool-eq₁ ≡ Bool-eq₂ → ⊥
nope x = lower (split-path (happly (ap π₁ x) (inl _)))

-- With Lift, we could prove stronger statement
-- (∀ ℓ → isSet (Set ℓ) → ⊥), but the idea is same - pick
-- something equivalent to Bool in Set ℓ, find two different
-- ways in which this type is equivalent and derive
-- a contradiction.
¬U-set : (∀ ℓ → isSet (Set ℓ)) → ⊥
¬U-set U-set = nope
  ( from-to-eq _ ⁻¹
  · ap from-≡
    (U-set _ Bool Bool (to-≡ Bool-eq₁) (to-≡ Bool-eq₂))
  · from-to-eq _
  )
  where
  from-≡     =         π₁ (ua {A = Bool} {B = Bool})
  to-≡       = π₁ (π₁ (π₂ (ua {A = Bool} {B = Bool})))
  from-to-eq = π₂ (π₁ (π₂ (ua {A = Bool} {B = Bool})))
