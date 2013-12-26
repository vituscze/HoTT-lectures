module HomotopyTypes.Coproduct where

open import HomotopyTypes
open import PathOperations
open import PathStructure.Coproduct
open import Types

⊎-isSet : ∀ {A : Set} {B : Set} →
  isSet A → isSet B → isSet (A ⊎ B)
⊎-isSet {A = A} {B = B} A-set B-set x y p q =
  case (λ x → (y : A ⊎ B) (p q : x ≡ y) → p ≡ q)
  (λ a y p q → case
    (λ y → (p q : inl a ≡ y) → p ≡ q)
    (λ a′ p q
      → split-eq p ⁻¹
      · ap (ap inl)
        (A-set _ _
          (lower (tr (F (inl a)) p (lift refl)))
          (lower (tr (F (inl a)) q (lift refl)))
        )
      · split-eq q
      )
    (λ _  p q → 0-elim _
      (lower (split-path p)))
    y p q)
  (λ b y p q → case
    (λ y → (p q : inr b ≡ y) → p ≡ q)
    (λ _  p q → 0-elim _
      (lower (split-path p)))
    (λ b′ p q
      → split-eq p ⁻¹
      · ap (ap inr)
        (B-set _ _
          (lower (tr (F (inr b)) p (lift refl)))
          (lower (tr (F (inr b)) q (lift refl)))
        )
      · split-eq q
      )
    y p q)
  x y p q
  where
  split-eq : {x y : A ⊎ B} → _
  split-eq {x = x} {y = y} =
    π₂ (π₂ (π₂ (split-merge-eq {x = x} {y = y})))
