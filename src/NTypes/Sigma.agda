{-# OPTIONS --without-K #-}
module NTypes.Sigma where

open import NTypes
open import PathOperations
open import PathStructure.Sigma
open import Transport
open import Types

Σ-isSet : ∀ {a b} {A : Set a} {B : A → Set b} →
  isSet A → (∀ x → isSet (B x)) → isSet (Σ A B)
Σ-isSet {A = A} {B = B} A-set B-set x y p q
  = split-eq p ⁻¹
  · ap₂-dep-eq {B = B} _,_
      (ap π₁ p)
      (ap π₁ q)
      π₁-eq
      (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p)
      (tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q)
      π₂-eq
  · split-eq q
  where
  split-eq : (p : x ≡ y) →
    ap₂-dep {B = B} _,_ (ap π₁ p)
      (tr-∘ π₁ p (π₂ x) ⁻¹  · dap π₂ p) ≡ p
  split-eq = π₂ (π₂ (π₂ split-merge-eq))

  π₁-eq : ap π₁ p ≡ ap π₁ q
  π₁-eq = A-set _ _ (ap π₁ p) (ap π₁ q)

  π₂-eq : tr (λ z → tr B z (π₂ x) ≡ π₂ y) π₁-eq
            (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p)
        ≡ tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q
  π₂-eq = B-set _ (tr B (ap π₁ q) (π₂ x)) (π₂ y)
    (tr
      (λ z → tr B z (π₂ x) ≡ π₂ y)
      π₁-eq
      (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p))
    (tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q)
