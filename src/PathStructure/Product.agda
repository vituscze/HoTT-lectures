module PathStructure.Product {a b} {A : Set a} {B : Set b} where

open import Equivalence
open import PathOperations
open import Types

split-path : {x y : A × B} → x ≡ y → (π₁ x ≡ π₁ y) × (π₂ x ≡ π₂ y)
split-path p = ap π₁ p , ap π₂ p

merge-path : {x₁ x₂ : A} {y₁ y₂ : B} →
  (x₁ ≡ x₂) × (y₁ ≡ y₂) → (x₁ , y₁) ≡ (x₂ , y₂)
merge-path (p , q) = ap₂ _,_ p q

split-merge-eq : {x y : A × B} →
  (x ≡ y) ≃ (π₁ x ≡ π₁ y) × (π₂ x ≡ π₂ y)
split-merge-eq
  = split-path
  , ( merge-path
    , λ pq → J
        (λ _ _ p → ∀ {b₁ b₂} (q : b₁ ≡ b₂) →
          split-path (merge-path (p , q)) ≡ p , q)
        (λ _ q → J
          (λ _ _ q →
            split-path (merge-path (refl , q)) ≡ refl , q)
          (λ _ → refl) _ _ q)
        _ _ (π₁ pq) (π₂ pq)
    )
  , ( merge-path
    , J (λ _ _ p → merge-path (split-path p) ≡ p) (λ _ → refl) _ _
    )
