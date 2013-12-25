{-# OPTIONS --without-K #-}
module Sigma {a b} {A : Set a} {B : A → Set b} where

open import Equivalence
open import Types

-- Projections for the positive sigma.
π₁′ : (p : Σ′ A B) → A
π₁′ p = split (λ _ → A) (λ a _ → a) p

π₂′ : (p : Σ′ A B) → B (π₁′ p)
π₂′ p = split (λ p → B (π₁′ p)) (λ _ b → b) p

-- Induction principle for the negative sigma.
split′ : ∀ {p} (P : Σ A B → Set p)
  (f : (a : A) (b : B a) → P (a , b)) → ∀ z → P z
split′ P f p = f (π₁ p) (π₂ p)

Σ→Σ′ : Σ A B → Σ′ A B
Σ→Σ′ p = π₁ p , π₂ p

Σ′→Σ : Σ′ A B → Σ A B
Σ′→Σ = split _ _,_

Σ≃Σ′ : Σ A B ≃ Σ′ A B
Σ≃Σ′
  = Σ→Σ′
  , (Σ′→Σ , λ p → split
      (λ p → Σ→Σ′ (Σ′→Σ p) ≡ p)
      (λ _ _ → refl) p)
  , (Σ′→Σ , λ _ → refl)
