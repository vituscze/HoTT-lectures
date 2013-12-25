{-# OPTIONS --without-K #-}
module PathStructure.Id.Tr {a b} {A : Set a} {B : Set b} where

open import Equivalence
open import PathOperations
open import Types

tr-split : {a a′ : A} {b b′ : B} (p : a ≡ a′) →
  tr (λ _ → B) p b ≡ b′ → b ≡ b′
tr-split {b = b} {b′ = b′} p = J
  (λ _ _ p → tr (λ _ → B) p b ≡ b′ → b ≡ b′)
  (λ _ p → p) _ _ p

tr-merge : {a a′ : A} {b b′ : B} (p : a ≡ a′) →
  b ≡ b′ → tr (λ _ → B) p b ≡ b′
tr-merge {b = b} {b′ = b′} p = J
  (λ _ _ p → b ≡ b′ → tr (λ _ → B) p b ≡ b′)
  (λ _ p → p) _ _ p

tr-eq : {a a′ : A} {b b′ : B} (p : a ≡ a′) →
  (tr (λ _ → B) p b ≡ b′) ≃ (b ≡ b′)
tr-eq p
  = tr-split p
  , (tr-merge p , λ q → J
      (λ _ _ p → tr-split p (tr-merge p q) ≡ q)
      (λ _ → refl) _ _ p)
  , (tr-merge p , λ q → J
      (λ _ _ p → (b b′ : B) (q : tr (λ _ → B) p b ≡ b′) →
        tr-merge p (tr-split p q) ≡ q)
      (λ _ _ _ _ → refl) _ _ p _ _ q)
