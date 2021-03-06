{-# OPTIONS --without-K #-}
module GroupoidStructure {a} {A : Set a} where

open import PathOperations
open import Types

p·p⁻¹ : {a b : A} (p : a ≡ b) → p · p ⁻¹ ≡ refl
p·p⁻¹ = J (λ _ _ p → p · p ⁻¹ ≡ refl) (λ _ → refl) _ _

p⁻¹·p : {a b : A} (p : a ≡ b) → p ⁻¹ · p ≡ refl
p⁻¹·p = J (λ _ _ p → p ⁻¹ · p ≡ refl) (λ _ → refl) _ _

p·id : {a b : A} (p : a ≡ b) → p · refl ≡ p
p·id = J (λ _ _ p → p · refl ≡ p) (λ _ → refl) _ _

id·p : {a b : A} (p : a ≡ b) → refl · p ≡ p
id·p _ = refl

p·q·r : {a b c d : A} (p : a ≡ b) (q : b ≡ c) (r : c ≡ d) →
  p · (q · r) ≡ (p · q) · r
p·q·r {c = c} {d = d} = J
  (λ _ b p → (q : b ≡ c) (r : c ≡ d) → p · q · r ≡ (p · q) · r)
  (λ b → J
    (λ _ c q → (r : c ≡ d) → refl · q · r ≡ (refl · q) · r)
    (λ _ _ → refl) _ _)
  _ _
