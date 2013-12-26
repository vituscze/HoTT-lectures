{-# OPTIONS --without-K #-}
module Transport where

open import GroupoidStructure
open import PathOperations
open import Types

tr-post : ∀ {a} {A : Set a} (a : A) {x y : A}
  (p : x ≡ y) (q : a ≡ x) →
  tr (λ x → a ≡ x) p q ≡ q · p
tr-post a p q = J
  (λ x y p → (q : a ≡ x) → tr (λ x → a ≡ x) p q ≡ q · p)
  (λ _ q → p·id q ⁻¹)
  _ _ p q

tr-pre : ∀ {a} {A : Set a} (a : A) {x y : A}
  (p : x ≡ y) (q : x ≡ a) →
  tr (λ x → x ≡ a) p q ≡ p ⁻¹ · q
tr-pre a p q = J
  (λ x y p → (q : x ≡ a) → tr (λ x → x ≡ a) p q ≡ p ⁻¹ · q)
  (λ _ q → id·p q ⁻¹)
  _ _ p q

tr-both : ∀ {a} {A : Set a} (a : A) {x y : A}
  (p : x ≡ y) (q : x ≡ x) →
  tr (λ x → x ≡ x) p q ≡ p ⁻¹ · q · p
tr-both a p q = J
  (λ x y p → (q : x ≡ x) → tr (λ x → x ≡ x) p q ≡ p ⁻¹ · q · p)
  (λ _ q → p·id q ⁻¹ · id·p (q · refl) ⁻¹)
  _ _ p q

tr-∘ : ∀ {a b p} {A : Set a} {B : Set b} {P : B → Set p}
  (f : A → B) {x y : A} (p : x ≡ y) (u : P (f x)) →
  tr (P ∘ f) p u ≡ tr P (ap f p) u
tr-∘ {P = P} f p u = J
  (λ x _ p → (u : P (f x)) → tr (P ∘ f) p u ≡ tr P (ap f p) u)
  (λ _ _ → refl) _ _ p u
