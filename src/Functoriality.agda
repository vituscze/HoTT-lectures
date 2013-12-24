module Functoriality {a} {A : Set a} where

open import PathOperations
open import Types

ap⁻¹ : ∀ {b} {B : Set b} {x y : A} (f : A → B) (p : x ≡ y) →
  ap f (p ⁻¹) ≡ (ap f p) ⁻¹
ap⁻¹ f p = J
  (λ _ _ p → ap f (p ⁻¹) ≡ ap f p ⁻¹)
  (λ _ → refl) _ _ p

ap· : ∀ {b} {B : Set b} {x y z : A} (f : A → B)
  (p : x ≡ y) (q : y ≡ z) →
  ap f (p · q) ≡ ap f p · ap f q
ap· {z = z} f p q = J
  (λ _ y p → (q : y ≡ z) → ap f (p · q) ≡ ap f p · ap f q)
  (λ _ _ → refl) _ _ p q

ap-id : {x y : A} (p : x ≡ y) → ap id p ≡ p
ap-id p = J (λ _ _ p → ap id p ≡ p) (λ _ → refl) _ _ p

ap-∘ : ∀ {b c} {B : Set b} {C : Set c} {x y : A}
  (f : B → C) (g : A → B) (p : x ≡ y) →
  ap (f ∘ g) p ≡ ap f (ap g p)
ap-∘ f g p = J
  (λ _ _ p → ap (f ∘ g) p ≡ ap f (ap g p))
  (λ _ → refl) _ _ p
