module Equivalence where

open import Homotopy
open import PathOperations
open import Types

infix  1 _≃_

qinv : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) → Set _
qinv {A = A} {B = B} f =
  Σ (B → A) λ g → (f ∘ g ∼ id) × (g ∘ f ∼ id)

isequiv : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) → Set _
isequiv {A = A} {B = B} f
  = (Σ (B → A) λ g → f ∘ g ∼ id)
  × (Σ (B → A) λ h → h ∘ f ∼ id)

_≃_ : ∀ {a b} (A : Set a) (B : Set b) → Set _
A ≃ B = Σ (A → B) λ f → isequiv f

qi→eq : ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} → qinv f → isequiv f
qi→eq (g , p , q) = (g , p) , (g , q)

eq→qi : ∀ {a b} {A : Set a} {B : Set b}
  {f : A → B} → isequiv f → qinv f
eq→qi {f = f} ((g , p) , (h , q)) =
  g , p , λ _ → q _ ⁻¹ · ap h (p _) · q _

≡→eq : ∀ {ℓ} {A : Set ℓ} {B : Set ℓ} → A ≡ B → A ≃ B
≡→eq p
  = tr id p
  , (tr id (p ⁻¹) , λ b → J
      (λ _ B p → (b : B) → tr id p (tr id (p ⁻¹) b) ≡ b)
      (λ _ _ → refl)
      _ _ p b)
  , (tr id (p ⁻¹) , λ a → J
      (λ A _ p → (a : A) → tr id (p ⁻¹) (tr id p a) ≡ a)
      (λ _ _ → refl)
      _ _ p a)

refl-equiv : ∀ {a} {A : Set a} → A ≃ A
refl-equiv = id , (id , λ _ → refl) , (id , λ _ → refl)

sym-equiv : ∀ {a b} {A : Set a} {B : Set b} →
  A ≃ B → B ≃ A
sym-equiv (f , (g , p) , (h , q))
  = g
  , (f , λ _ → q _ ⁻¹ · ap h (p _) · q _)
  , (f , p)

trans-equiv : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
  A ≃ B → B ≃ C → A ≃ C
trans-equiv
  (f₁ , (g₁ , p₁) , (h₁ , q₁)) (f₂ , (g₂ , p₂) , (h₂ , q₂))
  =  f₂ ∘ f₁
  , (g₁ ∘ g₂ , λ _ → ap f₂ (p₁ _) · p₂ _)
  , (h₁ ∘ h₂ , λ _ → ap h₁ (q₂ _) · q₁ _)
