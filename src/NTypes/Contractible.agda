{-# OPTIONS --without-K #-}
module NTypes.Contractible where

open import Equivalence
open import Types

isContr : ∀ {a} → Set a → Set _
isContr A = Σ A λ x → (y : A) → x ≡ y

contr→eq-⊤ : ∀ {a} {A : Set a} → isContr A → A ≃ ⊤
contr→eq-⊤ h
  = (λ _ → _)
  , ((λ _ → π₁ h) , λ _ → refl)
  , ((λ _ → π₁ h) , π₂ h)

eq-⊤→contr : ∀ {a} {A : Set a} → A ≃ ⊤ → isContr A
eq-⊤→contr (f , (g , α) , (h , β)) = h _ , β

pp-space-contr : ∀ {a} {A : Set a} (x : A) →
  isContr (Σ A λ y → x ≡ y)
pp-space-contr {A = A} x
  = (x , refl)
  , λ y → J
      (λ x y p → Id (Σ A (λ y → x ≡ y)) (x , refl) (y , p))
      (λ _ → refl) _ _ (π₂ y)
