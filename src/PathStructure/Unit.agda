module PathStructure.Unit where

open import Equivalence
open import Types

split-path : {x y : ⊤} → x ≡ y → ⊤
split-path _ = _

merge-path : {x y : ⊤} → ⊤ → x ≡ y
merge-path _ = refl

split-merge-eq : {x y : ⊤} → (x ≡ y) ≃ ⊤
split-merge-eq
  = split-path
  , (merge-path , λ _ → refl)
  , (merge-path , λ p → J {A = ⊤}
      (λ _ _ p → refl ≡ p)
      (λ _ → refl) _ _ p)
