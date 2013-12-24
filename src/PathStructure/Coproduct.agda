module PathStructure.Coproduct {a b} {A : Set a} {B : Set b} where

open import Equivalence
open import PathOperations
open import Types

-- We need to use Lift here, because Agda doesn't have
-- cumulative universes.
F : A ⊎ B → A ⊎ B → Set (a ⊔ b)
F x y =
  case (λ _ → A ⊎ B → Set _)
  (λ a y → case (λ _ → Set _) (λ a′ → Lift (a ≡ a′)) (λ _ → Lift ⊥) y)
  (λ b y → case (λ _ → Set _) (λ _ → Lift ⊥) (λ b′ → Lift (b ≡ b′)) y)
  x y

F-lemma : (x : A ⊎ B) → F x x
F-lemma x = case (λ x → F x x) (λ _ → lift refl) (λ _ → lift refl) x

split-path : {x y : A ⊎ B} → x ≡ y → F x y
split-path {x = x} p = tr (F x) p (F-lemma x)

merge-path : {x y : A ⊎ B} → F x y → x ≡ y
merge-path {x = x} {y = y} f = case (λ x → ∀ y → F x y → x ≡ y)
  (λ a y → case (λ y → F (inl a) y → inl a ≡ y)
    (λ _ → ap inl   ∘ lower)
    (λ _ → 0-elim _ ∘ lower)
    y)
  (λ b y → case (λ y → F (inr b) y → inr b ≡ y)
    (λ _ → 0-elim _ ∘ lower)
    (λ _ → ap inr   ∘ lower)
    y)
  x y f

split-merge-eq : {x y : A ⊎ B} → (x ≡ y) ≃ F x y
split-merge-eq {x = x} {y = y}
  = split-path
  , (merge-path , λ f → case
      (λ x → ∀ y (f : F x y) → split-path (merge-path {x} {y} f) ≡ f)
      (λ a y → case
        (λ y → (f : F (inl a) y) →
          split-path (merge-path {inl a} {y} f) ≡ f)
        (λ a′ p → J
          (λ a a′ p →
            split-path (merge-path {inl a} {inl a′} (lift p)) ≡ lift p)
          (λ _ → refl) _ _ (lower p))
        (λ _ → 0-elim _ ∘ lower)
        y)
      (λ b y → case
        (λ y → (f : F (inr b) y) →
          split-path (merge-path {inr b} {y} f) ≡ f)
        (λ _ → 0-elim _ ∘ lower)
        (λ b′ p → J
          (λ b b′ p →
            split-path (merge-path {inr b} {inr b′} (lift p)) ≡ lift p)
          (λ _ → refl) _ _ (lower p))
        y)
      x y f)
  , (merge-path , λ p → J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (λ x → case
        (λ x → merge-path {x} {x} (split-path {x} {x} refl) ≡ refl)
        (λ _ → refl)
        (λ _ → refl)
        x)
      x y p)
