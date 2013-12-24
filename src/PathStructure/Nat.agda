module PathStructure.Nat where

open import Equivalence
open import PathOperations
open import Types

F : ℕ → ℕ → Set
F m n = ind (λ _ → ℕ → Set)
  (λ _ r n → ind (λ _ → Set) (λ n-1 _ → r n-1) ⊥ n)
  (λ     n → ind (λ _ → Set) (λ _   _ → ⊥)     ⊤ n)
  m n

F-lemma : ∀ n → F n n
F-lemma n = ind (λ n → F n n) (λ _ f → f) _ n

-- Explicit arguments to prevent code littered with curly brackets.
split-path : ∀ x y → x ≡ y → F x y
split-path x _ p = tr (F x) p (F-lemma x)

merge-path : ∀ x y → F x y → x ≡ y
merge-path _ _ f = ind
  (λ x → ∀ y → F x y → x ≡ y)
  (λ x r y → ind
    (λ y → F (suc x) y → suc x ≡ y)
    (λ _ _ f → ap suc (r _ f))
    (0-elim _)
    y)
  (λ y → ind
    (λ y → F zero y → zero ≡ y)
    (λ _ _ → 0-elim _)
    (λ _ → refl)
    y)
  _ _ f

-- Lemmas.
ap-refl : ∀ {n} (p : n ≡ n) → p ≡ refl →
  ap suc p ≡ refl
ap-refl _ = J
  (λ p q _ → J (λ x y _ → suc x ≡ suc y) (λ _ → refl) _ _ p ≡ ap suc q)
  (λ _ → refl) _ refl

tr-ap : ∀ m n (f : F m n) →
    tr (F (suc m))       (ap suc (merge-path m n f)) (F-lemma (suc m))
  ≡ tr (F (suc m) ∘ suc)         (merge-path m n f)  (F-lemma (suc m))
tr-ap m n f = J
  (λ x y p → tr (F (suc x))       (ap suc p) (F-lemma (suc x))
           ≡ tr (F (suc x) ∘ suc)         p  (F-lemma (suc x)))
  (λ _ → refl)
  _ _ (merge-path m n f)

split-merge-eq : ∀ {x y} → (x ≡ y) ≃ F x y
split-merge-eq {x = x} {y = y}
  = split-path _ _
  , (merge-path _ _ , λ f → ind
      (λ x → ∀ y (f : F x y) → split-path x y (merge-path x y f) ≡ f)
      (λ x r y f → ind
        (λ y → (f : F (suc x) y) →
          split-path (suc x) y (merge-path (suc x) y f) ≡ f)
        (λ y _ f → tr-ap x y f · r y f)
        (λ b → 0-elim _ b)
        y f)
      (λ y f → ind
        (λ y → (f : F zero y) →
          split-path zero y (merge-path zero y f) ≡ f)
        (λ _ _ b → 0-elim _ b)
        (λ _ → refl)
        y f)
      x y f)
  , (merge-path _ _ , λ p → J
      (λ _ _ p → merge-path _ _ (split-path _ _ p) ≡ p)
      (λ x → ind
        (λ x → merge-path x x (split-path x x refl) ≡ refl)
        (λ _ → ap-refl _)
        refl
        x)
      _ _ p)
