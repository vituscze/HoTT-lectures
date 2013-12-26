{-# OPTIONS --without-K #-}
module HomotopyTypes where

open import Equivalence
open import PathOperations
open import PathStructure.Coproduct as PCoproduct
open import PathStructure.Product   as PProduct
open import PathStructure.Sigma     as PSigma
open import PathStructure.Unit      as PUnit
open import Transport
open import Types

isProp : ∀ {a} → Set a → Set _
isProp A = (x y : A) → x ≡ y

isSet : ∀ {a} → Set a → Set _
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q

set→id-prop : ∀ {a} {A : Set a} →
  isSet A → {x y : A} → isProp (x ≡ y)
set→id-prop A-set p q = A-set _ _ p q

id-prop→set : ∀ {a} {A : Set a} →
  ({x y : A} → isProp (x ≡ y)) → isSet A
id-prop→set f _ _ p q = f p q

prop-eq : ∀ {a b} {A : Set a} {B : Set b} → A ≃ B → isProp A → isProp B
prop-eq (f , (g , α) , (h , β)) A-prop x y =
  tr id
    ( ap (λ z → z ≡ f (g y)) (α x)
    · ap (λ z → x ≡ z)       (α y)
    )
    (ap f (A-prop (g x) (g y)))

1-isProp : isProp ⊤
1-isProp _ _ = PUnit.merge-path _

1-isSet : isSet ⊤
1-isSet x y p q =
  prop-eq (sym-equiv PUnit.split-merge-eq) 1-isProp p q

0-isSet : isSet ⊥
0-isSet x = 0-elim _ x

×-isSet : ∀ {a b} {A : Set a} {B : Set b} →
  isSet A → isSet B → isSet (A × B)
×-isSet A-set B-set x y p q
  = split-eq p ⁻¹
  · ap (λ y → ap₂ _,_ y (ap π₂ p))
    (A-set _ _ (ap π₁ p) (ap π₁ q))
  · ap (λ y → ap₂ _,_ (ap π₁ q) y)
    (B-set _ _ (ap π₂ p) (ap π₂ q))
  · split-eq q
  where
  split-eq : (p : x ≡ y) → ap₂ _,_ (ap π₁ p) (ap π₂ p) ≡ p
  split-eq = π₂ (π₂ (π₂ PProduct.split-merge-eq))

Σ-isSet : ∀ {a b} {A : Set a} {B : A → Set b} →
  isSet A → (∀ x → isSet (B x)) → isSet (Σ A B)
Σ-isSet {A = A} {B = B} A-set B-set x y p q
  = split-eq p ⁻¹
  · ap₂-dep-eq {B = B} _,_
      (ap π₁ p)
      (ap π₁ q)
      π₁-eq
      (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p)
      (tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q)
      π₂-eq
  · split-eq q
  where
  split-eq : (p : x ≡ y) →
    ap₂-dep {B = B} _,_ (ap π₁ p)
      (tr-∘ π₁ p (π₂ x) ⁻¹  · dap π₂ p) ≡ p
  split-eq = π₂ (π₂ (π₂ PSigma.split-merge-eq))

  π₁-eq : ap π₁ p ≡ ap π₁ q
  π₁-eq = A-set _ _ (ap π₁ p) (ap π₁ q)

  π₂-eq : tr (λ z → tr B z (π₂ x) ≡ π₂ y) π₁-eq
            (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p)
        ≡ tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q
  π₂-eq = B-set _ (tr B (ap π₁ q) (π₂ x)) (π₂ y)
    (tr
      (λ z → tr B z (π₂ x) ≡ π₂ y)
      π₁-eq
      (tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p))
    (tr-∘ π₁ q (π₂ x) ⁻¹ · dap π₂ q)

⊎-isSet : ∀ {A : Set} {B : Set} →
  isSet A → isSet B → isSet (A ⊎ B)
⊎-isSet {A = A} {B = B} A-set B-set x y p q =
  case (λ x → (y : A ⊎ B) (p q : x ≡ y) → p ≡ q)
  (λ a y p q → case
    (λ y → (p q : inl a ≡ y) → p ≡ q)
    (λ a′ p q
      → split-eq p ⁻¹
      · ap (ap inl)
        (A-set _ _
          (lower (tr (F (inl a)) p (lift refl)))
          (lower (tr (F (inl a)) q (lift refl)))
        )
      · split-eq q
      )
    (λ _  p q → 0-elim _
      (lower (PCoproduct.split-path p)))
    y p q)
  (λ b y p q → case
    (λ y → (p q : inr b ≡ y) → p ≡ q)
    (λ _  p q → 0-elim _
      (lower (PCoproduct.split-path p)))
    (λ b′ p q → split-eq p ⁻¹
      · ap (ap inr)
        (B-set _ _
          (lower (tr (F (inr b)) p (lift refl)))
          (lower (tr (F (inr b)) q (lift refl)))
        )
      · split-eq q
      )
    y p q)
  x y p q
  where
  split-eq : {x y : A ⊎ B} → _
  split-eq {x = x} {y = y} =
    π₂ (π₂ (π₂ (PCoproduct.split-merge-eq {x = x} {y = y})))
