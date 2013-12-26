{-# OPTIONS --without-K #-}
module HomotopyTypes.HLevel where

open import GroupoidStructure
open import HomotopyTypes
open import HomotopyTypes.Contractible
open import PathOperations
open import Types

hLevel : ℕ → ∀ {a} → Set a → Set a
hLevel n = ind (λ _ → Set _ → Set _)
  (λ _ r A → (x y : A) → r (x ≡ y))
  isContr
  n

isProp→hLevel1 : ∀ {a} {A : Set a} →
  isProp A → hLevel 1 A
isProp→hLevel1 {A = A} A-prop x y
  = A-prop x y
  , path
  where
  split-path : {x y : A} (p : x ≡ y) →
    A-prop x y ≡ p · A-prop y y
  split-path p = J
    (λ x y p → A-prop x y ≡ p · A-prop y y)
    (λ _ → refl) _ _ p

  path : {x y : A} (p : x ≡ y) → A-prop x y ≡ p
  path p = J
    (λ x y p → A-prop x y ≡ p)
    (λ x → split-path (A-prop x x ⁻¹) · p⁻¹·p (A-prop x x))
    _ _ p

hLevel-suc : ∀ n {a} {A : Set a} →
  hLevel n A → hLevel (suc n) A
hLevel-suc n h = ind
  (λ n → ∀ {A} → hLevel n A → hLevel (suc n) A)
  (λ _ r h x y → r (h x y))
  (λ     h → isProp→hLevel1 λ x y → π₂ h x ⁻¹ · π₂ h y)
  n h
