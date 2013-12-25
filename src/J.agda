{-# OPTIONS --without-K #-}
open import Types

module J {a c} {A : Set a} (C : (x y : A) → x ≡ y → Set c) where

open import GrupoidStructure
open import PathOperations
open import PathStructure.Id.Tr
open import PathStructure.Sigma

γ : {x y : A} (p : x ≡ y) →
  Id (Σ A λ y → x ≡ y) (x , refl) (y , p)
γ p = merge-path (p , tr-post _ p refl · id·p _)

justification : {x y : A} (p : x ≡ y) → C x x refl → C x y p
justification p = tr (λ z → C _ (π₁ z) (π₂ z)) (γ p)
