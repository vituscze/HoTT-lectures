{-# OPTIONS --without-K #-}
module HIT.Interval where

open import PathOperations
open import PathStructure.Id.Tr
open import Types

module I-Definition where
  private
    data #I : Set where
      #0 : #I
      #1 : #I

  I : Set
  I = #I

  0ᵢ : I
  0ᵢ = #0

  1ᵢ : I
  1ᵢ = #1

  postulate
    seg : 0ᵢ ≡ 1ᵢ

  I-rec : ∀ {p} (P : I → Set p)
    (xₒ : P 0ᵢ) (x₁ : P 1ᵢ) (p : tr P seg xₒ ≡ x₁) →
    ∀ i → P i
  I-rec P xₒ x₁ p #0 = xₒ
  I-rec P xₒ x₁ p #1 = x₁

  postulate
    I-β : ∀ {p} (P : I → Set p)
      (xₒ : P 0ᵢ) (x₁ : P 1ᵢ)
      (p : tr P seg xₒ ≡ x₁) →
      apd (I-rec P xₒ x₁ p) seg ≡ p

open I-Definition public

from-path-space : ∀ {a} {A : Set a} →
  (Σ A λ x → Σ A λ y → x ≡ y) → I → A
from-path-space z = I-rec _
  (π₁ z)
  (π₁ (π₂ z))
  (tr id (tr-≡ seg ⁻¹) (π₂ (π₂ z)))

to-path-space : ∀ {a} {A : Set a} →
  (I → A) → Σ A λ x → Σ A λ y → x ≡ y
to-path-space f = f 0ᵢ , f 1ᵢ , ap f seg
