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

  I-ind : ∀ {p} (P : I → Set p)
    (x₀ : P 0ᵢ) (x₁ : P 1ᵢ) (p : tr P seg x₀ ≡ x₁) →
    ∀ i → P i
  I-ind P x₀ x₁ p #0 = x₀
  I-ind P x₀ x₁ p #1 = x₁

  postulate
    I-β-i : ∀ {p} (P : I → Set p)
      (x₀ : P 0ᵢ) (x₁ : P 1ᵢ)
      (p : tr P seg x₀ ≡ x₁) →
      apd (I-ind P x₀ x₁ p) seg ≡ p

  I-rec : ∀ {p} {P : Set p}
    (x₀ x₁ : P) (p : x₀ ≡ x₁)
    (i : I) → P
  I-rec x₀ x₁ p #0 = x₀
  I-rec x₀ x₁ p #1 = x₁

  postulate
    I-β-r : ∀ {p} {P : Set p}
      (x₀ x₁ : P) (p : x₀ ≡ x₁) →
      ap (I-rec x₀ x₁ p) seg ≡ p

open I-Definition public

from-path-space : ∀ {a} {A : Set a} →
  (Σ A λ x → Σ A λ y → x ≡ y) → I → A
from-path-space (x , y , p) = I-rec x y p

to-path-space : ∀ {a} {A : Set a} →
  (I → A) → Σ A λ x → Σ A λ y → x ≡ y
to-path-space f = f 0ᵢ , f 1ᵢ , ap f seg
