module FunExt where

open import HIT.Interval
open import PathOperations
open import PathStructure.Id.Tr
open import Types

funext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  (∀ x → f x ≡ g x) → f ≡ g
funext {A = A} {B = B} {f = f} {g = g} p = ap h seg
  where
    h : I → (x : A) → B x
    h i x = I-rec (λ _ → B x)
      (f x) (g x) (tr id (tr-≡ seg ⁻¹) (p x)) i
