{-# OPTIONS --without-K #-}
module Fiber where

open import Equivalence
open import NTypes.Contractible
open import PathOperations
open import Types

fib : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) (y : B) →
  Set _
fib {A = A} f y = Σ A λ x → f x ≡ y

fib→dom : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
  Σ B (fib f) → A
fib→dom f (b , a , p) = a

dom→fib : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
  A → Σ B (fib f)
dom→fib f a = f a , a , refl

fib-dom-eq :  ∀ {a b} {A : Set a} {B : Set b} (f : A → B) →
  Σ B (fib f) ≃ A
fib-dom-eq {A = A} {B = B} f
  = fib→dom f
  , (dom→fib f , λ _ → refl)
  , (dom→fib f , λ {(b , a , p) →
      ap (swap ∘ _,_ a) (π₂ (pp-space-contr (f a)) (b , p))})
  where
  swap : (Σ A λ x → Σ B λ y → f x ≡ y) → Σ B (fib f)
  swap (b , a , p) = a , b , p
