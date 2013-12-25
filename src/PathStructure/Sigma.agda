{-# OPTIONS --without-K #-}
module PathStructure.Sigma {a b} {A : Set a} {B : A → Set b} where

open import Equivalence
open import PathOperations
open import Transport
open import Types

ap₂-dep : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
  {x x′ : A} {y : B x} {y′ : B x′}
  (f : (a : A) (b : B a) → C) (p : x ≡ x′) (q : tr B p y ≡ y′) →
  f x y ≡ f x′ y′
ap₂-dep {B = B} f p q = J
  (λ x x′ p → (y : B x) (y′ : B x′) (q : tr B p y ≡ y′) → f x y ≡ f x′ y′)
  (λ x _ _ q → ap (f x) q)
  _ _ p _ _ q

ap₂-dep-eq : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Set c}
  (f : (x : A) → B x → C)
  {x x′ : A} (p p′ : x ≡ x′) (pp : p ≡ p′)
  {y : B x} {y′ : B x′} (q : tr B p y ≡ y′) (q′ : tr B p′ y ≡ y′)
  (qq : tr (λ z → tr B z y ≡ y′) pp q ≡ q′) →
  ap₂-dep f p q ≡ ap₂-dep f p′ q′
ap₂-dep-eq {B = B} f {x = x} {x′ = x′} p p′ pp q q′ qq = J
  (λ p p′ pp → (y : B x) (y′ : B x′)
    (q : tr B p y ≡ y′) (q′ : tr B p′ y ≡ y′)
    (qq : tr (λ z → tr B z y ≡ y′) pp q ≡ q′) →
    ap₂-dep f p q ≡ ap₂-dep f p′ q′)
  (λ p _ _ q q′ qq → J
    (λ q q′ qq → ap₂-dep f p q ≡ ap₂-dep f p q′)
    (λ _ → refl)
    _ _ qq)
  _ _ pp _ _ _ _ qq

split-path : {x y : Σ A B} →
  x ≡ y → Σ (π₁ x ≡ π₁ y) (λ p → tr B p (π₂ x) ≡ π₂ y)
split-path {x = x} p = ap π₁ p , tr-∘ π₁ p (π₂ x) ⁻¹ · dap π₂ p

merge-path : {x y : Σ A B} →
  Σ (π₁ x ≡ π₁ y) (λ p → tr B p (π₂ x) ≡ π₂ y) → x ≡ y
merge-path pq = ap₂-dep _,_ (π₁ pq) (π₂ pq)

split-merge-eq : {x y : Σ A B} →
  (x ≡ y) ≃ Σ (π₁ x ≡ π₁ y) (λ p → tr B p (π₂ x) ≡ π₂ y)
split-merge-eq
  = split-path
  , (merge-path , λ pq → J
      (λ x x′ p → (y : B x) (y′ : B x′) (q : tr B p y ≡ y′) →
        split-path (merge-path (p , q)) ≡ p , q)
      (λ x y y′ q → J {A = B x}
        (λ _ _ q → split-path (merge-path (refl , q)) ≡ refl , q)
        (λ _ → refl) _ _ q)
      _ _ (π₁ pq) _ _ (π₂ pq))
  , (merge-path , λ p → J
      (λ _ _ p → merge-path (split-path p) ≡ p)
      (λ _ → refl) _ _ p)
