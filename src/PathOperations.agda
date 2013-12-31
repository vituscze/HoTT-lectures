{-# OPTIONS --without-K #-}
module PathOperations where

open import Types

infixr 4 _·_
infix  9 _⁻¹

_⁻¹ : ∀ {a} {A : Set a} {x y : A} →
  x ≡ y → y ≡ x
_⁻¹ = J (λ x y _ → y ≡ x) (λ _ → refl) _ _

_·_ : ∀ {a} {A : Set a} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
_·_ {z = z} = J (λ x y _ → y ≡ z → x ≡ z) (λ _ p′ → p′) _ _

tr : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} (p : x ≡ y) →
  P x → P y
tr P = J (λ x y _ → P x → P y) (λ _ x → x) _ _

ap : ∀ {a b} {A : Set a}  {B : Set b} {x y : A} (f : A → B) →
  x ≡ y → f x ≡ f y
ap f = J (λ x y _ → f x ≡ f y) (λ _ → refl) _ _

ap₂ : ∀ {a b c} {A : Set a}  {B : Set b} {C : Set c}
  {x x′ y y′} (f : A → B → C) (p : x ≡ x′) (q : y ≡ y′) →
  f x y ≡ f x′ y′
ap₂ f p q = ap (λ _ → f _ _) p · ap (f _) q

apd : ∀ {a b} {A : Set a} {B : A → Set b} {x y : A}
  (f : ∀ a → B a) (p : x ≡ y) →
  tr B p (f x) ≡ f y
apd {B = B} f = J
  (λ x y p → tr B p (f x) ≡ f y)
  (λ _ → refl) _ _

happly : ∀ {a b} {A : Set a} {B : A → Set b} {f g : (x : A) → B x} →
  f ≡ g → ∀ x → f x ≡ g x
happly p x = ap (λ f → f x) p
