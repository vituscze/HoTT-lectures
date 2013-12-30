{-# OPTIONS --without-K #-}
module NTypes.HedbergsTheorem where

open import GroupoidStructure
open import NTypes
open import NTypes.Negation
open import PathOperations
open import Transport
open import Types

stable : ∀ {a} → Set a → Set a
stable A = ¬ ¬ A → A

dec : ∀ {a} → Set a → Set a
dec A = A ⊎ ¬ A

dec→stable : ∀ {a} {A : Set a} → dec A → stable A
dec→stable {A = A} dec = case (λ _ → stable A)
  (λ  a   _ → a)
  (λ ¬a ¬¬a → 0-elim _ (¬¬a ¬a))
  dec

dec-eq : ∀ {a} → Set a → Set a
dec-eq A = (x y : A) → dec (x ≡ y)

stable-eq : ∀ {a} → Set a → Set a
stable-eq A = (x y : A) → stable (x ≡ y)

dec-eq→stable-eq : ∀ {a} {A : Set a} → dec-eq A → stable-eq A
dec-eq→stable-eq dec x y = dec→stable (dec x y)

-- Lemma 2.9.6 from HoTT book.
lemma : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
  {x y : A} (p : x ≡ y) (f : B x → C x) (g : B y → C y) →
  tr _ p f ≡ g → (b : B x) → tr _ p (f b) ≡ g (tr _ p b)
lemma {B = B} {C = C} p f g f≡g = J
  (λ x y p → (f : B x → C x) (g : B y → C y) →
    tr _ p f ≡ g → (b : B x) → tr _ p (f b) ≡ g (tr _ p b))
  (λ _ _ _ → happly) _ _ p f g f≡g

stable-eq→set : ∀ {a} {A : Set a} → stable-eq A → isSet A
stable-eq→set {A = A} h x y p q = J
  (λ x y p → (q : x ≡ y) → q ≡ p)
  K _ _ q p
  where
  K : (x : A) (p : x ≡ x) → p ≡ refl
  K x p
    = id·p _ ⁻¹
    · ap (λ z → z · p)
      (p⁻¹·p (h x x r)) ⁻¹
    · p·q·r (h x x r ⁻¹) (h x x r) p ⁻¹
    · ap (λ z → h x x r ⁻¹ · z)
      ( tr-post x p (h x x r) ⁻¹
      · lemma p (h x x) (h x x) (dap (h x) p) r
      · ap (h x x)
        (¬-isProp (tr (λ v → ¬ ¬ (x ≡ v)) p r) r)
      )
    · p⁻¹·p (h x x r)
    where
    -- Choice of r doesn't matter.
    r : ¬ ¬ (x ≡ x)
    r = λ z → z refl
