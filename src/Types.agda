{-# OPTIONS --without-K #-}
module Types where

open import Level
  using (_⊔_; Lift; lift; lower)
  public

infix  1 _≡_
infixr 1 _⊎_
infixr 2 _×_
infix  3 ¬_
infixr 4 _,_
infixr 9 _∘_

-- The negative fragment.
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    π₁ : A
    π₂ : B π₁

open Σ public
-- Projections are defined automatically.

_×_ : ∀ {a b} → Set a → Set b → Set _
A × B = Σ A λ _ → B

-- Unit type with definitional η.
record ⊤ : Set where
  constructor tt

id : ∀ {a} {A : Set a} → A → A
id x = x

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ a → B a → Set c}
  (f : ∀ {a} (b : B a) → C a b)
  (g : ∀ a → B a) →
  ∀ x → C x (g x)
(f ∘ g) x = f (g x)

-- The positive fragment.
data ⊥ : Set where

-- Ex falso quodlibet.
0-elim : ∀ {p} {P : Set p} → ⊥ → P
0-elim ()

¬_ : ∀ {a} → Set a → Set a
¬ A = A → ⊥

-- Unit type without definitional η.
data Unit : Set where
  tt : Unit

1-elim : ∀ {p} (P : Unit → Set p) → P tt →
  ∀ z → P z
1-elim P c tt = c

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Case analysis.
case : ∀ {a b p} {A : Set a} {B : Set b} (P : A ⊎ B → Set p)
  (f : ∀ a → P (inl a)) (g : ∀ b → P (inr b)) → ∀ z → P z
case P f g (inl a) = f a
case P f g (inr b) = g b

-- Simga as a positive type.
data Σ′ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  _,_ : (a : A) → B a → Σ′ A B

split : ∀ {a b p} {A : Set a} {B : A → Set b} (P : Σ′ A B → Set p)
  (f : (a : A) (b : B a) → P (a , b)) → ∀ z → P z
split P f (a , b) = f a b

-- Natural numbers.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ind : ∀ {p} (P : ℕ → Set p)
  (s : ∀ n → P n → P (suc n))
  (z : P zero) →
  ∀ z → P z
ind P s z zero    = z
ind P s z (suc n) = s n (ind P s z n)

-- Identity type.
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- When the type cannot be infered.
Id : ∀ {a} (A : Set a) (x y : A) → Set _
Id _ x y = x ≡ y

-- Path induction.
J : ∀ {a p} {A : Set a} (P : ∀ (x : A) y → x ≡ y → Set p)
  (f : ∀ x → P x x refl) → ∀ x y → (p : x ≡ y) → P x y p
J P f x .x refl = f x
