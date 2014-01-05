{-# OPTIONS --without-K #-}
module K where

open import NTypes.Contractible
open import PathOperations
open import PathStructure.Sigma
open import Types

-- Not strictly related to the lectures.
--
-- Here we show that the various forms of extending
-- pure ITT to propositionally extensional TT are
-- (logically) equivalent.

-- The most general form of axiom K.
K-gen : ∀ a p → Set _
K-gen a p = {A : Set a} (x : A) (P : x ≡ x → Set p) (h : x ≡ x) →
  P refl → P h

-- Specialized form of axiom K.
K : ∀ a → Set _
K a = {A : Set a} (x : A) (p : x ≡ x) → p ≡ refl

uip : ∀ a → Set _
uip a = {A : Set a} (x y : A) (p q : x ≡ y) → p ≡ q

π₂-Id : ∀ a b → Set _
π₂-Id a b = {A : Set a} {B : A → Set b} (a : A) (b₁ b₂ : B a) →
  Id (Σ A B) (a , b₁) (a , b₂) → b₁ ≡ b₂


-- Relation between K and its specialized version.
K-gen→K : ∀ {a} → K-gen a a → K a
K-gen→K K x p = K x (λ p → p ≡ refl) p refl

K→K-gen : ∀ {a p} → K a → K-gen a p
K→K-gen K x P h p = tr P (K x h ⁻¹) p

-- Relation between K and UIP.
K→uip : ∀ {a} → K a → uip a
K→uip K x y p q = J (λ _ _ p → ∀ q → q ≡ p) K _ _ q p

uip→K : ∀ {a} → uip a → K a
uip→K uip x p = uip x x p refl

-- Relation between K and π₂-Id.
K→π₂-Id : ∀ {a b} → K a → π₂-Id a b
K→π₂-Id K {B = B} _ b₁ b₂ p = tr
  (λ z → tr B z b₁ ≡ b₂)
  (K _ (π₁ (split-path p)))
  (π₂ (split-path p))

π₂-Id→K : ∀ {a} → π₂-Id a a → K a
π₂-Id→K πId x p =
  πId x p refl (π₂ (pp-space-contr x) (x , p) ⁻¹)
