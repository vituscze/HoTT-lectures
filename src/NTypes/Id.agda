{-# OPTIONS --without-K #-}
module NTypes.Id where

open import GroupoidStructure
open import NTypes
open import PathOperations
open import Transport
open import Types

-- This should also be derivable from hLevel-suc from
-- HomotopyTypes.HLevel module.
Id-isSet : ∀ {a} {A : Set a} {x y : A} →
  isSet A → isSet (x ≡ y)
Id-isSet {x = x} {y = y} A-set _ _ pp qq
  = path pp ⁻¹ · path qq
  where
  split-path : {p q : x ≡ y} (pp : p ≡ q) →
    A-set _ _ p q ≡ pp · A-set _ _ q q
  split-path pp = J
    (λ p q pp → A-set _ _ p q ≡ pp · A-set _ _ q q)
    (λ _ → refl) _ _ pp

  path : {p q : x ≡ y} (pp : p ≡ q) →
    A-set _ _ p q ≡ pp
  path pp = J
    (λ p q pp → A-set _ _ p q ≡ pp)
    (λ p → split-path (A-set _ _ p p ⁻¹) · p⁻¹·p (A-set _ _ p p))
    _ _ pp

-- From the lectures.
Id-isSet-alt : ∀ {a} {A : Set a} {u v : A} →
  isSet A → isSet (u ≡ v)
Id-isSet-alt {u = u} {v = v} H r s α β
  = id·p α ⁻¹
  · ap (λ z → z · α)
    (p⁻¹·p (H′ r)) ⁻¹
  · p·q·r (H′ r ⁻¹) (H′ r) α ⁻¹
  · ap (λ z → H′ r ⁻¹ · z)
    ( tr-post r α (H′ r) ⁻¹
    · dap H′ α
    · dap H′ β ⁻¹
    · tr-post r β (H′ r)
    )
  · p·q·r (H′ r ⁻¹) (H′ r) β
  · ap (λ z → z · β)
    (p⁻¹·p (H′ r))
  · id·p β
  where
    H′ = λ q → H u v r q
