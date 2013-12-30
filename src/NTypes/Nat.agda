{-# OPTIONS --without-K #-}
module NTypes.Nat where

open import NTypes
open import PathOperations
open import PathStructure.Nat
open import Types

ℕ-isSet : isSet ℕ
ℕ-isSet = ind
  (λ m → (n : ℕ) (p q : m ≡ n) → p ≡ q)
  (λ m-1 r → ind (λ n → (p q : suc m-1 ≡ n) → p ≡ q)
    (λ n-1 r′ p′ q′
      → split-eq p′ ⁻¹
      · ap (ap suc)
        (r _
          (merge-path m-1 n-1
            (tr (F (suc m-1)) p′ (F-lemma (suc m-1))))
          (merge-path m-1 n-1
            (tr (F (suc m-1)) q′ (F-lemma (suc m-1)))))
      · split-eq q′
      )
    (λ p q → split-eq p ⁻¹ · split-eq q))
  (ind (λ n → (p q : 0 ≡ n) → p ≡ q)
    (λ _ _ p q → split-eq p ⁻¹ · split-eq q)
    (λ     p q → split-eq p ⁻¹ · split-eq q))
  where
  split-eq : {x y : ℕ} → _
  split-eq {x} {y} = π₂ (π₂ (π₂ (split-merge-eq {x} {y})))
