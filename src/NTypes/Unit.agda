{-# OPTIONS --without-K #-}
module NTypes.Unit where

open import Equivalence
open import NTypes
open import PathStructure.Unit
open import Types

1-isProp : isProp ⊤
1-isProp _ _ = merge-path _

1-isSet : isSet ⊤
1-isSet x y p q =
  prop-eq (sym-equiv split-merge-eq) 1-isProp p q
