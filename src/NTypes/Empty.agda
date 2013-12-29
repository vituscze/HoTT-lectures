{-# OPTIONS --without-K #-}
module NTypes.Empty where

open import NTypes
open import Types

0-isSet : isSet ⊥
0-isSet x = 0-elim _ x
