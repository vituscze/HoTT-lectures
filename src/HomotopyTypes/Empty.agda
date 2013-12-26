{-# OPTIONS --without-K #-}
module HomotopyTypes.Empty where

open import HomotopyTypes
open import Types

0-isSet : isSet ⊥
0-isSet x = 0-elim _ x
