{-# OPTIONS --no-erase-record-parameters #-}
module Haskell.Law.Num where

open import Haskell.Prim
open import Haskell.Prelude using (Num)

record LawfulNum (a : Set) ⦃ iNum : Num a ⦄ : Set where
  open Num iNum
  field
    +-assoc     : ∀ x y z → x + (y + z) ≡ (x + y) + z
    +-sym       : ∀ x y → x + y ≡ y + x
    +-identityₗ : ∀ x → 0 + x ≡ x
    +-identityᵣ : ∀ x → x + 0 ≡ x

postulate instance
  iIntegerLawfulNum : LawfulNum Integer
  
