-- This interface from Haskell base should be moved to the agda2hs prelude
module Data.Bits where

open import Haskell.Prelude

record Bits (a : Set) ⦃ _ : Eq a ⦄ : Set where
  field
    _&_        : a → a → a
    _∣_        : a → a → a
    xor        : a → a → a
    complement : a → a

    shiftL     : a → Int → a
    shiftR     : a → Int → a

    bit        : Int → a
    setBit     : a → Int → a
    testBit    : a → Int → Bool
{-# COMPILE AGDA2HS Bits existing-class #-}

open Bits ⦃...⦄ public  

postulate instance
  iBitsInteger : Bits Integer

-- those should be moved to a lawful bits interface
postulate
  testBitShift  : (i : Integer) → IsFalse (testBit (shiftL i 1) 0)
  testBitsetBit : (i : Integer) {n : Int} → IsTrue (testBit (setBit i n) n)
  shiftRshiftL  : (i : Integer) {n : Int}
                → shiftR (shiftL i n) n ≡ i
  shiftsetshift : (i : Integer) → shiftR (setBit (shiftL i 1) 0) 1 ≡ i
  testBit0      : IsFalse (testBit 0 0)
  shiftR0       : ∀ {n} → shiftR 0 n ≡ 0
