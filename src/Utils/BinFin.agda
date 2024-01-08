module Utils.BinFin where

open import Haskell.Prelude hiding (s)
open import Utils.Misc
open import Utils.BinNat
open import  Haskell.Prim using (ltNat)

record BinFin (@0 n : Nat) : Set where
  constructor BF
  field
    bint     : BinNat
    @0 bound : IsTrue (ltNat (BinNat.nat bint) n)

fz : ∀ {@0 n} → BinFin (suc n)
fz = BF z {!!}

fs : ∀ {@0 n} → BinFin n → BinFin (suc n)
fs bf = BF (s (BinFin.bint bf)) (BinFin.bound bf)

data FinView : ∀ {@0 n} → @0 BinFin n → Set where
  Z :                            FinView (fz {0})
  S : ∀ {@0 n} (bf : BinFin n) → FinView (fs bf)
