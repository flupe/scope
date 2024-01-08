module Utils.Tree where

open import Haskell.Prelude
open import Utils.Bin
open import Utils.BinInt

-- | Complete binary tree of depth @n@
data BinTree (a : Set) : @0 Nat → Set where
  Leaf : a → BinTree a 0
  Node : ∀ {@0 n} (l r : BinTree a n) → BinTree a (suc n)
{-# COMPILE AGDA2HS BinTree #-}

data @0 TreePath : Nat → Bin → Set where
  instance
    here  : TreePath 0 Z
    left  : ∀ {@0 n b} → @0 ⦃ TreePath n b ⦄ → TreePath (suc n) (O b)
    right : ∀ {@0 n b} → @0 ⦃ TreePath n b ⦄ → TreePath (suc n) (I b)

@0 predPathO : ∀ {n b} → TreePath (suc n) (O b) → TreePath n b
predPathO (left ⦃ p ⦄) = p

@0 predPathI : ∀ {n b} → TreePath (suc n) (I b) → TreePath n b
predPathI (right ⦃ p ⦄) = p

record BinPath (@0 n : Nat) : Set where
  constructor BP
  field
    bint    : BinInt
    @0 path : TreePath n (bint .bin)
open BinPath public
{-# COMPILE AGDA2HS BinPath unboxed #-}

lookupBinTree : ∀ {a} {@0 n} → BinPath n → BinTree a n → a
lookupBinTree bp (Leaf x  ) = x
lookupBinTree (BP bi p) (Node l r) =
  case view bi of λ where
    (VO bi) → lookupBinTree (BP bi (predPathO p)) l
    (VI bi) → lookupBinTree (BP bi (predPathI p)) r
{-# COMPILE AGDA2HS lookupBinTree #-}
