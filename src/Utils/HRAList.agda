module Utils.HRAList where

open import Haskell.Prelude hiding (a; b)

open import Utils.Misc
open import Utils.Bin
open import Utils.BinInt
open import Utils.Tree
open import Utils.RAList

private variable
  @0 a : Set
  @0 b : Bin
  @0 n : Nat

-- | ornamented BinTree
data HBinTree (p : @0 a → Set) : @0 BinTree a n → Set where
  HLeaf : {@0 x : a} → p x → HBinTree p (Leaf x)
  HNode : {@0 l r : BinTree a n}
        → HBinTree p l
        → HBinTree p r
        → HBinTree p (Node l r)
{-# COMPILE AGDA2HS HBinTree #-}

-- | ornamented RAList
data HRAList' (p : @0 a → Set) : @0 RAList' a b n → Set where
  HRALZ : HRAList' p {n = n} RALZ
  HRALO : {@0 xs : RAList' a b (suc n)}            → HRAList' p xs → HRAList' p (RALO xs)
  HRALI : {@0 xs : RAList' a b (suc n)} {@0 t : BinTree a n} → HBinTree p t → HRAList' p xs → HRAList' p (RALI t xs)
{-# COMPILE AGDA2HS HRAList' #-}
