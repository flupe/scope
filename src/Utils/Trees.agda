module Utils.Trees where

open import Haskell.Prelude
open import Utils.Bin
open import Utils.BinInt


add  : BinInt → BinInt → BinInt
add x y = case (view x , view y) of λ where
  (VZ    , _    ) → y
  (_     , VZ   ) → x
  (VO x' , VO y') → o (add x' y')
  (VO x' , VI y') → i (add x' y')
  (VI x' , VO y') → i (add x' y')
  (VI x' , VI y') → o (add anything y')
{-# COMPILE AGDA2HS add #-}

data Tree (a : Set) : @0 Nat → Set where
  Leaf : a → Tree a 0
  Node : ∀ {@0 n} (l r : Tree a n) → Tree a (1 + n)
{-# COMPILE AGDA2HS Tree #-}

data RAList' (a : Set) : @0 Bin → @0 Nat → Set where
  RALZ : ∀ {@0 n}                                    → RAList' a (Z  ) n
  RALO : ∀ {@0 n b}            → RAList' a b (suc n) → RAList' a (O b) n
  RALI : ∀ {@0 n b} → Tree a n → RAList' a b (suc n) → RAList' a (I b) n
{-# COMPILE AGDA2HS RAList' #-}

RAList : Set → @0 BinInt → Set
RAList a bi = RAList' a (bin bi) 0
{-# COMPILE AGDA2HS RAList #-}
