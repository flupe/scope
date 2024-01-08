module Utils.RAList where

open import Haskell.Prim using (it)
open import Haskell.Prelude
open import Haskell.Law.Equality
open import Haskell.Extra.Refinement

open import Utils.Bin
open import Utils.BinInt
open import Utils.Tree
-- open import Data.Bits


data RAList' (a : Set) : @0 Bin → @0 Nat → Set where
  RALZ : ∀ {@0 n}                                       → RAList' a (Z  ) n
  RALO : ∀ {@0 n b}               → RAList' a b (suc n) → RAList' a (O b) n
  RALI : ∀ {@0 n b} → BinTree a n → RAList' a b (suc n) → RAList' a (I b) n
{-# COMPILE AGDA2HS RAList' #-}

insertBinTree : ∀ {a} {@0 b n} → BinTree a n → RAList' a b n → RAList' a (bsucc b) n
insertBinTree t RALZ        = RALI t RALZ
insertBinTree t (RALO xs)   = RALI t xs
insertBinTree t (RALI x xs) = RALO (insertBinTree (Node x t) xs)
{-# COMPILE AGDA2HS insertBinTree #-}

concatRAList  : ∀ {a} {@0 b₁ b₂ n} → RAList' a b₁ n → RAList' a b₂ n → RAList' a (badd b₁ b₂) n
concatRAList' : ∀ {a} {@0 b₁ b₂ n} → RAList' a b₁ n → RAList' a b₂ n → BinTree a n →  RAList' a (baddcarry b₁ b₂) n

concatRAList (RALZ)      ys          = ys
concatRAList (RALO xs  ) (RALZ)      = RALO xs
concatRAList (RALO xs  ) (RALO ys)   = RALO (concatRAList xs ys)
concatRAList (RALO xs  ) (RALI x ys) = RALI x (concatRAList xs ys)
concatRAList (RALI x xs) (RALZ)      = RALI x xs
concatRAList (RALI x xs) (RALO ys)   = RALI x (concatRAList xs ys)
concatRAList (RALI x xs) (RALI y ys) = RALO (concatRAList' xs ys (Node x y))
{-# COMPILE AGDA2HS concatRAList #-}

-- concat with carry
concatRAList' RALZ        ys          t = insertBinTree t ys
concatRAList' (RALO x)    RALZ        t = insertBinTree t (RALO x)
concatRAList' (RALI x xs) RALZ        t = insertBinTree t (RALI x xs)
concatRAList' (RALO xs)   (RALO ys)   t = RALI t (concatRAList xs ys)
concatRAList' (RALO xs)   (RALI y ys) t = RALO (concatRAList' xs ys (Node t y))
concatRAList' (RALI x xs) (RALO ys)   t = RALO (concatRAList' xs ys (Node x t))
concatRAList' (RALI x xs) (RALI y ys) t = RALI t (concatRAList' xs ys (Node x y))
{-# COMPILE AGDA2HS concatRAList' #-}

RAList : Set → @0 Bin → Set
RAList a bi = RAList' a bi 0
{-# COMPILE AGDA2HS RAList #-}

record RALIndex' (@0 b : Bin) (@0 offset) : Set where
  constructor MkPath
  field
    index       : BinInt
    path        : BinInt
    @0 deep     : TreePath offset (bin path)
open RALIndex' public
{-# COMPILE AGDA2HS RALIndex' #-}

RALIndex : @0 Bin → Set
RALIndex bi = RALIndex' bi 0

{-# COMPILE AGDA2HS RALIndex #-}
