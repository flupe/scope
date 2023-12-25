module Utils.RAList where

open import Haskell.Prim using (it)
open import Haskell.Prelude
open import Haskell.Law.Equality
open import Haskell.Extra.Refinement

open import Utils.Bin
open import Utils.BinInt
open import Data.Bits

private
  variable @0 n : Nat

  data Tree (a : Set) : @0 Nat → Set where
    Leaf : a → Tree a 0
    Node : ∀ {@0 n} (l r : Tree a n) → Tree a (1 + n)
  {-# COMPILE AGDA2HS Tree #-}

  data Length : Bin → Nat → Set where
    instance
      LZ : Length Z zero
      LO : ∀ {b n} → {{ Length b n }} → Length (O b) (suc n)
      LI : ∀ {b n} → {{ Length b n }} → Length (I b) (suc n)

  lookupTree : (path : BinInt) → @0 {{ Length (bin path) n }} → Tree a n → a
  lookupTree _    (Leaf x  ) = x
  lookupTree path {{ z }} (Node l r) =
    case view path of λ where
      (VO pl) → lookupTree pl {{ olength pl z }} l
      (VI pr) → lookupTree pr {{ ilength pr z }} r
    where
      @0 ilength : ∀ {n} (p : BinInt) → Length (bin (i p)) (suc n) → Length (bin p) n
      ilength p LI = it
  
      @0 olength : ∀ {n} (p : BinInt) {{_ : IsFalse (int p == 0) }}
                 → Length (bin (o' p)) (suc n) → Length (bin p) n
      olength p LO = it
  {-# COMPILE AGDA2HS lookupTree #-}

data RAList' (a : Set) : @0 Bin → @0 Nat → Set where
  RALZ : ∀ {@0 n}                                    → RAList' a (Z  ) n
  RALO : ∀ {@0 n b}            → RAList' a b (suc n) → RAList' a (O b) n
  RALI : ∀ {@0 n b} → Tree a n → RAList' a b (suc n) → RAList' a (I b) n
{-# COMPILE AGDA2HS RAList' #-}

opaque
  RAList : Set → @0 BinInt → Set
  RAList a bi = RAList' a (bin bi) 0
  {-# COMPILE AGDA2HS RAList #-}

record Path (@0 b : Bin) : Set where
  constructor MkPath
  field
    index       : BinInt
    path        : BinInt
    @0 {offset} : Nat
    @0 deep     : Length (bin path) offset
open Path public
{-# COMPILE AGDA2HS Path #-}
