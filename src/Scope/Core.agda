module Scope.Core where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def using (IsLawfulMonoid)
open import Haskell.Law.Monoid.List using (iLawfulMonoidList)
open import Haskell.Extra.Erase
open import Haskell.Extra.Dec as Dec
open import Haskell.Extra.Refinement

open import Utils.Tactics
open import Utils.BinInt

open import Utils.RAList
open import Utils.Tree
open import Data.Bits

private variable
  name : Set

record Scope (@0 name) : Set where
  constructor MkScope
  field
    -- a scope has a given size
    size     : BinInt
    -- an as many names (erased) as its size
    @0 names : RAList name (size .bin)
open Scope public
{-# COMPILE AGDA2HS Scope newtype #-}

opaque

  singleton : @0 name → Scope name
  singleton x = MkScope (i z) (RALI (Leaf x) RALZ)
  {-# COMPILE AGDA2HS singleton #-}

  syntax singleton x = [ x ]

  empty : Scope name
  empty = MkScope z RALZ
  {-# COMPILE AGDA2HS empty inline #-}

  concatScope : Scope name → Scope name → Scope name
  concatScope s1 s2 =
    MkScope
      (bintadd (s1 .size) (s2 .size))
      (concatRAList (s1 .names) (s2 .names))
  {-# COMPILE AGDA2HS concatScope inline #-}

  instance
    iSemigroupScope : Semigroup (Scope name)
    iSemigroupScope ._<>_ = concatScope

    {-# COMPILE AGDA2HS iSemigroupScope #-}

    iMonoidScope : Monoid (Scope name)
    iMonoidScope = record { DefaultMonoid (λ { .DefaultMonoid.mempty → empty }) }

    {-# COMPILE AGDA2HS iMonoidScope #-}

  bind : @0 name → Scope name → Scope name
  bind x α = singleton x <> α
  {-# COMPILE AGDA2HS bind #-}

  syntax bind x α = x ◃ α

  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz _ α → Rezz _ (bind x α)
  rezzBind (rezz r) = rezz (bind _ r)
  {-# COMPILE AGDA2HS rezzBind #-}

{-

    iLawfulSemigroupScope : IsLawfulSemigroup (Scope name)
    iLawfulSemigroupScope = iLawfulSemigroupList

    iLawfulMonoidScope : IsLawfulMonoid (Scope name)
    iLawfulMonoidScope = iLawfulMonoidList

-}
