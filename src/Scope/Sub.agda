module Scope.Sub where

open import Haskell.Prelude
open import Haskell.Extra.Refinement

open import Scope.Core
open import Utils.Bin
open import Utils.BinInt
open import Utils.RAList
open import Utils.Misc
-- open import Scope.Split

private variable
  name : Set
  @0 x y : name
  @0 α α₁ α₂ β β₁ β₂ γ : Scope name

record Sub (@0 α β : Scope name) : Set where
  constructor MkSub
  field
    sub     : Scope name
    @0 invs : badd (α .size .bin) (sub .size .bin) ≡ (β .size .bin)
    @0 invn : subst (λ b → (xs : RAList' name b 0) → Set) invs
                    (concatRAList (α .names) (sub .names) ≡_)
                    (β .names)
open Sub public
{-# COMPILE AGDA2HS Sub newtype #-}

syntax Sub α β = α ⊆ β

postulate admit : a

subTrans : α ⊆ β → β ⊆ γ → α ⊆ γ
subTrans s1 s2 =
  MkSub (concatScope (s1 .sub) (s2 .sub))
        admit
        admit
{-# COMPILE AGDA2HS subTrans #-}
{-

  subTrans : α ⊆ β → β ⊆ γ → α ⊆ γ
  subTrans < p > < q > =
    let < r , _ > = splitAssoc p q
    in  < r >
  {-# COMPILE AGDA2HS subTrans #-}

  subLeft : α ⋈ β ≡ γ → α ⊆ γ
  subLeft p = < p >
  {-# COMPILE AGDA2HS subLeft transparent #-}

  subRight : α ⋈ β ≡ γ → β ⊆ γ
  subRight p = < splitComm p >
  {-# COMPILE AGDA2HS subRight #-}

  subWeaken : α ⊆ β → α ⊆ (bind x β)
  subWeaken < p > = < splitBindRight p >
  {-# COMPILE AGDA2HS subWeaken #-}

  subEmpty : mempty ⊆ α
  subEmpty = subLeft splitEmptyLeft
  {-# COMPILE AGDA2HS subEmpty #-}

  subRefl : α ⊆ α
  subRefl = subLeft splitEmptyRight
  {-# COMPILE AGDA2HS subRefl #-}

  rezzSub : α ⊆ β → Rezz _ β → Rezz _ α
  rezzSub < p > = rezzSplitLeft p
  {-# COMPILE AGDA2HS rezzSub #-}

  subJoin : Rezz _ α₂
          → α₁ ⊆ α₂
          → β₁ ⊆ β₂
          → (α₁ <> β₁) ⊆ (α₂ <> β₂)
  subJoin r < p > < q > = < splitJoin r p q >
  {-# COMPILE AGDA2HS subJoin #-}

  subJoinKeep : Rezz _ α → β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  subJoinKeep r < p > = < splitJoinLeft r p >
  {-# COMPILE AGDA2HS subJoinKeep #-}

  subJoinDrop : Rezz _ α → β₁ ⊆ β₂ → β₁ ⊆ (α <> β₂)
  subJoinDrop r < p > = < splitJoinRight r p >
  {-# COMPILE AGDA2HS subJoinDrop #-}

opaque
  unfolding Sub

  subBindKeep : α ⊆ β → (bind y α) ⊆ (bind y β)
  subBindKeep {y = y} = subJoinKeep (rezz (singleton y))
  {-# COMPILE AGDA2HS subBindKeep #-}

  subBindDrop : α ⊆ β → α ⊆ (bind y β)
  subBindDrop {y = y} = subJoinDrop (rezz (singleton y))
  {-# COMPILE AGDA2HS subBindDrop #-}

opaque
  unfolding Sub

  joinSubLeft : Rezz _ α₁ → (α₁ <> α₂) ⊆ β → α₁ ⊆ β
  joinSubLeft r < p > =
    let < q , _ > = splitAssoc (splitRefl r) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubLeft #-}

  joinSubRight : Rezz _ α₁ → (α₁ <> α₂) ⊆ β → α₂ ⊆ β
  joinSubRight r < p > =
    let < q , _ > = splitAssoc (splitComm (splitRefl r)) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubRight #-}

-}
