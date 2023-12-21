module Utils.Bin where

open import Haskell.Prelude
open import Haskell.Prim
open import Data.Bits

open import Haskell.Law.Equality using (subst; sym; cong; cong₂)
open import Haskell.Law.Eq using (equality; iLawfulEqInteger)

private variable @0 n : Nat

data Bin : @0 Nat → Set where
  Z   : Bin 0
  I O : Bin n → Bin (suc n)

data _encodes_ : Bin n → Integer → Set where
  Z : Z encodes 0
  I : ∀ {b : Bin n} {i}
    → b encodes (shiftR i 1)
    → IsTrue (testBit i 0)
    → (I b) encodes i
  O : ∀ {b : Bin n} {i}
    → b encodes (shiftR i 1)
    → IsFalse (testBit i 0)
    → (O b) encodes  i

{-

data MinimalNotNull : Bin → Set
data Minimal : Bin → Set

data MinimalNotNull where
  O : ∀ {b} → MinimalNotNull b → MinimalNotNull (O b)
  I : ∀ {b} → Minimal b → MinimalNotNull (I b)

data Minimal where
  Z : Minimal Z
  I : ∀ {b} → Minimal b → Minimal (I b)
  O : ∀ {b} → MinimalNotNull b → Minimal (O b)

-}

record BinInt (@0 len : Nat) : Set where
  constructor MkBinInt
  field
    int    : Integer
    @0 bin : Bin len
    @0 inv : bin encodes int

open BinInt public
{-# COMPILE AGDA2HS BinInt #-}

z : BinInt 0
z = MkBinInt 0 Z Z
{-# COMPILE AGDA2HS z #-}

o : BinInt n → BinInt (suc n)
o (MkBinInt i b inv) = record
  { int = shiftL i 1
  ; bin = O b
  ; inv = O (subst (λ i → b encodes i) (sym (shiftRshiftL i)) inv)
            (testBitShift i)
  }
{-# COMPILE AGDA2HS o #-}

i : BinInt n → BinInt (suc n)
i (MkBinInt i b inv) = record
  { int = setBit (shiftL i 1) 0
  ; bin = I b
  ; inv = I (subst (λ i → b encodes i) (sym (shiftsetshift i)) inv)
            (testBitsetBit _)
  }
{-# COMPILE AGDA2HS i #-}

private
  schrodinger : ∀ {b} → IsTrue b → IsFalse b → ⊥
  schrodinger itsTrue ()

  propIsTrue : ∀ {b} (p q : IsTrue b) → p ≡ q
  propIsTrue itsTrue itsTrue = refl

  propIsFalse : ∀ {b} (p q : IsFalse b) → p ≡ q
  propIsFalse itsFalse itsFalse = refl

data BinView : @0 BinInt n → Set where
  Z : BinView z
  O : (bi : BinInt n) → BinView (o bi)
  I : (bi : BinInt n) → BinView (i bi)
{-# COMPILE AGDA2HS BinView #-}

-- for a given length, all binary encodings of an integer are identical
@0 uniqBin : ∀ {i} {x y : Bin n} → x encodes i → y encodes i → x ≡ y
uniqBin Z       Z       = refl
uniqBin (I a _) (I b _) = cong I (uniqBin a b)
uniqBin (O a _) (O b _) = cong O (uniqBin a b)
uniqBin (I _ t) (O _ f) = magic (schrodinger t f)
uniqBin (O _ f) (I _ t) = magic (schrodinger t f)

-- proof of encodings are propositions
@0 propInv : ∀ {i} {x : Bin n} (p q : x encodes i) → p ≡ q
propInv Z Z = refl
propInv (I p x) (I q y) = cong₂ I (propInv p q) (propIsTrue x y)
propInv (O p x) (O q y) = cong₂ O (propInv p q) (propIsFalse x y)

@0 zeros : ∀ n → Bin n
zeros zero = Z
zeros (suc n) = O (zeros n)

@0 zerosIs0 : zeros n encodes 0
zerosIs0 {n = zero } = Z
zerosIs0 {n = suc n} =
  O (subst (λ i → zeros n encodes i) (sym shiftR0) zerosIs0)
    testBit0

private
  postulate anything : a

  subst' : (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → p x → p y
  subst' p refl x = x
  {-# COMPILE AGDA2HS subst' transparent #-}

zeroBinView
  : ∀ i → @0 i ≡ 0 → (@0 b : Bin n) (@0 inv : b encodes i)
  → BinView (MkBinInt i b inv)
zeroBinView {n = n} i p =
  subst' (λ i → (@0 b : Bin n) (@0 inv : b encodes i) → BinView (MkBinInt i b inv))
         (sym p)
    (λ b inv → subst'
      (λ b → (@0 inv : b encodes 0) → BinView (MkBinInt 0 b inv))
      (uniqBin zerosIs0 inv)
      (λ inv' → anything) inv)
{-# COMPILE AGDA2HS zeroBinView #-}


viewBin : (bi : BinInt n) → BinView bi
viewBin (MkBinInt i b inv) =
  if i == 0
    then (λ ⦃ p ⦄ → zeroBinView i (equality _ _ p) b inv)
    else anything
{-# COMPILE AGDA2HS viewBin #-}


{-

add  : Bin → Bin → Bin
add1 : Bin → Bin → Bin

add B     y     = y
add x     B     = x
add (x I) (y O) = add x y I
add (x O) (y I) = add x y I
add (x O) (y O) = add x y O
add (x I) (y I) = add1 x y O

add1 B B = B I
add1 B (y I) = add1 B y O
add1 B (y O) = y I
add1 (x I) B = add1 x B O
add1 (x I) (y I) = add1 x y I
add1 (x I) (y O) = add1 x y O
add1 (x O) B = x I
add1 (x O) (y I) = add1 x y O
add1 (x O) (y O) = add x y I


-}
