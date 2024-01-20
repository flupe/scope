-- | run-time integers packed with their compile-time binary representation
module Utils.BinInt where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Law.Equality using (sym; cong)
open import Haskell.Law.Bool
open import Haskell.Law.Eq using (equality)

open import Data.Bits
open import Utils.Bin 
open import Utils.Misc


record BinInt : Set where
  constructor BI
  field
    int    : Integer
    @0 bin : Bin
    @0 inv : int as bin
open BinInt public
{-# COMPILE AGDA2HS BinInt unboxed #-}


z : BinInt
z = BI 0 Z (Z itsTrue)
{-# COMPILE AGDA2HS z inline #-}

i : BinInt → BinInt
i (BI i b i≈b) =
  BI (setBit (shiftL i 1) 0) (I b)
     (I (testBitsetBit (shiftL i 1))
        (subst (_as b) (sym (shiftsetshift i)) i≈b))
{-# COMPILE AGDA2HS i inline #-}

o' : (bi : BinInt) → @0 {{ IsFalse (int bi == 0) }} → BinInt
o' (BI i b i≈b) {{ i/=0 }} =
  BI (shiftL i 1) (O b)
     (O (testBitShiftL i)
        (neq0ShiftL i i/=0)
        (subst (_as b) (sym (shiftRshiftL i)) i≈b))
{-# COMPILE AGDA2HS o' inline #-}

-- o : BinInt → BinInt
-- o (BI i b i≈b) =
--   BI (shiftL i 1)
--      (if i == 0 then Z else O b)
--      (if i == 0 then (λ ⦃ i==0 ⦄ →
--        subst (shiftL i 1 as_) (sym (ifTrueEqThen _ i==0)) $
--          subst (_as Z)
--                (subst (λ i → i ≡ shiftL i 1)
--                       (sym (equality _ _ i==0))
--                       (sym (equality _ _ (trueIs (eq0ShiftL 0 itsTrue)))))
--                (Z {i = i} (isTrue i==0))
--      ) else λ ⦃ i/=0 ⦄ →
--        subst (shiftL i 1 as_) (sym (ifFalseEqElse _ i/=0)) $
--          O (testBitShiftL i)
--            (neq0ShiftL i (isFalse i/=0))
--            (subst (_as b) (sym (shiftRshiftL i)) i≈b)
--      )
-- {-# COMPILE AGDA2HS o inline #-}


data BinView : @0 BinInt → Set where
  VZ : BinView z
  VO : (bi : BinInt) → {{ @0 _ : IsFalse (int bi == 0) }} → BinView (o' bi)
  VI : (bi : BinInt) → BinView (i bi)
{-# COMPILE AGDA2HS BinView #-}


record @0 IsK (bi : BinInt) (K : Bin → Bin) : Set where
  constructor MkIsK
  field {b'} : Bin
        a'   : shiftR (int bi) 1 as b'
        beq  : K b' ≡ bin bi

@0 isI : (bi   : BinInt)
         (bit1 : IsTrue (testBit (int bi) 0))
       → IsK bi I
isI (BI _ (Z  ) (Z z    )) t = schrodinger z (testBitneq0 t)
isI (BI _ (O _) (O f _ _)) t = schrodinger t f
isI (BI _ (I _) (I _ p  )) t = MkIsK p refl

@0 isO : (bi   : BinInt)
         (i/=0 : IsFalse (int bi == 0))
         (bit0 : IsFalse (testBit (int bi) 0))
       → IsK bi O
isO (BI _ (Z  ) (Z x    )) i/=0 bit0 = schrodinger x i/=0
isO (BI _ (I _) (I x _  )) i/=0 bit0 = schrodinger x bit0 
isO (BI _ (O _) (O _ _ p)) i/=0 bit0 = MkIsK p refl

view : ∀ bi → BinView bi
view (BI i b i≈b) =
  if i == 0 then (λ ⦃ i==0 ⦄ →
    subst₂ (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
      (sym (equality _ _ i==0)) (uniqAs (Z (isTrue i==0)) i≈b)
      (λ 0≈b → subst (λ 0≈b → BinView (BI 0 Z 0≈b))
                 (irrAs (Z itsTrue) 0≈b)
                 VZ)
      i≈b
  ) else λ ⦃ i/=0 ⦄ →
    if testBit i 0 then (λ ⦃ bit ⦄ →
      let0 (isI (BI i b i≈b) (isTrue bit)) λ is →
        subst₂ (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
          (setBitshiftLshiftR (isTrue bit)) (IsK.beq is)
          (λ i≈b → subst (λ i≈b → BinView (BI _ _ i≈b))
              (irrAs (I (testBitsetBit _)
                        (subst (_as _) (sym (shiftsetshift (shiftR i 1)))
                               (IsK.a' is))) i≈b)
              (VI (BI (shiftR i 1) (IsK.b' is) _)))
          i≈b
    ) else λ ⦃ nbit ⦄ →
      let0 (isO (BI i b i≈b) (isFalse i/=0) (isFalse nbit)) λ is →
        subst₂ (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
          (shiftLshiftR1 i (isFalse nbit)) (IsK.beq is)
          (λ i≈b → subst (λ i≈b → BinView (BI _ _ i≈b))
              (irrAs (O (testBitShiftL _)
                        (neq0ShiftL _ (neq0ShiftR i (isFalse i/=0) (isFalse nbit)))
                        (subst (_as _) (sym (shiftRshiftL (shiftR i 1)))
                               (IsK.a' is))) i≈b)
              (VO (BI (shiftR i 1) (IsK.b' is) _) ⦃ _ ⦄))
          i≈b
{-# COMPILE AGDA2HS view #-}

postulate
  -- TODO(flupe)
  @0 baddAs
       : ∀ {x bx} {y by}
       → x as bx
       → y as by
       → (x + y) as badd bx by

bintadd : BinInt → BinInt → BinInt
bintadd bx by =
  BI (bx .int + by .int)
     (badd (bx .bin) (by .bin))
     (baddAs (bx .inv) (by .inv))
{-# COMPILE AGDA2HS bintadd inline #-}
