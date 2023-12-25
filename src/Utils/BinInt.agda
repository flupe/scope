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

-- 2*[_]+1
i : BinInt → BinInt
i (BI i b i≈b) = BI
  (setBit (shiftL i 1) 0)
  (I b)
  (I (testBitsetBit (shiftL i 1))
     (subst (_as b) (sym (shiftsetshift i)) i≈b))
{-# COMPILE AGDA2HS i inline #-}

o' : (bi : BinInt) → @0 {{ IsFalse (int bi == 0) }} → BinInt
o' (BI i b i≈b) {{ i/=0 }} =
  BI (shiftL i 1)
     (O b)
     (O (testBitShiftL i)
        (neq0ShiftL i i/=0)
        (subst (_as b) (sym (shiftRshiftL i)) i≈b))
{-# COMPILE AGDA2HS o' inline #-}

-- 2*[_]
o : BinInt → BinInt
o (BI i b i≈b) =
  BI (shiftL i 1)
     (if i == 0 then Z else O b)
     (if i == 0 then (λ ⦃ i==0 ⦄ →
       subst (shiftL i 1 as_) (sym (ifTrueEqThen _ i==0)) $
         subst (_as Z)
               (subst (λ i → i ≡ shiftL i 1)
                      (sym (equality _ _ i==0))
                      (sym (equality _ _ (trueIs (eq0ShiftL 0 itsTrue)))))
               (Z {i = i} (isTrue i==0))
     ) else λ ⦃ i/=0 ⦄ →
       subst (shiftL i 1 as_) (sym (ifFalseEqElse _ i/=0)) $
         O (testBitShiftL i)
           (neq0ShiftL i (isFalse i/=0))
           (subst (_as b) (sym (shiftRshiftL i)) i≈b)
     )
{-# COMPILE AGDA2HS o inline #-}

data BinView : @0 BinInt → Set where
  VZ : BinView z
  VO : (bi : BinInt) → {{ @0 _ : IsFalse (int bi == 0) }} → BinView (o' bi)
  VI : (bi : BinInt) → BinView (i bi)
{-# COMPILE AGDA2HS BinView #-}

record IsI (bi : BinInt) : Set where
  constructor MkIsI
  field
    {i'} : Integer
    {b'} : Bin
    {a'} : i' as b'
    ieq  : shiftR (int bi) 1 ≡ i'
    ieq2 : setBit (shiftL i' 1) 0 ≡ int bi
    beq  : I b' ≡ bin bi
    aeq  : inv bi
         ≡ subst₂ (λ i b → i as b) ieq2 beq
                  (I (testBitsetBit _) (subst (_as b') (sym (shiftsetshift _)) a'))

@0 isI : (bi : BinInt) → IsTrue (testBit (int bi) 0) → IsI bi
isI (BI i .Z (Z z    )) t = schrodinger z (testBitneq0 t)
isI (BI i .(O _) (O f _ _)) t = schrodinger t f
isI (BI i (I b') inv@(I x p  )) t =
  subst 
   (λ i → (@0 i≈b : i as I b') → IsI (BI i (I b') i≈b))
   (setBitshiftLshiftR t)
   (λ i≈b → MkIsI (shiftsetshift (shiftR i 1)) refl refl
     (irrAs i≈b (I (testBitsetBit _) (subst ((_as b')) (sym (shiftsetshift _)) p))))
   inv

record IsO (bi : BinInt) (@0 i/=0 : IsFalse (int bi == 0))
                         (@0 bit0 : IsFalse (testBit (int bi) 0)) : Set where
  constructor MkIsO
  field
    {i'} : Integer
    {b'} : Bin
    {a'} : i' as b'
    ieq  : shiftR (int bi) 1 ≡ i'
    ieq2 : shiftL i' 1 ≡ int bi
    beq  : O b' ≡ bin bi
    aeq  : inv bi
         ≡ subst₂ (λ i b → i as b) ieq2 beq
                  (O (testBitShiftL i')
                     (neq0ShiftL i' (subst (λ i → IsFalse (i == 0)) ieq (neq0ShiftR (int bi) i/=0 bit0)))
                     (subst (_as b') (sym (shiftRshiftL i')) a'))


@0 isO
  : (bi : BinInt) (i/=0 : IsFalse (int bi == 0))
                  (bit0 : IsFalse (testBit (int bi) 0))
  → IsO bi i/=0 bit0
isO (BI i .(Z  ) (Z x        )) i/=0 bit0 = schrodinger x i/=0
isO (BI i .(I _) (I x p      )) i/=0 bit0 = schrodinger x bit0 
isO (BI i .(O b) (O {b} t f p)) i/=0 bit0 = subst₂
  (λ t' f' → IsO (BI i (O b) (O t f p)) f' t')
  (irrIsFalse t bit0) (irrIsFalse f i/=0)
  (subst (λ i → (@0 t   : IsFalse (i == 0)) (@0 f : IsFalse (testBit i 0))
                (@0 i≈b : shiftR i 1 as b) → IsO (BI i (O b) (O f t i≈b)) t f)
    (shiftLshiftR1 i t)
    (λ t' f' i≈b → MkIsO {a' = p}
      (cong (λ i → shiftR i 1) (shiftLshiftR1 i t)) refl refl (irrAs _ _))
    f t p)

view : ∀ bi → BinView bi
view (BI i b i≈b) =
  if i == 0
  then (λ ⦃ i==0 ⦄ → subst
    (λ i → (@0 i≈b : i as b) → BinView (BI i b i≈b))
    (sym (equality _ _ i==0))
    (λ i≈b → subst
      (λ b → (@0 0≈b : 0 as b) → BinView (BI 0 b 0≈b))
      (uniqAs (Z itsTrue) i≈b)
      (λ 0≈b → subst
        (λ 0≈b → BinView (BI (Integer.pos 0) Z 0≈b))
        (irrAs (Z itsTrue) 0≈b)
        VZ)
      i≈b)
    i≈b
  ) else λ ⦃ i/=0 ⦄ →
    if testBit i 0 then (λ ⦃ bit ⦄ →
      let0 (isI (BI i b i≈b) (isTrue bit)) λ is → subst₂
        (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
        (IsI.ieq2 is) (IsI.beq is)
        (subst
          (λ i → (@0 i≈b : i as I (IsI.b' is)) → BinView (BI i _ i≈b))
          (cong (λ i → setBit (shiftL i 1) 0) (IsI.ieq is))
          λ i≈b → subst (λ i≈b → BinView (BI _ _ i≈b))
            (irrAs (I (testBitsetBit _)
                      (subst (_as _) (sym (shiftsetshift (shiftR i 1)))
                             (subst (_as _) (sym (IsI.ieq is)) (IsI.a' is)))) i≈b)
            (VI (BI (shiftR i 1) (IsI.b' is) _)))
        i≈b
    ) else λ ⦃ nbit ⦄ →
      let0 (isO (BI i b i≈b) (isFalse i/=0) (isFalse nbit)) λ is → subst₂
        (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
        (IsO.ieq2 is) (IsO.beq is)
        (subst
          (λ i → (@0 i≈b : i as O (IsO.b' is)) → BinView (BI i _ i≈b))
          (cong (λ i₁ → shiftL i₁ 1) (IsO.ieq is))
          λ i≈b → subst (λ i≈b → BinView (BI _ _ i≈b))
            (irrAs (O (testBitShiftL _)
                      (neq0ShiftL _ (neq0ShiftR i (isFalse i/=0) (isFalse nbit)))
                      (subst (_as _) (sym (shiftRshiftL (shiftR i 1)))
                             (subst (_as _) (sym (IsO.ieq is)) (IsO.a' is)))) i≈b)
            (VO (BI (shiftR i 1) (IsO.b' is) _)
                ⦃ neq0ShiftR i (isFalse i/=0) (isFalse nbit) ⦄))
        i≈b
{-# COMPILE AGDA2HS view #-}
