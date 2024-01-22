-- | run-time integers packed with their compile-time binary representation
module Utils.BinInt where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Law.Equality using (sym; cong; cong₂)
open import Haskell.Law.Bool
open import Haskell.Law.Eq using (equality)

open import Data.Bits
open import Utils.Bin 
open import Utils.Misc


data _as_ (i : Integer) : Bin → Set where
  Z : IsTrue (i == 0)
    → i as Z
  I : {b : Bin}
    → IsTrue (testBit i 0)
    → shiftR i 1 as b
    → i          as I b
  O : {b : Bin}
    → IsFalse (testBit i 0)
    → IsFalse (i == 0)
    → shiftR i 1 as b
    → i          as O b


@0 uniqAs : {i : Integer} {x y : Bin} → i as x → i as y → x ≡ y
uniqAs (Z _    ) (Z _    ) = refl
uniqAs (I _ p  ) (I _ q  ) = cong I (uniqAs p q)
uniqAs (O _ _ p) (O _ _ q) = cong O (uniqAs p q)
uniqAs (Z z    ) (I t _  ) = schrodinger t (testBit0 z)
uniqAs (Z t    ) (O _ f _) = schrodinger t f
uniqAs (I t _  ) (Z z    ) = schrodinger t (testBit0 z)
uniqAs (I t _  ) (O f _ _) = schrodinger t f
uniqAs (O _ f _) (Z t    ) = schrodinger t f
uniqAs (O f _ _) (I t _  ) = schrodinger t f


@0 irrAs : {i : Integer} {b : Bin} (p q : i as b) → p ≡ q
irrAs (Z t1     ) (Z t2     ) = cong Z (irrIsTrue t1 t2)
irrAs (I t1 p   ) (I t2 q   ) = cong₂ I (irrIsTrue t1 t2) (irrAs p q)
irrAs (O f1 z1 p) (O f2 z2 q) = cong₃ O (irrIsFalse f1 f2) (irrIsFalse z1 z2) (irrAs p q)


postulate @0 bsuccAs : ∀ {i b} → i as b → succ i as bsucc b


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


{-
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
-- -}


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
isI (BI _ (Z  ) (Z i==0    )) bit1 = schrodinger i==0 (testBitneq0 bit1)
isI (BI _ (O _) (O bit0 _ _)) bit1 = schrodinger bit1 bit0
isI (BI _ (I _) (I _ p     )) bit1 = MkIsK p refl

@0 isO : (bi   : BinInt)
         (i/=0 : IsFalse (int bi == 0))
         (bit0 : IsFalse (testBit (int bi) 0))
       → IsK bi O
isO (BI _ (Z  ) (Z i==0  )) i/=0 bit0 = schrodinger i==0 i/=0
isO (BI _ (I _) (I bit1 _)) i/=0 bit0 = schrodinger bit1 bit0 
isO (BI _ (O _) (O _ _ p )) i/=0 bit0 = MkIsK p refl

view : ∀ bi → BinView bi
view (BI i b i≈b)
  = if i == 0 then (λ ⦃ i==0 ⦄ → let0 (equality i 0 i==0) λ where
    refl → dsubst₂ {b = 0 as_} (λ b i≈b → BinView (BI 0 b i≈b))
             (uniqAs (Z (isTrue i==0)) i≈b) (irrAs _ _)
             VZ
  ) else λ ⦃ i/=0 ⦄ → if testBit i 0 then (λ ⦃ bit ⦄ →
    let0 (isI (BI i b i≈b) (isTrue bit)) λ where
      (MkIsK {b} i'≈b refl) →
        dsubst₂ {b = _as I b} (λ i i≈Ib → BinView (BI i (I b) i≈Ib))
          (setBitshiftLshiftR (isTrue bit)) (irrAs _ _)
          (VI (BI (shiftR i 1) b i'≈b))
  ) else λ ⦃ nbit ⦄ →
    let0 (isO (BI i b i≈b) (isFalse i/=0) (isFalse nbit)) λ where
      (MkIsK {b} i'≈b refl) →
        dsubst₂ {b = _as O b} (λ i i≈Ob → BinView (BI i (O b) i≈Ob))
          (shiftLshiftR1 i (isFalse nbit)) (irrAs _ _)
          (VO (BI (shiftR i 1) b i'≈b) ⦃ neq0ShiftR i (isFalse i/=0) (isFalse nbit) ⦄)
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
