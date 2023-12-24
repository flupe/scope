module Utils.Bin where

open import Haskell.Prelude hiding (b)

open import Haskell.Law.Equality using (subst; sym; cong; cong₂)
open import Haskell.Law.Eq using (equality)
open import Haskell.Prim hiding (b)
open import Haskell.Law.Bool
open import Data.Bits
open import Utils.Misc

data Bin : Set where
  Z   : Bin
  O I : Bin → Bin

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
