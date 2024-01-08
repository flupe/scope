module Utils.Bin where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Law.Eq using (equality; nequality)
open import Haskell.Law.Equality using (sym; cong; cong₂)


open import Haskell.Law.Num
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


-- binary addition and whatnot
------------------------------

bsucc : Bin → Bin
bsucc Z     = I Z
bsucc (O b) = I b
bsucc (I b) = O (bsucc b)

badd baddcarry : Bin → Bin → Bin

badd (Z  ) (y  ) = y
badd (x  ) (Z  ) = x
badd (O x) (O y) = O (badd x y)
badd (O x) (I y) = I (badd x y)
badd (I x) (O y) = I (badd x y)
badd (I x) (I y) = O (baddcarry x y)

data @0 Badd  : @0 Bin → @0 Bin → @0 Bin → Set
data @0 BaddC : @0 Bin → @0 Bin → @0 Bin → Set

-- inductive graph of badd
data Badd where
  BZ+ : ∀ {@0 b}     → Badd Z b b
  B+Z : ∀ {@0 b}     → Badd b Z b
  O+O : ∀ {@0 x y r} → Badd  x y r → Badd (O x) (O y) (O r)
  O+I : ∀ {@0 x y r} → Badd  x y r → Badd (O x) (I y) (I r)
  I+O : ∀ {@0 x y r} → Badd  x y r → Badd (I x) (O y) (I r)
  I+I : ∀ {@0 x y r} → BaddC x y r → Badd (I x) (I y) (I r)

-- inductive graph of baddcarry
data BaddC where
  BZ+ : ∀ {@0 b}     → BaddC Z b (bsucc b)
  B+Z : ∀ {@0 b}     → BaddC b Z (bsucc b)
  O+O : ∀ {@0 x y r} → Badd  x y r → BaddC (O x) (O y) (I r)
  O+I : ∀ {@0 x y r} → BaddC x y r → BaddC (O x) (I y) (O r)
  I+O : ∀ {@0 x y r} → BaddC x y r → BaddC (I x) (O y) (O r)
  I+I : ∀ {@0 x y r} → BaddC x y r → BaddC (I x) (I y) (I r)

+Z : ∀ b → badd b Z ≡ b
+Z Z     = refl
+Z (O b) = refl
+Z (I b) = refl

baddcarry (Z  ) (y  ) = bsucc y
baddcarry (x  ) (Z  ) = bsucc x
baddcarry (O x) (O y) = I (badd x y)
baddcarry (O x) (I y) = O (baddcarry x y)
baddcarry (I x) (O y) = O (baddcarry x y)
baddcarry (I x) (I y) = I (baddcarry x y)

postulate
  @0 bsuccAs : ∀ {i b} → i as b → succ i as bsucc b

-- bsuccAs {i = i} (Z p)
--   rewrite equality i 0 (trueIs {b = i == 0} p)
--         = I testBit1 (subst (_as Z) (sym shiftR1) (Z itsTrue))
-- bsuccAs {i} (O bit0 i/=0 p)
--   = {!!}
-- bsuccAs {i} (I {b} tB p)
--   = O {!!} {!!} {!!}
{-

open LawfulNum iIntegerLawfulNum

baddAs {x} {y = y} (Z x==0) yas
  rewrite equality x 0 (trueIs x==0)
        | +-identityₗ y
        = yas
baddAs {x} {bx} {y} xas (Z y==0)
  rewrite equality y 0 (trueIs y==0)
        | +-identityᵣ x
        | +Z bx
        = xas
baddAs (I tstx1 p) (O tsty0 y/=0 q) =
  I {!!}
    {!!}
baddAs (O x x₁ p) (I x₂ q   ) = {!!}
baddAs (O x x₁ p) (O x₂ x₃ q) = {!!}
baddAs (I x p   ) (I x₁ q   ) = {!!}

-}
