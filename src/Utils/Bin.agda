module Utils.Bin where

open import Haskell.Prelude
open import Haskell.Prim
open import Haskell.Law.Eq using (equality; nequality)
open import Haskell.Law.Equality
  renaming (trans to infixl 5 _∙_)


open import Haskell.Law.Num
open import Data.Bits
open import Utils.Misc

data Bin : Set where
  Zero     : Bin
  Odd Even : Bin → Bin
{-# COMPILE AGDA2HS Bin #-}

bsucc : Bin → Bin
bsucc Zero     = Odd Zero
bsucc (Odd b)  = Even b
bsucc (Even b) = Odd (bsucc b)

bdouble : Bin → Bin
bdouble Zero     = Zero
bdouble (Odd x)  = Even (bdouble x)
bdouble (Even x) = Even (Odd x)

bpred : Bin → Bin
bpred Zero     = Zero
bpred (Odd x)  = bdouble x
bpred (Even x) = Odd x

bdouble-bsucc : ∀ b → bdouble (bsucc b) ≡ Even b
bdouble-bsucc Zero     = refl
bdouble-bsucc (Odd b)  = refl
bdouble-bsucc (Even b) = cong Even (bdouble-bsucc b)

bpred-bsucc : ∀ b → bpred (bsucc b) ≡ b
bpred-bsucc Zero = refl
bpred-bsucc (Odd b) = refl
bpred-bsucc (Even b) = bdouble-bsucc b

badd  : (x y : Bin) → Bin
baddc : (x y : Bin) → Bin
badd (Zero  ) (y     ) = y
badd (x     ) (Zero  ) = x
badd (Odd  x) (Odd  y) = Even (baddc x y)
badd (Odd  x) (Even y) = Odd  (baddc x y)
badd (Even x) (Odd  y) = Odd  (baddc x y)
badd (Even x) (Even y) = Even (baddc x y)

baddc (Zero  ) (y     ) = bsucc y
baddc (     x) (Zero  ) = bsucc x
baddc (Odd  x) (Odd  y) = Odd (baddc x y)
baddc (Odd  x) (Even y) = {!!}
baddc (Even x) (Odd  y) = {!!}
baddc (Even x) (Even y) = {!!}

{-

private
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

  baddcarry (Z  ) (y  ) = bsucc y
  baddcarry (x  ) (Z  ) = bsucc x
  baddcarry (O x) (O y) = I (badd x y)
  baddcarry (O x) (I y) = O (baddcarry x y)
  baddcarry (I x) (O y) = O (baddcarry x y)
  baddcarry (I x) (I y) = I (baddcarry x y)

  badd-comm      : ∀ x y → badd x y ≡ badd y x
  baddcarry-comm : ∀ x y → baddcarry x y ≡ baddcarry y x

  badd-comm (Z  ) (Z  ) = refl
  badd-comm (Z  ) (O y) = refl
  badd-comm (Z  ) (I y) = refl
  badd-comm (O x) (Z  ) = refl
  badd-comm (O x) (O y) = cong O (badd-comm x y)
  badd-comm (O x) (I y) = cong I (badd-comm x y)
  badd-comm (I x) (Z  ) = refl
  badd-comm (I x) (O y) = cong I (badd-comm x y)
  badd-comm (I x) (I y) = cong O (baddcarry-comm x y)

  baddcarry-comm (Z  ) (Z  ) = refl
  baddcarry-comm (Z  ) (O y) = refl
  baddcarry-comm (Z  ) (I y) = refl
  baddcarry-comm (O x) (Z  ) = refl
  baddcarry-comm (O x) (O y) = cong I (badd-comm x y)
  baddcarry-comm (O x) (I y) = cong O (baddcarry-comm x y)
  baddcarry-comm (I x) (Z  ) = refl
  baddcarry-comm (I x) (O y) = cong O (baddcarry-comm x y)
  baddcarry-comm (I x) (I y) = cong I (baddcarry-comm x y)

  baddcarry≈bsucc-badd : ∀ x y → baddcarry x y ≡ bsucc (badd x y)
  baddcarry≈bsucc-badd (Z  ) (y  ) = refl
  baddcarry≈bsucc-badd (O x) (Z  ) = refl
  baddcarry≈bsucc-badd (O x) (O y) = refl
  baddcarry≈bsucc-badd (O x) (I y) = cong O (baddcarry≈bsucc-badd x y)
  baddcarry≈bsucc-badd (I x) (Z  ) = refl
  baddcarry≈bsucc-badd (I x) (O y) = cong O (baddcarry≈bsucc-badd x y)
  baddcarry≈bsucc-badd (I x) (I y) = refl

  badd-bsucc : ∀ x y → badd (bsucc x) y ≡ bsucc (badd x y)
  badd-bsucc (Z  ) (Z  ) = refl
  badd-bsucc (Z  ) (O y) = refl
  badd-bsucc (Z  ) (I y) = refl
  badd-bsucc (O x) (Z  ) = refl
  badd-bsucc (O x) (O y) = refl
  badd-bsucc (O x) (I y) = cong O (baddcarry≈bsucc-badd x y)
  badd-bsucc (I x) (Z  ) = refl
  badd-bsucc (I x) (O y) = cong O (badd-bsucc x y)
  badd-bsucc (I x) (I y) = cong I (badd-bsucc x y ∙ sym (baddcarry≈bsucc-badd x y))

  badd-assoc     : ∀ x y z → badd x (badd y z) ≡ badd (badd x y) z
  badd-baddcarry : ∀ x y z → badd x (baddcarry y z) ≡ badd (baddcarry x y) z
  baddcarry-assoc : ∀ x y z → baddcarry x (baddcarry y z) ≡ baddcarry (baddcarry x y) z

  x+⟨y+1+z⟩≡⟨x+y⟩+1+z : ∀ x y z → badd x (baddcarry y z) ≡ baddcarry (badd x y) z
  x+⟨y+1+z⟩≡⟨x+y⟩+1+z x y z =
    badd x (baddcarry y z)    ≡⟨ cong (badd x) (baddcarry≈bsucc-badd y z) ⟩
    badd x (bsucc (badd y z)) ≡⟨ badd-comm x _ ⟩
    badd (bsucc (badd y z)) x ≡⟨ badd-bsucc (badd y z) x ⟩
    bsucc (badd (badd y z) x) ≡⟨ cong bsucc (badd-comm (badd y z) x) ⟩
    bsucc (badd x (badd y z)) ≡⟨ cong bsucc (badd-assoc x y z) ⟩
    bsucc (badd (badd x y) z) ≡˘⟨ baddcarry≈bsucc-badd (badd x y) z ⟩
    baddcarry (badd x y) z    ∎

  x+1+⟨y+z⟩≡⟨x+y⟩+1+z : ∀ x y z → baddcarry x (badd y z) ≡ baddcarry (badd x y) z
  x+1+⟨y+z⟩≡⟨x+y⟩+1+z x y z =
    baddcarry x (badd y z)    ≡⟨ baddcarry≈bsucc-badd x (badd y z) ⟩
    bsucc (badd x (badd y z)) ≡⟨ cong bsucc (badd-assoc x y z) ⟩
    bsucc (badd (badd x y) z) ≡˘⟨ baddcarry≈bsucc-badd (badd x y) z ⟩
    baddcarry (badd x y) z    ∎

  baddcarry-assoc x y z =
    baddcarry x (baddcarry y z)       ≡⟨ cong (baddcarry x) (baddcarry≈bsucc-badd y z) ⟩
    baddcarry x (bsucc (badd y z))    ≡⟨ baddcarry≈bsucc-badd x _ ⟩
    bsucc (badd x (bsucc (badd y z))) ≡⟨ cong bsucc (badd-comm x _) ⟩
    bsucc (badd (bsucc (badd y z)) x) ≡⟨ cong bsucc (badd-bsucc (badd y z) x) ⟩
    bsucc (bsucc (badd (badd y z) x)) ≡⟨ cong (bsucc ∘ bsucc) (badd-comm (badd y z) x ∙ badd-assoc x y z) ⟩
    bsucc (bsucc (badd (badd x y) z)) ≡˘⟨ cong bsucc (badd-bsucc (badd x y) z) ⟩
    bsucc (badd (bsucc (badd x y)) z) ≡˘⟨ baddcarry≈bsucc-badd (bsucc (badd x y)) z ⟩
    baddcarry (bsucc (badd x y)) z    ≡˘⟨ cong (λ n → baddcarry n z) (baddcarry≈bsucc-badd x y) ⟩
    baddcarry (baddcarry x y) z       ∎

  badd-baddcarry x y z = {!!}

  badd-assoc (Z  ) (y  ) (z  ) = refl
  badd-assoc (O x) (Z  ) (z  ) = refl
  badd-assoc (O x) (O y) (Z  ) = refl
  badd-assoc (O x) (O y) (O z) = cong O (badd-assoc x y z)
  badd-assoc (O x) (O y) (I z) = cong I (badd-assoc x y z)
  badd-assoc (O x) (I y) (Z  ) = refl
  badd-assoc (O x) (I y) (O z) = cong I (badd-assoc x y z)
  badd-assoc (O x) (I y) (I z) = cong O (x+⟨y+1+z⟩≡⟨x+y⟩+1+z x y z)
  badd-assoc (I x) (Z  ) (z  ) = refl
  badd-assoc (I x) (O y) (Z  ) = refl
  badd-assoc (I x) (O y) (O z) = cong I (badd-assoc x y z)
  badd-assoc (I x) (O y) (I z) = cong O (x+1+⟨y+z⟩≡⟨x+y⟩+1+z x y z)
  badd-assoc (I x) (I y) (Z  ) = refl
  badd-assoc (I x) (I y) (O z) = cong O {!!}
  badd-assoc (I x) (I y) (I z) = cong I (badd-baddcarry x y z)
{-

  badd-baddcarry (Z  ) (Z  ) (Z  ) = refl
  badd-baddcarry (Z  ) (Z  ) (O z) = refl
  badd-baddcarry (Z  ) (Z  ) (I z) = refl
  badd-baddcarry (Z  ) (O y) (Z  ) = refl
  badd-baddcarry (Z  ) (O y) (O z) = refl
  badd-baddcarry (Z  ) (O y) (I z) = refl
  badd-baddcarry (Z  ) (I y) (Z  ) = refl
  badd-baddcarry (Z  ) (I y) (O z) = cong O {!!}
  badd-baddcarry (Z  ) (I y) (I z) = cong I {!!}
  badd-baddcarry (O x) (Z  ) (Z  ) = cong I {!!}
  badd-baddcarry (O x) (Z  ) (O z) = refl
  badd-baddcarry (O x) (Z  ) (I z) = cong O {!!}
  badd-baddcarry (O x) (O y) (Z  ) = refl
  badd-baddcarry (O x) (O y) (O z) = cong I (badd-assoc x y z)
  badd-baddcarry (O x) (O y) (I z) = cong O {!!}
  badd-baddcarry (O x) (I y) (Z  ) = cong O {!!}
  badd-baddcarry (O x) (I y) (O z) = cong O (badd-baddcarry x y z)
  badd-baddcarry (O x) (I y) (I z) = cong I {!!}
  badd-baddcarry (I x) (Z  ) (Z  ) = cong O {!!}
  badd-baddcarry (I x) (Z  ) (O z) = cong O {!!}
  badd-baddcarry (I x) (Z  ) (I z) = cong I {!!}
  badd-baddcarry (I x) (O y) (Z  ) = refl
  badd-baddcarry (I x) (O y) (O z) = cong O {!!}
  badd-baddcarry (I x) (O y) (I z) = cong I (badd-baddcarry x y z)
  badd-baddcarry (I x) (I y) (Z  ) = cong I {!!}
  badd-baddcarry (I x) (I y) (O z) = cong I (badd-baddcarry x y z)
  badd-baddcarry (I x) (I y) (I z) = cong O (baddcarry-assoc x y z)
  -}

{-
  baddcarry-assoc (Z  ) (Z  ) (Z  ) = refl
  baddcarry-assoc (Z  ) (Z  ) (O z) = refl
  baddcarry-assoc (Z  ) (Z  ) (I z) = refl
  baddcarry-assoc (Z  ) (O y) (Z  ) = refl
  baddcarry-assoc (Z  ) (O y) (O z) = cong O (sym (baddcarry≈bsucc-badd y z))
  baddcarry-assoc (Z  ) (O y) (I z) = refl
  baddcarry-assoc (Z  ) (I y) (Z  ) = refl
  baddcarry-assoc (Z  ) (I y) (O z) = cong I {!!}
  baddcarry-assoc (Z  ) (I y) (I z) = cong O {!!}
  baddcarry-assoc (O x) (Z  ) (Z  ) = cong O {!!}
  baddcarry-assoc (O x) (Z  ) (O z) = refl
  baddcarry-assoc (O x) (Z  ) (I z) = cong I {!!}
  baddcarry-assoc (O x) (O y) (Z  ) = cong O (baddcarry≈bsucc-badd x y)
  baddcarry-assoc (O x) (O y) (O z) = cong O {!!}
  baddcarry-assoc (O x) (O y) (I z) = cong I {!!}
  baddcarry-assoc (O x) (I y) (Z  ) = cong I {!!}
  baddcarry-assoc (O x) (I y) (O z) = cong I (badd-baddcarry x y z)
  baddcarry-assoc (O x) (I y) (I z) = cong O (baddcarry-assoc x y z)
  baddcarry-assoc (I x) (Z  ) (Z  ) = cong I {!!}
  baddcarry-assoc (I x) (Z  ) (O z) = cong I {!!}
  baddcarry-assoc (I x) (Z  ) (I z) = cong O {!!}
  baddcarry-assoc (I x) (O y) (Z  ) = refl
  baddcarry-assoc (I x) (O y) (O z) = cong I {!!}
  baddcarry-assoc (I x) (O y) (I z) = cong O (baddcarry-assoc x y z)
  baddcarry-assoc (I x) (I y) (Z  ) = cong O {!!}
  baddcarry-assoc (I x) (I y) (O z) = cong O (baddcarry-assoc x y z)
  baddcarry-assoc (I x) (I y) (I z) = cong I (baddcarry-assoc x y z)

-}

{-
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
  -}


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

-}
