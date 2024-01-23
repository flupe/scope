module Test where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Bool
open import Utils.Misc
  renaming (subst to subst0)

postulate
  pred>=→>  : (x y : Integer) → IsTrue (pred x >= y) → IsTrue (x > y)
  >→/=      : (x y : Integer) → IsTrue (x > y) → IsFalse (x == y)
  pred-succ : (x   : Integer) → pred (succ x) ≡ x

data _as_ : @0 Integer → @0 Nat → Set where
  0as0 : ∀ {i  } → IsTrue  (i == 0) → i as 0
  iasS : ∀ {i n} → pred i as n      → i as (suc n)

@0 succAs : ∀ {i n} → i as n → succ i as (suc n)
succAs {i} {n = n} p = iasS (subst0 (_as n) (sym (pred-succ i)) p)

@0 asGeq0 : ∀ {i n} → i as n → IsTrue (i >= 0)
asGeq0 {i} (0as0 i==0 ) = isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0))
asGeq0 {i} (iasS pri≈n) = isTrue (||-leftTrue  (0 < i) (i == 0) (trueIs (pred>=→> i 0 (asGeq0 pri≈n))))

@0 asSuccNeq0 : ∀ {i n} → i as (suc n) → IsFalse (i == 0)
asSuccNeq0 {i} (iasS pri≈n) = >→/= i 0 (pred>=→> i 0 (asGeq0 pri≈n))

@0 uniqAsNat : ∀ {i} {n m} → i as n → i as m → n ≡ m
uniqAsNat (0as0 _    ) (0as0 _    ) = refl
uniqAsNat (0as0 i==0 ) p@(iasS _  ) = schrodinger i==0 (asSuccNeq0 p)
uniqAsNat p@(iasS _  ) (0as0 i==0 ) = schrodinger i==0 (asSuccNeq0 p)
uniqAsNat (iasS pri≈n) (iasS pri≈m) = cong suc (uniqAsNat pri≈n pri≈m)

-- view
-------

data NatView : @0 Integer → @0 Nat → Set where
  Zero : NatView 0 0
  Succ : ∀ {@0 i n} → @0 ⦃ pred i as n ⦄ → NatView i (suc n)

{-# COMPILE AGDA2HS NatView #-}

record IsS (i : Integer) (n : Nat) : Set where
  constructor _⟨_⟩
  field {n'}   : Nat
        pri≈n' : pred i as n'
        sucn'  : suc n' ≡ n

@0 isS : ∀ {i n} → {{ i as n }} → (i == 0) ≡ False → IsS i n
isS ⦃ 0as0 i==0 ⦄ i/=0 = schrodinger i==0 (isFalse i/=0)
isS ⦃ iasS p    ⦄ i/=0 = p ⟨ refl ⟩

inspect : ∀ i {@0 n} → @0 {{ i as n }} → NatView i n
inspect i {n} {{ i≈n }} =
  if i == 0
  then (λ {{ i==0 }} → let0 (equality i 0 i==0) λ where
    refl → subst0 (NatView 0) (uniqAsNat (0as0 IsTrue.itsTrue) i≈n) Zero)
  else (λ {{ i/=0 }} → let0 (isS i/=0) λ where
    (pri≈n' ⟨ refl ⟩) → Succ {{ pri≈n' }})

{-# COMPILE AGDA2HS inspect #-}

-- example
----------

mul : ∀ x {@0 n} → @0 {{ x as n }} → Integer → Integer
mul x y =
  case inspect x of λ where
    Zero → 0
    Succ → y + mul (pred x) y

{-# COMPILE AGDA2HS mul #-}

double : ∀ x {@0 n} → @0 {{ x as n }} → Integer
double x =
  case inspect x of λ where
    Zero → 0
    Succ → succ (succ (double (pred x)))

{-# COMPILE AGDA2HS double #-}

-----------------------------------------------------------------

-- IntNat
---------

record IntNat : Set where
  constructor IN
  field
    int    : Integer
    @0 nat : Nat
    @0 inv : int as nat
open IntNat public

{-# COMPILE AGDA2HS IntNat unboxed #-}

zeroIN : IntNat
zeroIN = IN 0 0 (0as0 IsTrue.itsTrue)

{-# COMPILE AGDA2HS zeroIN inline #-}

succIN : IntNat → IntNat
succIN i = IN (succ (int i)) (suc (nat i)) (succAs (inv i))

{-# COMPILE AGDA2HS succIN inline #-}

predIN : ∀ (i : IntNat) {@0 n} → @0 {{ pred (int i) as n }} → IntNat
predIN i {n} {{ pri≈n }} = IN (pred (int i)) n pri≈n

{-# COMPILE AGDA2HS predIN inline #-}

inspectIN : (n : IntNat) → NatView (int n) (nat n)
inspectIN n = inspect (int n) {{ inv n }}

{-# COMPILE AGDA2HS inspectIN inline #-}

-- {-# TERMINATING #-}
-- doubleIN : IntNat → IntNat
-- doubleIN x =
--   case inspectIN x of λ where
--     Zero → zeroIN
--     Succ → succIN (succIN (doubleIN (predIN x)))
-- 
-- {-# COMPILE AGDA2HS doubleIN #-}
