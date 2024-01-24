module Test where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Bool
open import Haskell.Extra.Erase
open import Utils.Misc renaming (subst to subst0)

private variable @0 n : Nat


postulate
  pred>=→>  : (x y : Integer) → IsTrue (pred x >= y) → IsTrue (x > y)
  >→/=      : (x y : Integer) → IsTrue (x > y) → IsFalse (x == y)
  pred-succ : (x   : Integer) → pred (succ x) ≡ x


-- view
-------

data NatView (@0 i : Integer) : @0 Nat → Set where
  Zero : @0 {{ IsTrue (i == 0)    }} → NatView i 0
  Succ : @0 {{ NatView (pred i) n }} → NatView i (suc n)

{-# COMPILE AGDA2HS NatView #-}


@0 succView : ∀ {i n} → NatView i n → NatView (succ i) (suc n)
succView {i} {n = n} p = Succ {{ subst0 (λ i → NatView i n) (sym (pred-succ i)) p }}

@0 viewGeq0 : ∀ {i n} → NatView i n → IsTrue (i >= 0)
viewGeq0 {i} (Zero {{ i==0  }}) = isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0))
viewGeq0 {i} (Succ {{ pri≈n }}) = isTrue (||-leftTrue  (0 < i) (i == 0) (trueIs (pred>=→> i 0 (viewGeq0 pri≈n))))

@0 viewSuccNeq0 : ∀ {i n} → NatView i (suc n) → IsFalse (i == 0)
viewSuccNeq0 {i} (Succ {{ pri≈n }}) = >→/= i 0 (pred>=→> i 0 (viewGeq0 pri≈n))


-- inversion lemmas
-------------------

data IsZ : Nat → Set where itsZero : IsZ zero
data IsS : Nat → Set where itsSuc  : IsS (suc n)

@0 isZ : ∀ i {n} → {{ NatView i n }} → {{ (i == 0) ≡ True }} → IsZ n
isZ i   {{ Zero }}            = itsZero
isZ i p@{{ Succ }} {{ i==0 }} = schrodinger (isTrue i==0) (viewSuccNeq0 p)

@0 isS : ∀ i {n} → {{ NatView i n }} → {{ (i == 0) ≡ False }} → IsS n
isS i {{ Zero {{ i==0 }} }} {{ i/=0 }} = schrodinger i==0 (isFalse i/=0)
isS i {{ Succ            }}            = itsSuc


-- inspection i.e "resurrecting the view"
-----------------------------------------

inspect : ∀ i → {{ @0 v : NatView i n }} → Rezz _ v
inspect i {{ v }} =
  if i == 0
  then (let0 (isZ i) λ where
    itsZero → let0 v λ where
      Zero ⦃ p ⦄ → Rezzed Zero p)
  else (let0 (isS i) λ where
    itsSuc → let0 v λ where
      Succ ⦃ p ⦄ → Rezzed Succ p)

{-# COMPILE AGDA2HS inspect #-}

pattern Z = rezz Zero
pattern S = rezz Succ


-- demo
-------

mul : ∀ x {@0 n} → @0 {{ NatView x n }} → Integer → Integer
mul x y =
  case inspect x of λ where
    Z → 0
    S → y + mul (pred x) y

{-# COMPILE AGDA2HS mul #-}

{-
inspect : ∀ i {@0 n} → @0 {{ i as n }} → NatView i n
inspect i {n} {{ i≈n }} =
  if i == 0
  then (λ {{ i==0 }} → let0 (equality i 0 i==0) λ where
    refl → subst0 (NatView 0) (uniqAsNat (as0 IsTrue.itsTrue) i≈n) Zero)
  else (λ {{ i/=0 }} → let0 (isS i/=0) λ where
    (pri≈n' ⟨ refl ⟩) → Succ {{ pri≈n' }})

data _as_ : Integer → Nat → Set where
  as0 : ∀ {i  } → IsTrue  (i == 0) → i as 0
  asS : ∀ {i n} → pred i as n      → i as (suc n)


@0 succAs : ∀ {i n} → i as n → succ i as (suc n)
succAs {i} {n = n} p = asS (subst0 (_as n) (sym (pred-succ i)) p)

@0 asGeq0 : ∀ {i n} → i as n → IsTrue (i >= 0)
asGeq0 {i} (as0 i==0 ) = isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0))
asGeq0 {i} (asS pri≈n) = isTrue (||-leftTrue  (0 < i) (i == 0) (trueIs (pred>=→> i 0 (asGeq0 pri≈n))))

@0 asSuccNeq0 : ∀ {i n} → i as (suc n) → IsFalse (i == 0)
asSuccNeq0 {i} (asS pri≈n) = >→/= i 0 (pred>=→> i 0 (asGeq0 pri≈n))

@0 uniqAsNat : ∀ {i} {n m} → i as n → i as m → n ≡ m
uniqAsNat (as0 _    ) (as0 _    ) = refl
uniqAsNat (as0 i==0 ) p@(asS _  ) = schrodinger i==0 (asSuccNeq0 p)
uniqAsNat p@(asS _  ) (as0 i==0 ) = schrodinger i==0 (asSuccNeq0 p)
uniqAsNat (asS pri≈n) (asS pri≈m) = cong suc (uniqAsNat pri≈n pri≈m)


-- view
-------


data NatView (@0 i : Integer) : @0 Nat → Set where
  Zero :            @0 {{ IsTrue (i == 0) }} → NatView i 0
  Succ : ∀ {@0 n} → @0 {{ pred i as n     }} → NatView i (suc n)

{-# COMPILE AGDA2HS NatView #-}


record IsS (i : Integer) (n : Nat) : Set where
  constructor _⟨_⟩
  field {n'}   : Nat
        pri≈n' : pred i as n'
        sucn'  : suc n' ≡ n

@0 isS : ∀ {i n} → {{ i as n }} → (i == 0) ≡ False → IsS i n
isS {{ as0 i==0 }} i/=0 = schrodinger i==0 (isFalse i/=0)
isS {{ asS p    }} i/=0 = p ⟨ refl ⟩


inspect : ∀ i {@0 n} → @0 {{ i as n }} → NatView i n
inspect i {n} {{ i≈n }} =
  if i == 0
  then (λ {{ i==0 }} → let0 (equality i 0 i==0) λ where
    refl → subst0 (NatView 0) (uniqAsNat (as0 IsTrue.itsTrue) i≈n) Zero)
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


-- same, but trying to inline inspect

inspect' : ∀ i {@0 n} {@0 a : Set} → @0 {{ i as n }} → (NatView i n → a) → a
inspect' i {n} {{ i≈n }} f =
  if i == 0
  then (λ {{ i==0 }} → let0 (equality i 0 i==0) λ where
    refl → f (subst0 (NatView 0) (uniqAsNat (as0 IsTrue.itsTrue) i≈n) Zero))
  else (λ {{ i/=0 }} → let0 (isS i/=0) λ where (pri≈n' ⟨ refl ⟩) → (f (Succ {{ pri≈n' }})))

{-# COMPILE AGDA2HS inspect' inline #-}

double : ∀ x {@0 n} → @0 {{ x as n }} → Integer
double x =
  inspect' x λ where
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
zeroIN = IN 0 0 (as0 IsTrue.itsTrue)

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

-}
