{-# OPTIONS --prop #-}
module Test where

open import Haskell.Prelude
open import Haskell.Law.Eq
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Bool
open import Haskell.Extra.Erase
open import Utils.Misc

private variable @0 n : Nat

postulate
  pred>=→>  : (x y : Integer) → IsTrue (pred x >= y) → IsTrue (x > y)
  >→/=      : (x y : Integer) → IsTrue (x > y) → IsFalse (x == y)
  pred-succ : (x   : Integer) → pred (succ x) ≡ x
  succ-pred : (x   : Integer) → succ (pred x) ≡ x

data Squash (a : Set) : Prop where
  [_] : @0 a → Squash a

_as_ : Integer → Nat → Prop
i as zero  = Squash ((i == 0) ≡ True) -- Squash (IsTrue (i == 0))
i as suc n = pred i as n

substProp : {@0 a : Set} (@0 b : @0 a → Prop) {x y : a} → x ≡ y → b x → b y
substProp b refl z = z

.succAs : ∀ i (@0 n) → {{ i as n }} → succ i as suc n
succAs i n {{ p }} = substProp (_as n) (sym (pred-succ i)) p

postulate
  viewGeq0     : ∀ {i} n → i as n     → IsTrue (i >= 0)
  viewSuccNeq0 : ∀ {i} n → i as suc n → IsFalse (i == 0)

record IntNat : Set where
  constructor IN
  field
    int        : Integer
    @0 nat     : Nat
    .{{ inv }} : int as nat
open IntNat public
{-# COMPILE AGDA2HS IntNat unboxed #-}

@0 substAs : ∀ {i j n} → i as n → i ≡ j → j as n
substAs p refl = p

zIN : IntNat
zIN = IN 0 0 {{ [ refl ] }}

sIN : IntNat → IntNat
sIN (IN i n) = IN (succ i) (suc n) {{ succAs i n }}

data View : IntNat → Set where
  VZ : ∀ i → (v : i as 0) → View (IN i 0 {{ v }})
  VS : ∀ i → View (sIN i)

data IsNull? : Nat → Bool → Set where
  itsZ : IsNull? (zero ) True
  itsS : ∀ (@0 n) → IsNull? (suc n) False

@0 isNull? : ∀ {i} n b → .{{ i as n }} → {{ (i == 0) ≡ b }} → IsNull? n b
isNull? {i} (zero ) (False) ⦃ p ⦄ ⦃ i/=0 ⦄ = {!!} -- schrodinger p (isFalse i/=0)
isNull? {i} (suc n) (True ) ⦃ p ⦄ ⦃ i==0 ⦄ = {!!} -- schrodinger (isTrue i==0) (viewSuccNeq0 {i} {n} p)
isNull? {i} (zero ) (True ) ⦃ p ⦄ ⦃ i==0 ⦄ = itsZ
isNull? {i} (suc n) (False) ⦃ p ⦄ ⦃ i==0 ⦄ = itsS n

inspect : ∀ i → View i
inspect (IN i n {{ v }}) =
  if i == 0 then (λ ⦃ i==0 ⦄ → let0 (isNull? {i} n True) λ where
    itsZ → VZ i {!!}
  ) else λ ⦃ i/=0 ⦄ → let0 (isNull? {i} n False) λ where
    (itsS n) →
      subst (λ i → . {{ v : i as suc n}} → View (IN i (suc n) {{ v }})) (succ-pred i)
        (λ ⦃ v ⦄ → VS (IN (pred i) n ⦃ substProp (λ i → pred i as n) (succ-pred i) v ⦄))

{-
.succAs : ∀ i (@0 n) → {{ i as n }} → succ i as suc n
succAs i n {{ p }} = subst (_as n) (sym (pred-succ i)) p

postulate viewGeq0 : ∀ {i n} → i as n → IsTrue (i >= 0)
-- viewGeq0 {i} {zero } (i==0 ) = isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0))
-- viewGeq0 {i} {suc n} (pri≈n) = isTrue (||-leftTrue  (0 < i) (i == 0) (trueIs (pred>=→> i 0 (viewGeq0 {i} {n} pri≈n))))

postulate
  viewSuccNeq0 : ∀ {i n} → i as suc n → IsFalse (i == 0)
-- viewSuccNeq0 {i} {n} (pri≈n) = >→/= i 0 (pred>=→> i 0 (viewGeq0 {i} {n} pri≈n))

record IntNat : Set where
  constructor IN
  field
    int        : Integer
    @0 nat     : Nat
    .{{ inv }} : int as nat
open IntNat public
{-# COMPILE AGDA2HS IntNat unboxed #-}

zIN : IntNat
zIN = IN 0 0 {{ [ IsTrue.itsTrue ] }}

sIN : IntNat → IntNat
sIN (IN i n) = IN (succ i) (suc n) {{ succAs i n }}

data View : IntNat → Set where
  VZ : ∀ {@0 i n} (@0 @irr v : i as n) → View (IN i n {{ v }})
  VS : ∀ i → View (sIN i)

data IsNull? : Nat → Bool → Set where
  itsZ : IsNull? (zero ) True
  itsS : IsNull? (suc n) False

@0 isNull? : ∀ {i} n b → .{{ i as n }} → {{ (i == 0) ≡ b }} → IsNull? n b
isNull? {i} (zero ) (False) ⦃ p ⦄ ⦃ i/=0 ⦄ = {!!} -- schrodinger p (isFalse i/=0)
isNull? {i} (suc n) (True ) ⦃ p ⦄ ⦃ i==0 ⦄ = {!!} -- schrodinger (isTrue i==0) (viewSuccNeq0 {i} {n} p)
isNull? {i} (zero ) (True ) ⦃ p ⦄ ⦃ i==0 ⦄ = itsZ
isNull? {i} (suc n) (False) ⦃ p ⦄ ⦃ i==0 ⦄ = itsS

letIrr : ∀ {@0 a : Set} {@0 b : .a → Set} (@0 @irr x : a) → ((@0 @irr x : a) → b x) → b x
letIrr x f = f x
{-# COMPILE AGDA2HS letIrr transparent #-}

@0 .rezz0 : @0 a → a
rezz0 x = x

inspect : ∀ i → View i
inspect (IN i n) =
  if i == 0 then (λ ⦃ i==0 ⦄ → let0 (isNull? {i} n True) λ where
    itsZ → VZ [ (isTrue i==0) ]
  ) else
    {!!}

{-

-- view
-------

NatView (@0 i : Integer) : @0 Nat → Set where
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

@0 irrView : ∀ {i n} (p q : NatView i n) → p ≡ q
irrView (Zero {{ p }}) (Zero {{ q }}) = cong (λ p → Zero ⦃ p ⦄) (irrIsTrue p q)
irrView (Succ {{ p }}) (Succ {{ q }}) = cong (λ p → Succ ⦃ p ⦄) (irrView p q)


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

double : ∀ x {@0 n} → @0 {{ NatView x n }} → Integer
double x =
  case inspect x of λ where
    Z → 0
    S → 2 + double (pred x)

{-# COMPILE AGDA2HS double #-}


-- packing everything together
------------------------------

record IntNat : Set where
  constructor IN
  field
    int    : Integer
    @0 nat : Nat
    @0 inv : NatView int nat
open IntNat public

{-# COMPILE AGDA2HS IntNat unboxed #-}

zeroI : IntNat
zeroI = IN 0 0 Zero

{-# COMPILE AGDA2HS zeroI inline #-}

succI : IntNat → IntNat
succI i = IN (succ (int i)) (suc (nat i)) (succView (inv i))

{-# COMPILE AGDA2HS succI inline #-}

data View : @0 IntNat → Set where
  ZeroI : View zeroI
  SuccI : ∀ i → View (succI i)

{-# COMPILE AGDA2HS View #-}

inspectI : ∀ i → View i
inspectI (IN i n v) = case (inspect i {{ v }}) of λ where
  (rezz (Zero {{ i==0 }})) →
    dsubst₂ {b = λ i → NatView i 0} (λ i v → View (IN i 0 v))
      (sym (equality i 0 (trueIs i==0))) (irrView _ _)
      ZeroI
  (rezz (Succ {{ v }})) →
    dsubst₂ {b = λ i → NatView i (suc _)} (λ i v → View (IN i _ v))
      (succ-pred i) (irrView _ _)
      (SuccI (IN (pred i) _ v))

{-# COMPILE AGDA2HS inspectI #-}

doubleI : IntNat → IntNat
doubleI i =
  case inspectI i of λ where
    ZeroI     → zeroI
    (SuccI i) → succI (succI (doubleI i))

{-# COMPILE AGDA2HS doubleI #-}

-}

-}
