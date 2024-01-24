{-# OPTIONS --prop #-}
module Test3 where

open import Haskell.Law.Equality
open import Haskell.Law.Bool
open import Haskell.Prelude
open import Haskell.Prim using (itsTrue)

open import Utils.Misc hiding (subst)

private variable @0 n : Nat


-- v reasonable postulates
--------------------------

postulate
  pred>=→>  : (x y : Integer) → IsTrue (pred x >= y) → IsTrue (x > y)
  >→/=      : (x y : Integer) → IsTrue (x > y) → IsFalse (x == y)
  pred-succ : (x   : Integer) → pred (1 + x) ≡ x
  succ-pred : (x   : Integer) → 1 + (pred x) ≡ x


-- propositional squash
-----------------------

data Squash (A : Set) : Prop where
  [_] : A → Squash A

data ⊥ₚ : Prop where

⊥→⊥ₚ : ⊥ → ⊥ₚ
⊥→⊥ₚ ()

absurdₚ : ⊥ₚ → a
absurdₚ ()

mapS : (f : a → b) → Squash a → Squash b
mapS f [ x ] = [ f x ]

S-elim : {P : Prop} → (a → P) → Squash a → P
S-elim f [ x ] = f x

substₚ : (@0 b : @0 a → Prop) {x y : a} → x ≡ y → b x → b y
substₚ b refl z = z


-- invariant
------------

-- relating integers and their peano encoding
_as_ : Integer → Nat → Prop
i as zero  = Squash (IsTrue (i == 0))
i as suc n = pred i as n

succAs : ∀ {i} (@0 n) → i as n → (1 + i) as suc n
succAs {i} n p = substₚ (_as n) (sym (pred-succ i)) p

viewGeq0 : ∀ {i} n → i as n → Squash (IsTrue (i >= 0))
viewGeq0 {i} (zero ) [ i==0 ] = [ isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0)) ]
viewGeq0 {i} (suc n) i-1≈n    = mapS (isTrue ∘ ||-leftTrue (0 < i) (i == 0) ∘ trueIs ∘ pred>=→> i 0) (viewGeq0 n i-1≈n)

asS→/=0 : ∀ i n → i as suc n → Squash (IsFalse (i == 0))
asS→/=0 i n i-1≈n = mapS (>→/= i 0 ∘ pred>=→> i 0) (viewGeq0 n i-1≈n)

-- uniqAsNat : ∀ i n m → i as n → i as m → Squash (n ≡ m)
-- uniqAsNat i (zero ) (zero ) p        q = [ refl ]
-- uniqAsNat i (zero ) (suc m) [ i==0 ] q = mapS (schrodinger i==0) (asS→/=0 i m q)
-- uniqAsNat i (suc n) (zero ) p [ i==0 ] = mapS (schrodinger i==0) (asS→/=0 i n p)
-- uniqAsNat i (suc n) (suc m) p        q = mapS (cong suc) (uniqAsNat (pred i) n m p q)


-- integer-encoded nats
-----------------------

record IntNat : Set where
  constructor IN
  field
    int       : Integer
    @0 nat    : Nat
    {{ inv }} : int as nat
open IntNat public
{-# COMPILE AGDA2HS IntNat #-}

-- we get the usual smart constructors
--------------------------------------

zIN : IntNat
zIN = IN 0 0 {{ [ itsTrue ] }}
{-# COMPILE AGDA2HS zIN #-}

sIN : IntNat → IntNat
sIN (IN i n {{ v }}) = IN (1 + i) (suc n) {{ succAs n v }}
{-# COMPILE AGDA2HS sIN #-}

-- and we have an inductive view
--------------------------------

data View : @0 IntNat → Set where
  VZ : ∀ {@0 i} → {{ v : Squash (IsTrue (i == 0)) }} → View (IN i 0)
  VS : ∀ i → View (sIN i)
{-# COMPILE AGDA2HS View #-}

data Null? : Nat → Bool → Set where
  itsZero :            Null? (zero ) True
  itsSuc  : ∀ (@0 n) → Null? (suc n) False

@0 isNull : ∀ i n b → {{ i as n }} → {{ (i == 0) ≡ b }} → Null? n b
isNull i (zero ) True  {{ p }}            = itsZero
isNull i (suc n) False {{ p }}            = itsSuc n
isNull i (suc n) True  {{ p }} {{ i==0 }} = absurdₚ (S-elim (λ p → ⊥→⊥ₚ (schrodinger (isTrue i==0) p)) (asS→/=0 i n p))
isNull i (zero ) False {{ p }} {{ i/=0 }} = absurdₚ (S-elim (λ p → ⊥→⊥ₚ (schrodinger p (isFalse i/=0))) p)

inspect : ∀ i → View i
inspect (IN i n {{ v }}) =
  if (i == 0) then (let0 (isNull i n True) λ where itsZero → VZ)
  else let0 (isNull i n False) λ where
    (itsSuc n) → subst0 (λ i → {{ @0 _ : i as suc n }} → View (IN i (suc n)))
                        (succ-pred i) (VS (IN (pred i) n {{ v }}))
