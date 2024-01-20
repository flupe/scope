module Utils.BinNat where

open import Haskell.Prim hiding (s)
open import Haskell.Prelude hiding (s)
open import Haskell.Law.Equality hiding (subst)
open import Haskell.Law.Eq using (equality; eqReflexivity)
open import Haskell.Law.Bool
open import Haskell.Prim.Num

open import Data.Bits
open import Utils.Misc

private

  -- relating integers and their peano encoding
  data _as_ (i : Integer) : Nat → Set where
    Z : IsTrue (i == 0) → i as 0
    S : {n : Nat}
      → IsTrue (i > 0)
      → pred i as n
      → i as suc n

  -- these axioms all look reasonable
  -- they should be generalised and moved to LawfulOrd, and Integer properties
  postulate
    gt0neq0  : (i : Integer) → IsTrue (i > 0) → IsFalse (i == 0)
    <+≤→<    : (x y z : Integer) → IsTrue (y > x)  → IsTrue (z >= x) → IsTrue (y + z > x)
    succpred : (i : Integer) → succ (pred i) ≡ i
    swap+-   : (a b c : Integer) → (a + b) - c ≡ (a - c) + b
    times    : (i j : Integer) → j + (pred i * j) ≡ i * j

  -- integers have at most one encoding
  uniqAsNat : ∀ {i x y} → i as x → i as y → x ≡ y
  uniqAsNat     (Z _    ) (Z _    ) = refl
  uniqAsNat {i} (Z i==0 ) (S i>0 q) = schrodinger i==0 (gt0neq0 i i>0)
  uniqAsNat {i} (S i>0 p) (Z i==0 ) = schrodinger i==0 (gt0neq0 i i>0)
  uniqAsNat     (S _ p  ) (S _ q  ) = cong suc (uniqAsNat p q)

  -- encoding proofs are irrelevant
  irrAs : ∀ {i n} (p q : i as n) → p ≡ q
  irrAs (Z a  ) (Z b  ) = cong  Z (irrIsTrue a b)
  irrAs (S a p) (S b q) = cong₂ S (irrIsTrue a b) (irrAs p q)

  -- nats encode at most one integer
  uniqAsInt : ∀ {i j n} → i as n → j as n → i ≡ j
  uniqAsInt {i} {j} (Z i==0) (Z j==0)
    = trans (equality i 0 (trueIs i==0))
            (sym $ equality j 0 (trueIs j==0))
  uniqAsInt {i} {j} (S i>0 p) (S j>0 q) =
    i             ≡˘⟨ succpred i ⟩
    succ (pred i) ≡⟨ cong (λ i → succ i) (uniqAsInt p q) ⟩
    succ (pred j) ≡⟨ succpred j ⟩
    j             ∎

  -- actually, they encode exactly one integer
  fromNatAs : ∀ n → fromNat n as n
  fromNatAs zero    = Z itsTrue
  fromNatAs (suc n) = S itsTrue (fromNatAs n)

  -- encoded integers are always positive
  -- TODO: rewrite using fromNatAs?
  inatgeq0 : ∀ {i n} → i as n → IsTrue (i >= 0)
  inatgeq0 {i} (Z i==0 ) = isTrue (||-rightTrue (0 < i) (i == 0) (trueIs i==0))
  inatgeq0 {i} (S i>0 _) = isTrue (||-leftTrue  (0 < i) (i == 0) (trueIs i>0 ))

  -- TODO: rewrite using fromNatAs?
  succAs : ∀ {i n} → i as n → succ i as suc n
  succAs {i} (Z i==0)
    rewrite equality i 0 (trueIs i==0)
          = S itsTrue (Z itsTrue)
  succAs {i} {n} (S i>0 i-1≈n) =
    S (<+≤→< 0 i 1 i>0 itsTrue)
      (subst (_as n) (sym (swap+- i 1 1)) (succAs i-1≈n))

record BinNat : Set where
  constructor BN
  field
    int    : Integer
    @0 nat : Nat
    @0 inv : int as nat
open BinNat
{-# COMPILE AGDA2HS BinNat unboxed #-}

z : BinNat
z = BN 0 0 (Z itsTrue)
{-# COMPILE AGDA2HS z inline #-}

s : BinNat → BinNat
s (BN i n i≈n) = BN (succ i) (suc n) (succAs i≈n)
{-# COMPILE AGDA2HS s inline #-}

data NatView : @0 BinNat → Set where
  Z : NatView z
  S : ∀ bn → NatView (s bn)
{-# COMPILE AGDA2HS NatView #-}

private

  record @0 IsS (bn : BinNat) : Set where
    constructor MkIsS
    field {n'}     : Nat
          predi≈n' : pred (int bn) as n'
          sucn'    : suc n' ≡ nat bn

  @0 isS : ∀ {i n} → (i == 0) ≡ False → (@0 i≈n : i as n) → IsS (BN i n i≈n)
  isS i/=0 (Z i==0) = schrodinger i==0 (isFalse i/=0)
  isS _    (S _ p ) = MkIsS p refl

inspect : ∀ bn → NatView bn
inspect (BN i n i≈n) =
  if i == 0 then (λ ⦃ i==0 ⦄ → let0 (equality i 0 i==0) λ where
    (refl) →
      dsubst₂ {b = pos 0 as_} (λ n 0≈n → NatView (BN 0 n 0≈n))
        (uniqAsNat (Z itsTrue) i≈n) (irrAs _ _)
        $ Z
  ) else λ ⦃ i/=0 ⦄ → let0 (isS i/=0 i≈n) λ where
    (MkIsS {n'} predi≈n' refl) →
      dsubst₂ (λ i i≈n → NatView (BN i (suc n') i≈n))
        (succpred i) (irrAs _ _)
        $ S (BN (pred i) n' predi≈n')
{-# COMPILE AGDA2HS inspect #-}

private
  addAs : ∀ {i j} {n m} → i as n → j as m → (i + j) as (n + m)
  addAs {i = i} {j} {m = m} (Z i==0) q
    rewrite equality i 0 (trueIs i==0)
          | uniqAsInt q (fromNatAs m) = fromNatAs m
  addAs {i} {j} {suc n} {m} (S x p) q =
    subst (_as suc (addNat n m))
      (begin succ (pred i + j)   ≡˘⟨ cong (λ i → succ i) (swap+- i j 1) ⟩
             succ (pred (i + j)) ≡⟨ succpred (i + j) ⟩
             i + j               ∎)
      (succAs (addAs p q))

  mulAs : ∀ {i j} {n m} → i as n → j as m → (i * j) as (n * m)
  mulAs {i} {j} {0    } {m} (Z p  ) q
    rewrite equality i 0 (trueIs p)
          | uniqAsInt q (fromNatAs m) = Z itsTrue
  mulAs {i} {j} {suc n} {m} (S x p) q =
    subst (_as addNat m (mulNat n m)) (times i j) (addAs q (mulAs p q))

private
  addBinNat : (n m : BinNat) → BinNat
  addBinNat n m = BN (int n + int m) (nat n + nat m) (addAs (inv n) (inv m))
  {-# COMPILE AGDA2HS addBinNat inline #-}

  mulBinNat : (n m : BinNat) → BinNat
  mulBinNat n m = BN (int n * int m) (nat n * nat m) (mulAs (inv n) (inv m))
  {-# COMPILE AGDA2HS mulBinNat inline #-}

instance
  iNumberBinNat : Number BinNat
  iNumberBinNat .Number.Constraint _ = ⊤
  iNumberBinNat .fromNat n = BN (fromNat n) n (fromNatAs n)

  iNumBinNat : Num BinNat
  -- for now, no funky conversions
  iNumBinNat .MinusOK n m         = ⊥
  iNumBinNat .NegateOK _          = ⊥
  iNumBinNat .Num.FromIntegerOK _ = ⊥
  iNumBinNat ._+_ = addBinNat
  iNumBinNat ._*_ = mulBinNat
  iNumBinNat .abs = id
  iNumBinNat .signum bn =
    case inspect bn of λ where
      Z      → BN 0 0 (Z itsTrue)
      (S bn) → BN 1 1 (fromNatAs 1)
