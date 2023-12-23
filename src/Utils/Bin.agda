module Utils.Bin where

open import Haskell.Prelude hiding (b)

open import Haskell.Law.Equality using (subst; sym; cong; cong₂)
open import Haskell.Law.Eq using (equality)
open import Haskell.Prim hiding (b)
open import Haskell.Law.Bool
open import Data.Bits

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

record BinInt : Set where
  constructor BI
  field
    int    : Integer
    @0 bin : Bin
    @0 inv : int as bin
open BinInt public
{-# COMPILE AGDA2HS BinInt newtype #-}

private
  schrodinger : ∀ {b} → IsTrue b → IsFalse b → a
  schrodinger itsTrue ()

  isTrue : ∀ {b} → b ≡ True → IsTrue b
  isTrue refl = IsTrue.itsTrue
  
  isFalse : ∀ {b} → b ≡ False → IsFalse b
  isFalse refl = IsFalse.itsFalse

  irrIsTrue : ∀ {b} (p q : IsTrue b) → p ≡ q
  irrIsTrue itsTrue itsTrue = refl

  irrIsFalse : ∀ {b} (p q : IsFalse b) → p ≡ q
  irrIsFalse itsFalse itsFalse = refl

  trueIs : ∀ {b} → IsTrue b → b ≡ True
  trueIs itsTrue = refl

  cong₃ : {b : Set} (f : a → b → c → d) {x y : a} {z w : b} {u v : c}
        → x ≡ y → z ≡ w → u ≡ v
        → f x z u ≡ f y w v
  cong₃ f refl refl refl = refl

  subst' : {@0 a : Set} (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → p x → p y
  subst' p refl x = x
  {-# COMPILE AGDA2HS subst' transparent #-}

  subst₂ : {a b : Set} (p : a → b → Set) {x y : a} {z w : b}
         → x ≡ y → z ≡ w → p x z → p y w
  subst₂ p refl refl x = x

  subst'₂ : {@0 a b : Set} (@0 p : @0 a → @0 b → Set) {@0 x y : a} {@0 z w : b}
         → @0 x ≡ y → @0 z ≡ w → p x z → p y w
  subst'₂ p refl refl x = x
  {-# COMPILE AGDA2HS subst'₂ transparent #-}

uniqAs : {i : Integer} {x y : Bin} → i as x → i as y → x ≡ y
uniqAs (Z _    ) (Z _    ) = refl
uniqAs (I _ p  ) (I _ q  ) = cong I (uniqAs p q)
uniqAs (O _ _ p) (O _ _ q) = cong O (uniqAs p q)
uniqAs (Z z    ) (I t _  ) = schrodinger t (testBit0 z)
uniqAs (Z t    ) (O _ f _) = schrodinger t f
uniqAs (I t _  ) (Z z    ) = schrodinger t (testBit0 z)
uniqAs (I t _  ) (O f _ _) = schrodinger t f
uniqAs (O _ f _) (Z t    ) = schrodinger t f
uniqAs (O f _ _) (I t _  ) = schrodinger t f

irrAs : {i : Integer} {b : Bin} (p q : i as b) → p ≡ q
irrAs (Z t1     ) (Z t2     ) = cong Z (irrIsTrue t1 t2)
irrAs (I t1 p   ) (I t2 q   ) = cong₂ I (irrIsTrue t1 t2) (irrAs p q)
irrAs (O f1 z1 p) (O f2 z2 q) = cong₃ O (irrIsFalse f1 f2) (irrIsFalse z1 z2) (irrAs p q)

z : BinInt
z = BI 0 Z (Z itsTrue)
{-# COMPILE AGDA2HS z #-}

-- 2*[_]+1
i : BinInt → BinInt
i (BI i b i≈b) = BI
  (setBit (shiftL i 1) 0)
  (I b)
  (I (testBitsetBit (shiftL i 1))
     (subst (_as b) (sym (shiftsetshift i)) i≈b))
{-# COMPILE AGDA2HS i #-}

o' : (bi : BinInt) → @0 {{ IsFalse (int bi == 0) }} → BinInt
o' (BI i b i≈b) {{ i/=0 }} =
  BI (shiftL i 1)
     (O b)
     (O (testBitShiftL i)
        (neq0ShiftL i i/=0)
        (subst (_as b) (sym (shiftRshiftL i)) i≈b))

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
{-# COMPILE AGDA2HS o #-}

data BinView : @0 BinInt → Set where
  VZ : BinView z
  VO : (bi : BinInt) → {{ @0 _ : IsFalse (int bi == 0) }} → BinView (o' bi)
  VI : (bi : BinInt) → BinView (i bi)
{-# COMPILE AGDA2HS BinView #-}

postulate anything : a

record IsI (bi : BinInt) : Set where
  constructor MkIsI
  field
    {i'} : Integer
    {b'} : Bin
    {a'} : i' as b'
    ieq  : shiftR (int bi) 1 ≡ i'
    ieq2 : setBit (shiftL i' 1) 0 ≡ int bi
    beq  : I b' ≡ bin bi
    aeq  : inv bi ≡ subst₂
                      (λ i b → i as b) ieq2 beq
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

let0 : {b : Set} (@0 x : a) (f : @0 a → b) → b
let0 x f = f x
{-# COMPILE AGDA2HS let0 transparent #-}

view : ∀ bi → BinView bi
view (BI i b i≈b) =
  if i == 0
  then (λ ⦃ i==0 ⦄ → subst'
    (λ i → (@0 i≈b : i as b) → BinView (BI i b i≈b))
    (sym (equality _ _ i==0))
    (λ i≈b → subst'
      (λ b → (@0 0≈b : 0 as b) → BinView (BI 0 b 0≈b))
      (uniqAs (Z itsTrue) i≈b)
      (λ 0≈b → subst'
        (λ 0≈b → BinView (BI (Integer.pos 0) Z 0≈b))
        (irrAs (Z itsTrue) 0≈b)
        VZ)
      i≈b)
    i≈b
  ) else λ ⦃ i/=0 ⦄ →
    if testBit i 0 then (λ ⦃ bit ⦄ →
      let0 (isI (BI i b i≈b) (isTrue bit)) λ is → subst'₂
        (λ i b → (@0 i≈b : i as b) → BinView (BI i b i≈b))
        (IsI.ieq2 is) (IsI.beq is)
        (subst'
          (λ i → (@0 i≈b : i as I (IsI.b' is)) → BinView (BI i _ i≈b))
          (cong (λ i → setBit (shiftL i 1) 0) (IsI.ieq is))
          λ i≈b → subst' (λ i≈b → BinView (BI _ _ i≈b))
            (irrAs (I (testBitsetBit _)
                      (subst (_as _) (sym (shiftsetshift (shiftR i 1)))
                             (subst (_as _) (sym (IsI.ieq is)) (IsI.a' is)))) i≈b)
            (VI (BI (shiftR i 1) (IsI.b' is) _)))
        i≈b
    ) else λ ⦃ nbit ⦄ →
      anything
{-# COMPILE AGDA2HS view #-}

{- 

record BinInt (@0 len : Nat) : Set where
  constructor MkBinInt
  field
    int    : Integer
    @0 bin : Bin len
    @0 inv : bin encodes int

open BinInt public
{-# COMPILE AGDA2HS BinInt #-}

z : BinInt 0
z = MkBinInt 0 Z Z
{-# COMPILE AGDA2HS z #-}

o : BinInt n → BinInt (suc n)
o (MkBinInt i b inv) = record
  { int = shiftL i 1
  ; bin = O b
  ; inv = O (subst (λ i → b encodes i) (sym (shiftRshiftL i)) inv)
            (testBitShift i)
  }
{-# COMPILE AGDA2HS o #-}

i : BinInt n → BinInt (suc n)
i (MkBinInt i b inv) = record
  { int = setBit (shiftL i 1) 0
  ; bin = I b
  ; inv = I (subst (λ i → b encodes i) (sym (shiftsetshift i)) inv)
            (testBitsetBit _)
  }
{-# COMPILE AGDA2HS i #-}

data BinView : @0 BinInt n → Set where
  Z : BinView z
  O : (bi : BinInt n) → BinView (o bi)
  I : (bi : BinInt n) → BinView (i bi)
{-# COMPILE AGDA2HS BinView #-}

-- for a given length, all binary encodings of an integer are identical
@0 uniqBin : ∀ {i} {x y : Bin n} → x encodes i → y encodes i → x ≡ y
uniqBin Z       Z       = refl
uniqBin (I a _) (I b _) = cong I (uniqBin a b)
uniqBin (O a _) (O b _) = cong O (uniqBin a b)
uniqBin (I _ t) (O _ f) = magic (schrodinger t f)
uniqBin (O _ f) (I _ t) = magic (schrodinger t f)

-- proof of encodings are propositions
@0 propInv : ∀ {i} {x : Bin n} (p q : x encodes i) → p ≡ q
propInv Z Z = refl
propInv (I p x) (I q y) = cong₂ I (propInv p q) (propIsTrue x y)
propInv (O p x) (O q y) = cong₂ O (propInv p q) (propIsFalse x y)

@0 zeros : ∀ n → Bin n
zeros zero = Z
zeros (suc n) = O (zeros n)

@0 zerosIs0 : zeros n encodes 0
zerosIs0 {n = zero } = Z
zerosIs0 {n = suc n} =
  O (subst (λ i → zeros n encodes i) (sym shiftR0) zerosIs0)
    testBit0

private
  postulate anything : a

  subst' : (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → p x → p y
  subst' p refl x = x
  {-# COMPILE AGDA2HS subst' transparent #-}

zeroBinView
  : ∀ i → @0 i ≡ 0 → (@0 b : Bin n) (@0 inv : b encodes i)
  → BinView (MkBinInt i b inv)
zeroBinView {n = n} i p =
  subst' (λ i → (@0 b : Bin n) (@0 inv : b encodes i) → BinView (MkBinInt i b inv))
         (sym p)
    (λ b inv → subst'
      (λ b → (@0 inv : b encodes 0) → BinView (MkBinInt 0 b inv))
      (uniqBin zerosIs0 inv)
      (λ inv' → anything) inv)
{-# COMPILE AGDA2HS zeroBinView #-}


viewBin : (bi : BinInt n) → BinView bi
viewBin (MkBinInt i b inv) =
  if i == 0
    then (λ ⦃ p ⦄ → zeroBinView i (equality _ _ p) b inv)
    else anything
{-# COMPILE AGDA2HS viewBin #-}


{-

add  : Bin → Bin → Bin
add1 : Bin → Bin → Bin

add B     y     = y
add x     B     = x
add (x I) (y O) = add x y I
add (x O) (y I) = add x y I
add (x O) (y O) = add x y O
add (x I) (y I) = add1 x y O

add1 B B = B I
add1 B (y I) = add1 B y O
add1 B (y O) = y I
add1 (x I) B = add1 x B O
add1 (x I) (y I) = add1 x y I
add1 (x I) (y O) = add1 x y O
add1 (x O) B = x I
add1 (x O) (y I) = add1 x y O
add1 (x O) (y O) = add x y I


-}
-}

{-

open import Haskell.Prelude hiding (b)
open import Data.Bits

-- binary encoding
-- with a unique representation of zero
data Bin : Set where
  Z      : Bin
  2[_+1] : Bin → Bin
  2[_]+1 : Bin → Bin

private variable
  @0 n : Nat
  @0 b : Bin

-- succ : Bin → Bin
-- succ Z = 2[ Z ]+1
-- succ 2[ b +1] = 2[ succ b ]+1
-- succ 2[ b ]+1 = 2[ b +1]

-- data _encodes_ : Bin → Integer → Set where
--   Z     : Z encodes 0
--   2[+1] : ∀ {b i}
--         → b encodes (shiftR i 0 - 1)
--         → IsFalse (testBit i 0)
--         -- + proof that i is not zero?
--         → 2[ b +1] encodes i
--   2[]+1 : ∀ {b i}
--         → b encodes (shiftR i 0)
--         → IsTrue (testBit i 0)
--         → 2[ b ]+1 encodes i

toInteger : Bin → Integer
toInteger Z        = 0
toInteger 2[ b +1] = shiftL (succ (toInteger b)) 1
toInteger 2[ b ]+1 = setBit (shiftL (toInteger b) 1) 0

-- can I prove this?
postulate toInteger-inj : ∀ {x y} → toInteger x ≡ toInteger y → x ≡ y

record BInt : Set where
  constructor MkBInt
  field
    int    : Integer
    @0 bin : Bin
    @0 inv : int ≡ toInteger bin
{-# COMPILE AGDA2HS BInt #-}

z : BInt
z = MkBInt 0 Z refl
{-# COMPILE AGDA2HS z #-}

2*[_+1] : BInt → BInt
2*[ MkBInt i b p +1] =
  MkBInt
    (shiftL (succ i) 1)
    (2[ b +1])
    (cong (λ i → shiftL (succ i) 1) p)

2*[_]+1 : BInt → BInt
2*[ MkBInt i b p ]+1 =
  MkBInt
    (setBit (shiftL i 1) 0)
    (2[ b ]+1)
    (cong (λ i → setBit (shiftL i 1) 0) p)

-- literally the graph  of toInteger
-- (or the pseudo-inverse?)
data _encodes_ : @0 Bin → @0 Integer → Set where
  Z     : Z encodes 0
  2[+1] : ∀ {@0 b i}
        → IsFalse (testBit i 0)
        → IsFalse (i == 0) -- maybe IsTrue (i > 0) ?
        → b        encodes pred (shiftR i 1)
        → 2[ b +1] encodes i
  2[]+1 : ∀ {@0 b i}
        → IsTrue (testBit i 0)
        → b        encodes shiftR i 1
        → 2[ b ]+1 encodes i

private
  schrodinger : ∀ {b} → IsTrue b → IsFalse b → ⊥
  schrodinger itsTrue ()

  irrIsTrue : ∀ {b} (p q : IsTrue b) → p ≡ q
  irrIsTrue itsTrue itsTrue = refl

  irrIsFalse : ∀ {b} (p q : IsFalse b) → p ≡ q
  irrIsFalse itsFalse itsFalse = refl

@0 irrencode : ∀ {b i} (p q : b encodes i) → p ≡ q
irrencode Z Z = refl
irrencode (2[+1] t1 n1 p) (2[+1] t2 n2 q)
  rewrite irrencode p q
        | irrIsFalse t1 t2
        | irrIsFalse n1 n2
        = refl
irrencode (2[]+1 t1 p) (2[]+1 t2 q)
  rewrite irrencode p q
        | irrIsTrue t1 t2
        = refl

@0 uniqencode : ∀ {a b i} → a encodes i → b encodes i → a ≡ b
uniqencode (Z           ) (Z           ) = refl
uniqencode (2[+1] _ _ p ) (2[+1] _ _ q ) = cong 2[_+1] (uniqencode p q)
uniqencode (Z           ) (2[]+1 t _   ) = magic (schrodinger t testBit0)
uniqencode (2[+1] t1 _ p) (2[]+1 t2 q  ) = magic (schrodinger t2 t1)
uniqencode (2[]+1 t1 p  ) (Z           ) = magic (schrodinger t1 testBit0)
uniqencode (2[]+1 t1 p  ) (2[+1] t2 _ q) = magic (schrodinger t1 t2)
uniqencode (2[]+1 _ p   ) (2[]+1 _ q   ) = cong 2[_]+1 (uniqencode p q)

data View : @0 BInt → Set where
  VZ       : View z
  VTwoSucc : ∀ bi → View (2*[ bi +1])
  VSuccTwo : ∀ bi → View (2*[ bi ]+1)

private
  subst' : (@0 p : @0 a → Set) {@0 x y : a} → @0 x ≡ y → p x → p y
  subst' p refl z = z
  {-# COMPILE AGDA2HS subst' transparent #-}

  uip : {@0 x y : a} (p q : x ≡ y) → p ≡ q
  uip refl refl = refl

  isTrue : ∀ {b} → b ≡ True → IsTrue b
  isTrue refl = IsTrue.itsTrue
  
  isFalse : ∀ {b} → b ≡ False → IsFalse b
  isFalse refl = IsFalse.itsFalse

-- things needed for the SuccTwo case
-- SHOULD be provable
postulate
  one : (i : Integer)
      → IsTrue (testBit i 0)
      → setBit (shiftL (shiftR i 1) 1) 0 ≡ i

  two : (i : Integer)
      → IsFalse (testBit i 0)
      → IsFalse (i == 0)
      → shiftL (succ (pred i)) 1 ≡ i

view : ∀ bi → View bi
view (MkBInt i b inv) =
  if i == 0 then
    (λ ⦃ i==0 ⦄ →
       subst'
         (λ i → (@0 inv : i ≡ toInteger b) → View (MkBInt i b inv))
         (sym (equality _ _ i==0))
         (λ inv →
            subst' (λ b → (@0 inv : 0 ≡ toInteger b) → View (MkBInt 0 b inv))
                   (toInteger-inj inv)
                   (λ inv →
                      subst'
                         (λ inv → View (MkBInt 0 Z inv))
                         (uip refl inv)
                         VZ)
                   inv)
         inv)
  else λ ⦃ i/=0 ⦄ →
    if testBit i 0 then
      (λ ⦃ bit==1 ⦄ →
         subst' (λ i → (@0 inv : i ≡ toInteger b) → View (MkBInt i b inv))
                (one i (isTrue bit==1))
                (λ inv → {!!})
                inv)
    else
      (λ ⦃ bit==0 ⦄ → {!!})

-- complete binary trees
------------------------

data Tree (a : Set) : @0 Nat → Set where
  Leaf : a → Tree a 0
  Node : (l r : Tree a n) → Tree a (suc n)
{-# COMPILE AGDA2HS Tree #-}

data HTree (p : @0 a → Set) : @0 Tree a n → Set where
  HLeaf : ∀ {@0 x} → p x → HTree p (Leaf x)
  HNode : ∀ {@0 l r : Tree a n} → HTree p l → HTree p r → HTree p (Node l r)
{-# COMPILE AGDA2HS HTree #-}

-- random-access lists
----------------------

data BTree (a : Set) : @0 Bin → @0 Nat → Set where
  BLeaf   : BTree a Z n
  BTwoAdd : BTree a b (suc n) → Tree a n       → BTree a 2[ b ]+1 n
  BAddTwo : BTree a b (suc n) → Tree a (suc n) → BTree a 2[ b +1] n
{-# COMPILE AGDA2HS BTree #-}

pattern 2[_]+_ h t = BTwoAdd h t
pattern 2[_+_] h t = BAddTwo h t

data HBTree (p : @0 a → Set) : @0 BTree a b n → Set where
  HBLeaf   : HBTree p {n = n} BLeaf
  HBTwoAdd : {@0 bt : BTree a b (suc n)} {@0 t : Tree a n}
           → HBTree p bt → HTree p t
           → HBTree p (2[ bt ]+ t)
  HBAddTwo : {@0 bt : BTree a b (suc n)} {@0 t : Tree a (suc n)}
           → HBTree p bt → HTree p t
           → HBTree p (2[ bt + t ])
{-# COMPILE AGDA2HS HBTree #-}

pattern 2[_]+_ h t = HBTwoAdd h t
pattern 2[_+_] h t = HBAddTwo h t

-}
