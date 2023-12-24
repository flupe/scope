module Utils.Misc where

open import Agda.Builtin.Equality
open import Haskell.Prim

subst
  : ∀ {ℓ ℓ′} {@0 a : Set ℓ}
    (@0 f : @0 a → Set ℓ′)
    {@0 x y : a}
  → @0 x ≡ y → f x → f y
subst f refl x = x
{-# COMPILE AGDA2HS subst transparent #-}

@0 schrodinger : ∀ {b} → IsTrue b → IsFalse b → a
schrodinger itsTrue ()

@0 isTrue : ∀ {b} → b ≡ True → IsTrue b
isTrue refl = IsTrue.itsTrue

@0 isFalse : ∀ {b} → b ≡ False → IsFalse b
isFalse refl = IsFalse.itsFalse

@0 irrIsTrue : ∀ {b} (p q : IsTrue b) → p ≡ q
irrIsTrue itsTrue itsTrue = refl

@0 irrIsFalse : ∀ {b} (p q : IsFalse b) → p ≡ q
irrIsFalse itsFalse itsFalse = refl

@0 trueIs : ∀ {b} → IsTrue b → b ≡ True
trueIs itsTrue = refl

@0 cong₃ : {b : Set} (f : a → b → c → d) {x y : a} {z w : b} {u v : c}
      → x ≡ y → z ≡ w → u ≡ v
      → f x z u ≡ f y w v
cong₃ f refl refl refl = refl

-- subst₂ : {a b : Set} (p : a → b → Set) {x y : a} {z w : b}
--        → x ≡ y → z ≡ w → p x z → p y w
-- subst₂ p refl refl x = x

subst₂ : {@0 a b : Set} (@0 p : @0 a → @0 b → Set) {@0 x y : a} {@0 z w : b}
       → @0 x ≡ y → @0 z ≡ w → p x z → p y w
subst₂ p refl refl x = x
{-# COMPILE AGDA2HS subst₂ transparent #-}
