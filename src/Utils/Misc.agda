module Utils.Misc where

open import Agda.Builtin.Equality
open import Haskell.Prim

subst
  : ∀ {@0 a : Set}
    (@0 f : @0 a → Set)
    {@0 x y}
  → @0 x ≡ y → f x → f y
subst f refl x = x
{-# COMPILE AGDA2HS subst transparent #-}

dsubst₂ : ∀ {@0 a : Set} {@0 b : @0 a → Set} (@0 c : (@0 x : a) → @0 b x → Set)
            {@0 x₁ x₂ y₁ y₂} (@0 p : x₁ ≡ x₂) → @0 subst b p y₁ ≡ y₂
        → c x₁ y₁ → c x₂ y₂
dsubst₂ C refl refl c = c
{-# COMPILE AGDA2HS dsubst₂ transparent #-}

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

let0 : {@0 a b : Set} (@0 x : a) (f : (@0 y : a) → @0 ⦃ y ≡ x ⦄ → b) → b
let0 x f = f x
{-# COMPILE AGDA2HS let0 transparent #-}
