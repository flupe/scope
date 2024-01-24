{-# OPTIONS --prop #-}
module Test4 where


open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_==_)


-- experiment at trying to formalize what it means
-- to have an inductive view of a concrete type

-- NOTE: make constructors explicit in the encoding?

-- prelude
----------

record Lift i {j} (A : Set j) : Set (i ⊔ j) where
  constructor lift
  field unlift : A

data Fin : Nat → Set where
  fz : ∀ {n} → Fin (suc n)
  fs : ∀ {n} → Fin n → Fin (suc n)

data Squash (A : Set) : Prop where
  [_] : A → Squash A

_×_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A λ _ → B

_∘_ : ∀ {a b c} {@0 a : Set a} {@0 b : a → Set b} {@0 c : ∀ {x} → b x → Set c}
    → (g : ∀ {x} (y : b x) → c y) (f : ∀ x → b x)
    → ∀ x → c (f x)
(g ∘ f) x = g (f x)

Pred : ∀ {l} → Set l → Set (l ⊔ lsuc lzero)
Pred A = A → Prop


-- datatype-generic tooling
---------------------------

data Desc : Set₁ where
  κ : Desc
  σ : (S : Set) (T : S → Desc) → Desc
  ι : Desc → Desc

⟦_⟧ : ∀ {i} → Desc → Set i → Set i
⟦ κ     ⟧ X = Lift _ ⊤
⟦ σ S T ⟧ X = Σ S (λ s → ⟦ T s ⟧ X)
⟦ ι D   ⟧ X = X × ⟦ D ⟧ X

-- ⟦ D ⟧ is an endofunctor

map⟦⟧ : ∀ {i j} {X : Set i} {Y : Set j} (f : X → Y) D → ⟦ D ⟧ X → ⟦ D ⟧ Y
map⟦⟧ f (κ    ) (    x) = lift tt
map⟦⟧ f (σ S T) (s , x) = s   , map⟦⟧ f (T s) x
map⟦⟧ f (ι D  ) (r , x) = f r , map⟦⟧ f D x

-- μ D is the least fixed point of ⟦ D ⟧

data μ (D : Desc) : Set where
  ⟨_⟩ : ⟦ D ⟧ (μ D) → μ D


-- Allₚ : ∀ {l D} {A : Set l} (P : ⟦ D ⟧ (Pred A) → Pred A) → 
-- Allₚ : ∀ {l D} {A : Set l} (P : ⟦ D ⟧ (Pred A) → Pred A) → μ D → Pred A
-- Allₚ P ⟨ x ⟩ = {!!}


-- generic elim
---------------

module _ {l D} (P : μ D → Set l) where

  All' : ∀ D' → ⟦ D' ⟧ (μ D) → Set l
  All' (κ    ) x = Lift _ ⊤
  All' (σ S T) (s , x) = All' (T s) x
  All' (ι D' ) (r , x) = P r × All' D' x
  
  All : μ D → Set l
  All ⟨ x ⟩ = All' D x

  module _ (h : ∀ x → All x → P x) where

    all' : ∀ D' → ∀ x → All' D' x
    elim : ∀ x → P x
    
    all' (κ    ) x = lift tt
    all' (σ S T) (s , x) = all' (T s) x
    all' (ι D' ) (r , x) = elim r , all' D' x
    
    elim x@(⟨ x' ⟩) = h x (all' _ x')


-- generic fold
---------------

Alg : ∀ {a} → Desc → Set a → Set a
Alg D A = ⟦ D ⟧ A → A

module _ {a D} {@0 A : Set a} (alg : Alg D A) where

  -- TODO: refactor + prove extensional consistency

  fold'' : ∀ D' → Alg D' A → ⟦ D' ⟧ A → A
  fold'' (κ    ) alg (    x) = alg (lift tt)
  fold'' (σ S T) alg (s , x) = fold'' (T s) (alg ∘ (s ,_)) x
  fold'' (ι D' ) alg (r , x) = fold'' D' (alg ∘ (r ,_)) x

  fold : μ D → A

  -- fold' = map⟦⟧ fold
  fold' : ∀ D' → ⟦ D' ⟧ (μ D) → ⟦ D' ⟧ A
  fold' (κ    ) (    x) = lift tt
  fold' (σ S T) (s , x) = s , fold' (T s) x
  fold' (ι D' ) (r , x) = fold r , fold' D' x

  fold ⟨ x ⟩ = fold'' D alg (fold' D x)



-- signature for inductive views over type A
--------------------------------------------

record ViewSig (A : Set) : Set₁ where

  field
    -- | description of the inductive view
    D : Desc   

    -- | subset of values that can be viewed
    Correct : Pred A 

    -- | Encoding relation as a predicate transformer
    Enc : ⟦ D ⟧ A → Pred A → Pred A

  -- encoding relation (as a fold over the encoding algebra)
  _as_ : μ D → Pred A
  _as_ = {!!} -- fold Enc

  _as'_ : ⟦ D ⟧ (μ D) → Pred (⟦ D ⟧ A)
  _as'_ ds = {!!}

  field constr : Alg D A
        split  : ∀ x → {{ Correct x }} → ⟦ D ⟧ A

  field as-constr : ∀ ds vs → {{ ds as' vs }} → ⟨ ds ⟩ as constr vs

  encode : μ D → A
  encode = fold constr


module View {A : Set} (S : ViewSig A) where

  private open module S = ViewSig S

  record Encoded : Set where
    constructor packed
    field
      enc    : A
      @0 val : μ D
      inv    : val as enc

  open Encoded

  constrE : ⟦ D ⟧ Encoded → Encoded
  constrE xs = packed (constr (map⟦⟧ enc D xs))
                      ⟨ map⟦⟧ val D xs ⟩
                      ({!!})
  
  data View : @0 Encoded → Set where
    view : (xs : ⟦ D ⟧ Encoded) → View (constrE xs)

  inspect : ∀ v → View v
  inspect (packed e v v≈e) = {!!}

{-

-- demo
-------

module demo where

  open import Haskell.Prelude hiding (_,_; _,_,_)

  pattern Z   = true  ,     lift tt 
  pattern S n = false , n , lift tt

  pattern ze   = ⟨ Z   ⟩
  pattern su n = ⟨ S n ⟩


  intSig : ViewSig Integer
  intSig = record { S }
    where module S where
      -- viewing integers as peano nat
      D : Desc
      D = σ Bool λ { true  → κ ; false → ι κ }

      -- only non-negative integers can be viewed as such
      Correct : Pred Integer
      Correct i = Squash (IsTrue (i >= 0))
  
      Enc : Alg D (Pred Integer)
      Enc (Z  ) i = Squash (IsTrue (i == 0))
      Enc (S P) i = P (pred i)
  
      -- smart peano constructors
      constr : Alg D Integer
      constr Z     = 0
      constr (S i) = succ i

      -- NOTE(flupe): maybe too restrictive to only allow encoding relations as folds?
      _as_ : μ D → Pred Integer
      _as_ = fold Enc

      as-constr : ∀ ds vs → {{ {!!} }} → ⟨ ds ⟩ as constr vs
      as-constr ds vs = {!!}

      -- peeling off root constructor of valid integers
      split : ∀ i → {{ Correct i }} → ⟦ D ⟧ Integer
      split i = if (i == 0) then Z else S (pred i)


  open View intSig renaming (Encoded to IntNat)

  double : IntNat → IntNat
  double i with inspect i
  ... | view Z     = constrE Z
  ... | view (S i) = constrE (S (constrE (S (double i))))


module demo2 where

  open import Haskell.Prelude hiding (_,_; _,_,_)
  open import Data.Bits

  intSig : ViewSig Integer
  intSig = record { S }
    where module S where
      -- binary encoding
      D : Desc
      D = σ (Fin 3) λ where
        fz           → κ    -- 0     
        (fs fz)      → ι κ  -- 2[_+1]   (even)
        (fs (fs fz)) → ι κ  -- 2[_]+1   (odd )

      Correct : Pred Integer
      Correct i = Squash (IsTrue (i >= 0))
  
      Enc : Alg D (Pred Integer)
      Enc (fz ,             _) i = Squash (IsTrue (i == 0))
      Enc (fs fz ,      P , _) i = P (shiftR i 1) -- TODO: bitproof?
      Enc (fs (fs fz) , P , _) i = P (shiftR i 1)

      -- Enc (Z  ) i = Squash (IsTrue (i == 0))
      -- Enc (S P) i = P (pred i)
  
      constr : Alg D Integer
      constr (fz ,             _) = 0
      constr (fs fz ,      i , _) = shiftL i 1            -- (even)
      constr (fs (fs fz) , i , _) = setBit (shiftL i 1) 0 -- (odd )

      -- NOTE(flupe): maybe too restrictive to only allow encoding relations as folds?
      _as_ : μ D → Pred Integer
      _as_ = fold Enc

      as-constr : ∀ ds vs → {{ {!!} }} → ⟨ ds ⟩ as constr vs
      as-constr ds vs = {!!}

      -- peeling off root constructor of valid integers
      split : ∀ i → {{ Correct i }} → ⟦ D ⟧ Integer
      split i = if (i == 0) then {!!} else {!!}

-}
