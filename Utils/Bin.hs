module Utils.Bin where

import Data.Bits (Bits(setBit, shiftL, shiftR, testBit))

newtype BinInt = BI{int :: Integer}

z :: BinInt
z = BI 0

i :: BinInt -> BinInt
i (BI i) = BI (setBit (shiftL i 1) 0)

o :: BinInt -> BinInt
o (BI i) = BI (shiftL i 1)

data BinView = VZ
             | VO BinInt
             | VI BinInt

view :: BinInt -> BinView
view (BI i)
  = if i == 0 then VZ else
      if testBit i 0 then VI (BI (shiftR i 1)) else anything

data Tree a = Leaf a
            | Node (Tree a) (Tree a)

data BTree' a = BTZ
              | BTO (BTree' a)
              | BTI (Tree a) (BTree' a)

type BTree a = BTree' a

