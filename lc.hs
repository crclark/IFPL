{-Author: Connor Clark
Description: implementation of the untyped lambda calculus.
To be used as a reference implementation to compare more efficient 
implementations to.
-}

data LC = LCConstant Char --todo: define a real Constant type and populate it with values and functions.
          | LCVar Char
          | LCApp LC LC
          | LCAbs Char LC
          deriving (Show, Read, Ord, Eq)
