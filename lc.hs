{-Author: Connor Clark
Description: implementation of the untyped lambda calculus.
To be used as a reference implementation to compare more efficient 
implementations to.
-}

module LC where

import Constants as C
import Data.List

type Variable = String

data LC = LCConstant C.Constant 
          | LCVar Variable
          | LCApp LC LC
          | LCAbs Variable LC
          deriving (Show, Read, Ord, Eq)

--freeVars returns the free variables in a given lambda calculus term
freeVars :: LC -> [Variable]
freeVars (LCConstant c) = []
freeVars (LCVar x) = [x]
freeVars (LCApp x y) = nub $ freeVars x ++ freeVars y
freeVars (LCAbs var body) = delete var $ freeVars body

--boundVars returns the bound vars in a given lambda calculus term
boundVars :: LC -> [Variable]
boundVars (LCConstant c) = []
boundVars (LCVar x) = []
boundVars (LCApp x y) = nub $ boundVars x ++ boundVars y
boundVars (LCAbs var body) = if elem var (freeVars body) 
                                then var : (boundVars body)
                                else boundVars body

--one step of leftmost outermost reduction
smallStep :: LC -> LC
smallStep (LCConstant c) = LCConstant $ C.smallStep c
smallStep (LCApp (LCAbs var body) arg) =  sub arg var body --beta reduction! See def of sub below.
smallStep (LCApp (LCConstant x) (LCConstant y)) = LCConstant $ C.ConstantApp x y
smallStep (LCApp (LCConstant c) y) = LCApp (LCConstant c) (LC.smallStep y)
smallStep (LCApp x y) = LCApp (LC.smallStep x) y 
smallStep x = x

--evaluates a term to normal form
eval :: LC -> LC
eval = until (\x -> LC.smallStep x == x) LC.smallStep --todo: replace with something faster

--infinite supply of variable names, for alpha conversion
variables :: [Variable] 
variables = az ++ (concat $ map aznum [1..])
 where az = [[x] | x <- ['a'..'z']]
       aznum n = map (++ (show n)) az

--substitutes LC term m for free occurrences of x in term. Does alpha conversion as necessary.
sub :: LC -> Variable -> LC -> LC
sub m x (LCVar z) = if z == x then m else (LCVar z)
sub m x (LCApp e f) = LCApp (sub m x e) (sub m x f)
sub m x (LCAbs y body) = if x == y 
                              then LCAbs y body 
                              else if not (x `elem` (freeVars body)) || not (y `elem` (freeVars m))
                                      then LCAbs y (sub m x body)
                                      else LCAbs z (sub m x (sub (LCVar z) y body))
                                           where z = head unusedVars
                                                     where unusedVars = (variables \\ ((freeVars body) ++ (freeVars m)))
sub m x t = t --catch-all for constant expressions

--this term does not evaluate to a value
testTerm :: LC
testTerm = LCApp plusX weirdApp
 where plusX = LCApp (LCConstant C.PLUS) (LCVar "x")
       weirdApp = LCApp (LCAbs "x" (LCApp (LCApp (LCConstant C.PLUS) (LCVar "x")) (LCConstant (C.INT 1)))) (LCConstant (C.INT 4))

--this term does not evaluate to a value
testTerm2 :: LC
testTerm2 = LCAbs "x" (LCApp (LCApp (LCConstant C.PLUS) weirdApp) (LCVar "x"))
 where weirdApp = LCApp (LCAbs "y" (LCApp (LCApp (LCConstant C.PLUS) (LCVar "y")) (LCVar "z"))) (LCConstant (C.INT 7)) 

--this term should eval to 68
testTerm3 :: LC
testTerm3 = LCApp (LCApp (LCConstant C.PLUS) threeTimesFour) sevenTimesEight
 where threeTimesFour = LCApp (LCApp (LCConstant C.MULT) (LCConstant (C.INT 3))) (LCConstant (C.INT 4))
       sevenTimesEight = LCApp (LCApp (LCConstant C.MULT) (LCConstant (C.INT 7))) (LCConstant (C.INT 8))
