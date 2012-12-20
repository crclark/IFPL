{-Author: Connor Clark
Description: implementation of the untyped lambda calculus.
To be used as a reference implementation to compare more efficient 
implementations to.
-}

module LC where

import Constants as C
import Data.List
import Variables
import Pretty

data LC = LCConstant C.Constant
          | LCVar Variable
          | LCApp LC LC
          | LCAbs Variable LC
          | LCY
          | LCIf --COND deprecated
          | LCADT Int [LC] --Int is sum constructor tag todo: consider replacing this with Church-encoded data structures, just because that's more fun.
          deriving (Show, Read, Ord, Eq)

instance Pretty LC where
 pretty (LCConstant c) = pretty c
 pretty (LCVar v) = v
 pretty (LCApp x (LCConstant c)) = pretty x ++ " " ++ pretty c
 pretty (LCApp abs@(LCAbs _ _) y) = "(" ++ pretty abs ++ ")" ++ pretty y 
 pretty (LCApp x y) = pretty x ++ " (" ++ pretty y ++ ")"
 pretty (LCAbs var body) = "\\" ++ var ++ " -> "  ++ pretty body
 pretty LCY = "Y"
 pretty LCIf = "IF"
          

--freeVars returns the free variables in a given lambda calculus term
freeVars :: LC -> [Variable]
freeVars (LCConstant c) = []
freeVars (LCVar x) = [x]
freeVars (LCApp x y) = nub $ freeVars x ++ freeVars y
freeVars (LCAbs var body) = delete var $ freeVars body
freeVars LCY = []
freeVars LCIf = []
freeVars (LCADT _ ts) = nub $ concatMap freeVars ts

--boundVars returns the bound vars in a given lambda calculus term
boundVars :: LC -> [Variable]
boundVars (LCConstant c) = []
boundVars (LCVar x) = []
boundVars (LCApp x y) = nub $ boundVars x ++ boundVars y
boundVars (LCAbs var body) = if var `elem` (freeVars body) 
                                then var : boundVars body
                                else boundVars body

--one step of leftmost outermost reduction
smallStep :: LC -> LC

--reduce constant expressions:
smallStep (LCConstant c) = LCConstant $ constantSmallStep c

--reduce conditionals starting with Bools:
smallStep (LCApp (LCApp (LCApp LCIf (LCConstant (C.BOOL True))) y) z) = y
smallStep (LCApp (LCApp (LCApp LCIf (LCConstant (C.BOOL False))) y) z) = z
--otherwise, a conditional needs to evaluate its if-term:
smallStep (LCApp (LCApp (LCApp LCIf x) y) z) = LCApp (LCApp (LCApp LCIf (smallStep x)) y) z

--actual beta reduction:
smallStep (LCApp (LCAbs var body) arg) =  sub arg var body --beta reduction! See def of sub below.

--Unpacks a sum type and applies the given function to its innards:
smallStep (LCApp 
                (LCApp (LCConstant (C.UNPACK_SUM x arity)) f) 
                (LCADT y zs)) = if x == y --check that the right constructor has been used
                                   then foldl1 LCApp (f:zs) --if so, apply
                                   else LCConstant C.FAIL --otherwise, go to the next pattern match
--recursive case: evaluate arg far enough to pattern match on it:
smallStep (LCApp 
                left@(LCApp (LCConstant (C.UNPACK_SUM x arity)) f)
                nonADT) = LCApp left (smallStep nonADT)
                                   
--Unpacks a product type and applies the given function to its innards:
smallStep (LCApp 
                (LCApp (LCConstant (C.UNPACK_PRODUCT arity)) f) 
                (LCADT _ zs)) = foldl1 LCApp (f:zs)
--recursive case: evaluate argument enough to pattern match on it:
smallStep (LCApp
                left@(LCApp (LCConstant (C.UNPACK_PRODUCT arity)) f)
                nonADT) = LCApp left (smallStep nonADT)

--pack a nullary sum constructor:
smallStep (LCApp (LCConstant (C.PACK_SUM d 0)) (LCConstant C.NULL_PACK_ARG)) = LCADT d []

--packs a sum type. The arity field is decremented each time PACK_SUM is partially applied.
--That keeps track of when to finish packing.
smallStep (LCApp 
                (LCApp (LCConstant (C.PACK_SUM d0 arity)) (LCADT d1 xs)) 
                term) = if arity > 1 
                           then LCApp (LCConstant (C.PACK_SUM d0 (arity - 1))) (LCADT d1 (xs ++ [term]))
                           else LCADT d1 (xs ++ [term])
                           
--last step of packing. All that's left is a used-up pack statement of arity 0. todo: what if it is supposed to be arity 0? Make sure that case works right.
smallStep (LCApp (LCConstant (C.PACK_SUM _ 0)) adt@(LCADT d xs)) = adt

--first step of packing. No partially applied ADT present yet.
smallStep (LCApp (LCConstant (C.PACK_SUM d arity)) term) = LCApp (LCConstant (C.PACK_SUM d (arity - 1))) (LCADT d [term])

--analogous packing steps for product types
smallStep (LCApp (LCConstant (C.PACK_PRODUCT 0)) (LCConstant C.NULL_PACK_ARG)) = LCADT (-1) []

smallStep (LCApp (LCApp (LCConstant (C.PACK_PRODUCT arity)) (LCADT _ xs)) term) = if arity > 1 
                                                                                        then LCApp (LCConstant (C.PACK_PRODUCT (arity - 1))) (LCADT (-1) (xs ++ [term]))
                                                                                        else LCADT (-1) (xs ++ [term])
--todo: same as todo for the analogous pattern-match for PACK_SUM
smallStep (LCApp (LCConstant (C.PACK_PRODUCT 0)) adt@(LCADT d xs)) = adt

smallStep (LCApp (LCConstant (C.PACK_PRODUCT arity)) term) = LCApp (LCConstant (C.PACK_PRODUCT (arity - 1))) (LCADT (-1) [term])

--A constant applied to a constant is turned into a "Constant Application" so that it can be evaluated by the separate eval function for constant expressions.
smallStep (LCApp (LCConstant x) (LCConstant y)) = LCConstant $ C.ConstantApp x y

--FATBAR reduction rules:
smallStep (LCApp (LCApp (LCConstant C.FATBAR) (LCConstant C.FAIL)) b) = b

smallStep (LCApp (LCApp (LCConstant C.FATBAR) a) b) = a

--SEL reduction rule:
smallStep (LCApp (LCConstant (C.SEL n)) (LCADT _ xs)) = xs !! n

--CASE_T reduction rule translates to a lambda function, generated on the fly: --todo: test thoroughly
smallStep (LCApp (LCConstant (C.CASE_T n)) (LCADT i _)) = selectIthFromNArgs i n

--inductive case for constants
smallStep (LCApp (LCConstant c) y) = LCApp (LCConstant c) (smallStep y) --todo: test terms with constants more

--Built-in fixpoint combinator implementation
smallStep (LCApp LCY x) = LCApp x (LCApp LCY x)

--leftmost rule
smallStep (LCApp x y) = LCApp (smallStep x) y 

--stuck/fully evaluated terms
smallStep x = x

--evaluates a term to normal form
eval :: LC -> LC
eval = until (\x -> LC.smallStep x == x) LC.smallStep --todo: replace with something faster

selectIthFromNArgs :: Int -> Int -> LC
selectIthFromNArgs i n = foldr LCAbs ith vars
                        where vars = take n variables
                              ith = LCVar $ vars !! (i - 1)

--substitutes LC term m for free occurrences of x in term. Does alpha conversion as necessary.
sub :: LC -> Variable -> LC -> LC
sub m x (LCVar z) = if z == x then m else LCVar z
sub m x (LCApp e f) = LCApp (sub m x e) (sub m x f)
sub m x (LCAbs y body) | x == y = LCAbs y body 
                       | notElem x (freeVars body) || notElem y (freeVars m) = LCAbs y (sub m x body)
                       | otherwise = LCAbs z (sub m x (sub (LCVar z) y body))
                            where z = head unusedVars
                                        where unusedVars = variables \\ (freeVars body ++ freeVars m)
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

--implementing factorial with built-in Y combinator:
testFac = LCApp LCY  $ LCAbs "fac" $ LCAbs "n" $ LCApp (LCApp (LCApp LCIf condition) baseCase) recursiveCase
  where condition = (LCApp (LCApp (LCConstant C.EQUALS) (LCVar "n")) (LCConstant $ C.INT 0))
        baseCase = LCConstant $ C.INT 1
        recursiveCase = LCApp (LCApp (LCConstant C.MULT) (LCVar "n")) (LCApp (LCVar "fac") (LCApp (LCApp (LCConstant C.MINUS) (LCVar "n")) (LCConstant $ C.INT 1))) 

testY = LCApp LCY $ LCAbs "self" $ LCAbs "n" $ LCApp (LCApp (LCApp LCIf condition) baseCase) recursiveCase
  where condition = (LCApp (LCApp (LCConstant C.EQUALS) (LCVar "n")) (LCConstant $ C.INT 0))
        baseCase = LCConstant $ C.INT 1
        recursiveCase = LCApp (LCVar "self") $ LCApp (LCApp (LCConstant C.MINUS) (LCVar "n")) (LCConstant $ C.INT 1)

testCase :: LC
testCase = LCApp reflect (LCADT 2 [LCConstant $ INT 5, LCConstant $ INT 8])
            where reflect = LCAbs "t" $ LCApp (LCApp (LCApp (LCConstant $ CASE_T 2) (LCVar "t"))
                                                     leafCase)
                                              branchCase
                             where leafCase = LCApp (LCApp (LCConstant $ UNPACK_SUM 1 1) 
                                                           (LCAbs "n" $ LCApp (LCConstant $ PACK_SUM 1 1) (LCVar "n"))
                                                    )
                                                    (LCVar "t")
                                   branchCase = LCApp (LCApp (LCConstant $ UNPACK_SUM 2 2)
                                                             (LCAbs "t1" $ LCAbs "t2" $ LCApp (LCApp (LCConstant $ PACK_SUM 2 2) (LCApp (LCVar "reflect") (LCVar "t2")))
                                                                                              (LCApp (LCVar "reflect") (LCVar "t1"))
                                                             )
                                                      )
                                                      (LCVar "t")

                                                     
