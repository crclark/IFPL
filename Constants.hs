{-
Author: Connor Clark
AST for constant expressions, such as math ops, list ops, etc.
Also, a shallowly-embedded non-strict evaluator for same.
Other evaluators to be added later.
TODO: make AND and OR less strict! Or leave them to be implemented within the language...
-}

module Constants where

data Constant = ConstantApp Constant Constant
                | PLUS
                | MINUS
                | MULT
                | DIV
                | MOD
                | CONS
                | NIL
                | COND
                | TRUE
                | FALSE
                | AND
                | OR
                | NOT
                | INT Int
                | CHAR Char
                | BOOL Bool
                deriving (Show, Read, Eq, Ord)

--smallStep does one step of evaluation. To eval completely, use eval.
smallStep :: Constant -> Constant
--PLUS base case:
smallStep (ConstantApp (ConstantApp PLUS (INT x)) (INT y)) = INT $ x+y
--PLUS inductive case:
smallStep (ConstantApp (ConstantApp PLUS x) y) = ConstantApp (ConstantApp PLUS (smallStep x)) (smallStep y)
--MINUS base case:
smallStep (ConstantApp (ConstantApp MINUS (INT x)) (INT y)) = INT $ x - y
--MINUS inductive case:
smallStep (ConstantApp (ConstantApp MINUS x) y) = ConstantApp (ConstantApp MINUS (smallStep x)) (smallStep y)
--MULT base case:
smallStep (ConstantApp (ConstantApp MULT (INT x)) (INT y)) = INT $ x*y
--MULT inductive case:
smallStep (ConstantApp (ConstantApp MULT x) y) = ConstantApp (ConstantApp MULT (smallStep x)) (smallStep y)
--DIV base case: 
smallStep (ConstantApp (ConstantApp DIV (INT x)) (INT y)) = INT $ x `div` y
--DIV inductive case:
smallStep (ConstantApp (ConstantApp DIV x) y) = ConstantApp (ConstantApp DIV (smallStep x)) (smallStep y)
--MOD base case:
smallStep (ConstantApp (ConstantApp MOD (INT x)) (INT y)) = INT $ x `mod` y
--MOD inductive case:
smallStep (ConstantApp (ConstantApp MOD x) y) = ConstantApp (ConstantApp MOD (smallStep x)) (smallStep y)
--COND base case:
smallStep (ConstantApp (ConstantApp (ConstantApp COND (BOOL c)) x) y) = if c then x else y
--COND inductive case:
smallStep (ConstantApp (ConstantApp (ConstantApp COND c) y) z) = ConstantApp (ConstantApp (ConstantApp COND (smallStep c)) y) z
--AND base case:
smallStep (ConstantApp (ConstantApp AND (BOOL x)) (BOOL y)) = BOOL $ x && y
--AND inductive case:
smallStep (ConstantApp (ConstantApp AND x) y) = ConstantApp (ConstantApp AND (smallStep x)) (smallStep y)
--OR base case:
smallStep (ConstantApp (ConstantApp OR (BOOL x)) (BOOL y)) = BOOL $ x || y
--OR inductive case:
smallStep (ConstantApp (ConstantApp OR x) y) = ConstantApp (ConstantApp OR (smallStep x)) (smallStep y)
--NOT base case:
smallStep (ConstantApp NOT (BOOL x)) = BOOL $ not x
--NOT inductive case:
smallStep (ConstantApp NOT x) = ConstantApp NOT (smallStep x)
--basest case!
smallStep x = x

eval :: Constant -> Constant
eval = until (\x -> smallStep x == x) smallStep
