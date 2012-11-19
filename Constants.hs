{-
Author: Connor Clark
AST for constant expressions, such as math ops, list ops, etc.
Also, a shallowly-embedded non-strict evaluator for same.
Other evaluators to be added later.
These aren't really constants anymore, since some constant operations
can return anything. Now Constant t is a Constant for the language t.
The data constructor TERM holds a term in the language t.
This allows conditional statements to hold arbitrary code.
TODO: make AND and OR less strict! Or leave them to be implemented within the language...
-}

module Constants where

import Pretty

data Constant   = ConstantApp Constant Constant 
                  | EQUALS
                  | PLUS
                  | MINUS
                  | MULT
                  | DIV
                  | MOD
                  | CONS
                  | NIL
                  | COND
                  | AND
                  | OR
                  | NOT
                  | INT Int
                  | CHAR Char
                  | BOOL Bool
                     deriving (Show, Read, Eq, Ord)

--constantSmallStep does one step of evaluation. To eval completely, use eval.
constantSmallStep :: Constant -> Constant
--EQUALS-- base case:
constantSmallStep (ConstantApp (ConstantApp EQUALS x) y) = if constantNormalForm x && constantNormalForm y then BOOL $ x == y else (ConstantApp (ConstantApp EQUALS (constantSmallStep x)) (constantSmallStep y))
--PLUS base case:
constantSmallStep (ConstantApp (ConstantApp PLUS (INT x)) (INT y)) = INT $ x+y
--PLUS inductive case:
constantSmallStep (ConstantApp (ConstantApp PLUS x) y) = ConstantApp (ConstantApp PLUS (constantSmallStep x)) (constantSmallStep y)
--MINUS base case:
constantSmallStep (ConstantApp (ConstantApp MINUS (INT x)) (INT y)) = INT $ x - y
--MINUS inductive case:
constantSmallStep (ConstantApp (ConstantApp MINUS x) y) = ConstantApp (ConstantApp MINUS (constantSmallStep x)) (constantSmallStep y)
--MULT base case:
constantSmallStep (ConstantApp (ConstantApp MULT (INT x)) (INT y)) = INT $ x*y
--MULT inductive case:
constantSmallStep (ConstantApp (ConstantApp MULT x) y) = ConstantApp (ConstantApp MULT (constantSmallStep x)) (constantSmallStep y)
--DIV base case: 
constantSmallStep (ConstantApp (ConstantApp DIV (INT x)) (INT y)) = INT $ x `div` y
--DIV inductive case:
constantSmallStep (ConstantApp (ConstantApp DIV x) y) = ConstantApp (ConstantApp DIV (constantSmallStep x)) (constantSmallStep y)
--MOD base case:
constantSmallStep (ConstantApp (ConstantApp MOD (INT x)) (INT y)) = INT $ x `mod` y
--MOD inductive case:
constantSmallStep (ConstantApp (ConstantApp MOD x) y) = ConstantApp (ConstantApp MOD (constantSmallStep x)) (constantSmallStep y)
--COND base case:
constantSmallStep (ConstantApp (ConstantApp (ConstantApp COND (BOOL c)) x) y) = if c then x else y
--COND inductive case:
constantSmallStep (ConstantApp (ConstantApp (ConstantApp COND c) y) z) = ConstantApp (ConstantApp (ConstantApp COND (constantSmallStep c)) y) z
--AND base case:
constantSmallStep (ConstantApp (ConstantApp AND (BOOL x)) (BOOL y)) = BOOL $ x && y
--AND inductive case:
constantSmallStep (ConstantApp (ConstantApp AND x) y) = ConstantApp (ConstantApp AND (constantSmallStep x)) (constantSmallStep y)
--OR base case:
constantSmallStep (ConstantApp (ConstantApp OR (BOOL x)) (BOOL y)) = BOOL $ x || y
--OR inductive case:
constantSmallStep (ConstantApp (ConstantApp OR x) y) = ConstantApp (ConstantApp OR (constantSmallStep x)) (constantSmallStep y)
--NOT base case:
constantSmallStep (ConstantApp NOT (BOOL x)) = BOOL $ not x
--NOT inductive case:
constantSmallStep (ConstantApp NOT x) = ConstantApp NOT (constantSmallStep x)
--basest case!
constantSmallStep x = x

constantEval :: Constant -> Constant
constantEval = until (\x -> constantSmallStep x == x) constantSmallStep

constantNormalForm :: Constant -> Bool
constantNormalForm (ConstantApp _ _) = False
constantNormalForm _ = True

instance Pretty Constant where
 pretty (ConstantApp x y) = "(" ++ pretty x ++ ") " ++ pretty y
 pretty EQUALS = "=="
 pretty PLUS = "+"
 pretty MINUS = "-"
 pretty MULT = "*"
 pretty DIV = "\\"
 pretty MOD = "MOD"
 pretty CONS = ":"
 pretty NIL = "[]"
 pretty COND = "COND"
 pretty AND = "AND"
 pretty OR = "OR"
 pretty NOT = "NOT"
 pretty (INT x) = show x
 pretty (CHAR x) = show x
 pretty (BOOL x) = show x
