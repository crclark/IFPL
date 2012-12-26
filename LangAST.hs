module LangAST where

import ELC --for translation
import Constants as C
import Variables

data Expr = ExprConstant C.Constant
            |ExprApp Expr Expr
            |ExprVar Variable
            |ExprIf 
            |ExprLetRec [(Pattern, Expr)] Expr
            deriving (Show, Read, Eq, Ord)

type Identifier = String

data Def = Def Identifier [([Pattern], Expr)] --function name, then a bunch of cases for different patterns. List of patterns for each case to accommodate n-ary functions.
     deriving (Show, Read, Eq, Ord)

--todo: support kinds other than *. Should only need to change front-end implementation.
data ADTDef = ADTDef TypeName [(Constructor, [TypeName])] 
     deriving (Show, Read, Eq, Ord)


toELC :: Expr -> ELC 
toELC (ExprConstant c) = ELCConstant c
toELC (ExprApp x y) = ELCApp (toELC x) (toELC y)
toELC (ExprVar v) = ELCVar v
toELC (ExprIf) = ELCIf
toELC (ExprLetRec bs t) = ELCLetRec bsTrans $ toELC t
                             where bsTrans = zip (map fst bs) ( map (toELC . snd) bs)

--type ConstructorInfo = [(TypeName, [(Constructor, (Tag, Arity))])] 
buildConstructorInfo :: ADTDef -> ConstructorInfo
buildConstructorInfo (ADTDef name bs) = [(name, zip (map fst bs) (zip [1..] (map (length . snd) bs)))] 
