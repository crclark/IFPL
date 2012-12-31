module LangAST where

import ELC --for translation
import Constants as C
import Variables
import Data.List (find, (\\))

data Expr = ExprConstant C.Constant
            |ExprApp Expr Expr
            |ExprVar Variable
            |ExprIf 
            |ExprLetRec [(Pattern, Expr)] Expr
            deriving (Show, Read, Eq, Ord)

type Identifier = String

data Def = Def Identifier [([Pattern], Expr)] --function name, then a bunch of cases for different patterns. List of patterns for each case to accommodate n-ary functions.
     deriving (Show, Read, Eq, Ord)

defName :: Def -> Identifier
defName (Def i _) = i

--todo: support kinds other than *. Should only need to change front-end implementation.
data ADTDef = ADTDef TypeName [(Constructor, [TypeName])] 
     deriving (Show, Read, Eq, Ord)


exprToELC :: Expr -> ELC 
exprToELC (ExprConstant c) = ELCConstant c
exprToELC (ExprApp x y) = ELCApp (exprToELC x) (exprToELC y)
exprToELC (ExprVar v) = ELCVar v
exprToELC (ExprIf) = ELCIf
exprToELC (ExprLetRec bs t) = ELCLetRec bsTrans $ exprToELC t
                             where bsTrans = zip (map fst bs) ( map (exprToELC . snd) bs)

--defToELC translates a def to an ELC expression.
--note this strips off the definition's name. Make sure it is preserved by the caller.
defToELC :: Def -> ELC
defToELC (Def _ bs) = if numArgs == 0 
                         then exprToELC $ snd $ head $ bs 
                         else foldr ELCFatBar (ELCConstant C.FAIL) lambdaBs
                       where numArgs = (length . fst . head) bs
                             lambdaBs = map lambdaB bs
                             lambdaB (ps, e) = foldr ELCAbs (exprToELC e) ps 

--defToBinding translates a definition into a function name, function body pair.
--Also handles explicit self-recursion, as this is a convenient point at which we know the function's name.
defToBinding :: Def -> (Pattern, ELC)
defToBinding def = (PatternVar $ defName def, body)
                     where body = let elc = defToELC def in
                                    let newVar = head $ variables \\ freeVarsELC elc in
                                      if (defName def) `elem` (freeVarsELC elc)
                                         then recurseOn newVar (subst elc newVar (defName def))
                                         else elc
                           
  
--type ConstructorInfo = [(TypeName, [(Constructor, (Tag, Arity))])] 
buildConstructorInfo :: [ADTDef] -> ConstructorInfo
buildConstructorInfo = concatMap inner  
  where inner (ADTDef name bs) = [(name, zip (map fst bs) (zip [1..] (map (length . snd) bs)))] 

--defsToELC takes all the function defs of a program and translates them into a single ELC 
defsToELC :: [Def] -> ELC
defsToELC ds = if null bindings then mainELC else ELCLetRec bindings mainELC
               where (ourMain, lets) = splitOutMain ds
                     mainELC = defToELC ourMain
                     bindings = map defToBinding lets
                   
splitOutMain :: [Def] -> (Def,[Def])
splitOutMain ds = (ourMain, lets)
                  where ourMain = case find isMain ds of
                                   Just q -> q
                                   Nothing -> error "program entry point not found" 
                        lets = filter (not . isMain) ds
                        isMain = (== "main") . defName
