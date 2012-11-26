{-Author: Connor Clark
Description: Implements a basic "enriched lambda calculus"
for use as an intermediate language between a high-level 
functional language and the compiled/interpreted code.
todo: add letrecs to plain LC. IFPL p. 43 says it's more efficient.
-}

import Variables
import Constants as C
import LC 
import Data.List hiding (partition)
import Control.Monad

--abstract syntax for Enriched Lambda Calculus
data ELC = ELCConstant C.Constant 
           | ELCVar Variable
           | ELCApp ELC ELC
           | ELCAbs Pattern ELC --pattern-matching lambda abstraction
           | ELCLet Pattern ELC ELC --read as "Let pattern = elc in elc."
           | ELCLetRec [(Pattern, ELC)] ELC --read as "let these patterns equal the corresponding ELCs in ELC.
           | ELCFatBar ELC ELC --used in pattern matching
           | ELCCase Variable [Clause] --case statement for executing code based on what constructor the input was constructed with.
           | ELCIf --built-in if statement
            deriving (Show, Read, Ord, Eq)

--a Clause is a branch of a case statement, consisting of a constructor, variables to bind to the
--arguments of the constructor, and an ELC to evaluate.
data Clause = CLAUSE Constructor [Variable] ELC
              deriving (Show, Read, Ord, Eq)

--abstract syntax for valid patterns. For pattern matching.
data Pattern = PatternConstant C.Constant --e.g. fac 0 = 1 todo: implement support for this in match.
               | PatternVar Variable      --e.g. id x = x
               | PatternConstructor Constructor [Pattern] --e.g. head (x:xs) = x
                deriving (Show, Read, Ord, Eq)

--an equation is a pattern-matched ELC expression. 
--e.g. left (Tree l r) = l, except without the identifier "left".
--This seems redundant given the AST for ELC above, but is the format expected by match.
--This could probably be streamlined.
type Equation = ([Pattern], ELC)


--The stuff below is for translating pattern matching into FATBAR equivalents.
type Constructor = [Char] 

type TypeName = [Char]

type Arity = Int

--ConstructorInfo stores a list of type names, paired with their constructors and the 
--constructors' arities.
type ConstructorInfo = [(TypeName, [(Constructor, Arity)])] 

--ConstructorTags stores the tag id of each constructor for sum types.
--This allows sum constructors of the same arity and type to be differentiated.
type ConstructorTags = [(Constructor, Int)]

--looks up the arity of a constructor
arity :: ConstructorInfo -> Constructor -> Arity
arity info constructor = case (lookup constructor (join (map snd info))) of
                         Just x -> x
                         Nothing -> error "Unknown constructor referenced in pattern match"

--todo: verify that two types can't share a constructor name in legal Haskell/Miranda/whatever
--otherConstructors returns a list of all constructors of a type, given the name of one of its constructors
otherConstructors :: ConstructorInfo -> Constructor -> [Constructor]
otherConstructors info constructor = let constructorLists = (map (map fst) (map snd info))
                                         in join $ filter (elem constructor) constructorLists
                
isVar :: Equation -> Bool
isVar (PatternVar v : ps, _) = True
isVar _ = False

isCon :: Equation -> Bool
isCon (PatternConstructor c ps : ps2, _) = True
isCon _ = False

getCon (PatternConstructor c ps' : ps, e) = c

makeVar :: Int -> Variable
makeVar k = "_u" ++ show k

--match internals
partition :: Eq b => (a -> b) -> [a] -> [[a]]
partition f [] = []
partition f [x] = [[x]]
partition f (x : x' : xs) | f x == f x' = tack x (partition f (x':xs))
                          | otherwise = [x] : partition f (x':xs)
                          where tack y yss = (y : head yss) : tail yss

--todo: what about constants in patterns? like fac 0 = 1
matchVarCon :: Int -> [Variable] ->  ConstructorInfo ->[Equation] -> ELC -> ELC
matchVarCon k us info qs def | isVar (head qs) = matchVar k us qs def info
                             | isCon (head qs) = matchCon k us qs def info
                               where matchVar k (u:us) qs def info = match k us [(ps, subst e u v) | (PatternVar v : ps, e) <-qs] def info
                                     matchCon k (u:us) qs def info = ELCCase u [matchClause c k (u:us) (choose c qs) def info | c <- cs]
                                                                      where cs = otherConstructors info (getCon (head qs))
                                     choose c qs = [q | q <- qs, getCon q == c]

--internal of match
matchClause :: Constructor -> Int -> [Variable] -> [Equation] -> ELC -> ConstructorInfo -> Clause
matchClause c k (u:us) qs def info = CLAUSE c us' (match (k'+k)
                                                         (us' ++ us)
                                                         [(ps'++ps,e) | (PatternConstructor c ps' : ps, e) <- qs]
                                                         def
                                                         info)
                                       where k' = arity info c
                                             us' = [makeVar (i+k) | i <- [1..k']]
    
--match takes a seed for new var names, a list of variables to match to an equation (the arguments),
-- a list of equations (the function), an ELC term that is right of all fatbars, and information on
--the types in our program, and returns a new ELC that contains no pattern matching, but instead
--just case statements. This step appears to be optional, but results in more efficient pattern-matching
match :: Int -> [Variable] -> [Equation] -> ELC -> ConstructorInfo -> ELC
match k [] qs def info = foldr ELCFatBar def [e | ([],e) <- qs]
match k (u:us) qs def info = foldr (matchVarCon k (u:us) info) def (partition isVar qs)

--in the expression ELC, substitute var1 for var2 --todo: what about bound vars? ignore? Book not helpful.
subst :: ELC -> Variable -> Variable -> ELC
subst (ELCConstant c) var1 var2 = ELCConstant c 
subst (ELCVar var) var1 var2 = if var == var2 then ELCVar var1 else ELCVar var
subst (ELCApp l r) var1 var2 = ELCApp (subst l var1 var2) (subst r var1 var2)
subst (ELCAbs pat t) var1 var2 = ELCAbs pat (subst t var1 var2) --todo: sub inside pattern?
subst (ELCLet pat t1 t2) var1 var2 = ELCLet pat (subst t1 var1 var2) (subst t2 var1 var2)--todo: both sides of let? pattern? 
subst (ELCLetRec pats t) var1 var2 = ELCLetRec [(p, subst e var1 var2)| (p,e) <- pats] (subst t var1 var2)
subst (ELCFatBar t1 t2) var1 var2 = ELCFatBar (subst t1 var1 var2) (subst t2 var1 var2)
subst (ELCCase var clauses) var1 var2 = if var == var2 
                                           then ELCCase var1 [substC x var1 var2 | x <- clauses] 
                                           else ELCCase var [substC x var1 var2 | x <- clauses] 
subst ELCIf _ _ = ELCIf

--internal for subst. todo: use a where statement or something.
substC :: Clause -> Variable -> Variable -> Clause
substC (CLAUSE constructor vars t) var1 var2 = CLAUSE constructor (map (\x -> if x == var2 then var1 else x) vars) (subst t var1 var2) 

{- --todo: the book wants subst:: ELC -> Variable -> Variable -> ELC, but not sure if they want to worry about shadowing or not. Will figure it out later
sub :: ELC -> Variable -> ELC -> ELC
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
-}


--translation function from ELC to LC. todo: finish
translate :: ELC -> LC
translate (ELCConstant c) = LCConstant c
translate (ELCVar v) = LCVar v
translate (ELCApp x y) = LCApp (translate x) (translate y)
translate (ELCAbs pat body) = undefined --todo: define
translate (ELCLet (PatternVar v) x y) = LCApp (LCAbs v (translate y)) (translate x)
translate (ELCLet pat x y) = undefined --todo: handle other pattern cases
translate (ELCLetRec bindings t) = undefined --todo
translate (ELCFatBar x y) = undefined --todo
translate (ELCCase var cases) = undefined --todo
translate (ELCIf) = LCIf


-----------------MATCH TEST---------------------------
{-This is a representation of the following function:
mappairs f [] ys = []
mappairs f (x:xs) [] = []
mappairs f (x:xs) (y:ys) = f x y : mappairs f xs ys
-}

testInfo :: ConstructorInfo
testInfo = [("List", [("Cons", 2), ("Nil",0)])]

testUs :: [Variable]
testUs = ["_u1", "_u2", "_u3"]

testQs :: [Equation]
testQs = [ ([PatternVar "f", PatternConstructor "Nil" [], PatternVar "ys"], ELCConstant NIL),
           ([PatternVar "f", PatternConstructor "Cons" [PatternVar "x", PatternVar "xs"], PatternConstructor "Nil" [] ], ELCConstant NIL),
           ([PatternVar "f", PatternConstructor "Cons" [PatternVar "x", PatternVar "xs"], PatternConstructor "Cons" [PatternVar "y", PatternVar "ys"]], ELCApp (ELCApp (ELCConstant CONS) (ELCApp (ELCApp (ELCVar "f") (ELCVar "x")) (ELCVar "y")) ) $ ELCApp (ELCApp (ELCApp (ELCVar "THISFUNCTION") (ELCVar "f")) (ELCVar "xs")) (ELCVar "ys") )
         ]
testMatch :: ELC
testMatch = match 3 testUs testQs (ELCVar "ERROR!!!") testInfo 
