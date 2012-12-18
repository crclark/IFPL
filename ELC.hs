{-Author: Connor Clark
Description: Implements a basic "enriched lambda calculus"
for use as an intermediate language between a high-level 
functional language and the compiled/interpreted code.
todo: add letrecs to plain LC. IFPL p. 43 says it's more efficient.
todo: eliminate constructor names earlier in the process so I don't have to deal with them in ELC terms.
-}

import Variables
import Constants as C
import LC 
import Data.List hiding (partition)
import Data.Ord (comparing)
import Control.Monad
import Digraph --need to "sudo ghc-pkg expose ghc" for this to compile, now.
import Data.Hashable
import Data.Maybe (fromJust)

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
           | ELCY
            deriving (Show, Read, Ord, Eq)

instance Hashable ELC where
 hash = hash . show

--a Clause is a branch of a case statement, consisting of a constructor, variables to bind to the
--arguments of the constructor, and an ELC to evaluate.
data Clause = CLAUSE Constructor [Variable] ELC
              deriving (Show, Read, Ord, Eq)

--abstract syntax for valid patterns. For pattern matching.
data Pattern = PatternConstant C.Constant --e.g. fac 0 = 1 todo: implement support for this in match.
               | PatternVar Variable      --e.g. id x = x
               | PatternConstructor Constructor [Pattern] --e.g. head (x:xs) = x
                deriving (Show, Read, Ord, Eq)

instance Hashable Pattern where
 hash = hash . show

--an equation is a pattern-matched ELC expression. 
--e.g. left (Tree l r) = l, except without the identifier "left".
--This seems redundant given the AST for ELC above, but is the format expected by match.
--This could probably be streamlined.
type Equation = ([Pattern], ELC)


--The stuff below is for translating pattern matching into FATBAR equivalents.
type Constructor = [Char] 

type TypeName = [Char]

type Arity = Int

type Tag = Int --stores constructor tags (for identifying sum constructors)

--ConstructorInfo stores a list of type names, paired with their constructors and the 
--constructors' arities.
type ConstructorInfo = [(TypeName, [(Constructor, (Tag, Arity))])] 

--ConstructorTags stores the tag id of each constructor for sum types.
--This allows sum constructors of the same arity and type to be differentiated.
--if the constructor is for a product, the tag will be -1
type ConstructorTags = [(Constructor, Int)]

--gets tag of a given constructor
tag :: ConstructorInfo -> Constructor -> Int
tag info c = case lookup c (join (map snd info)) of
             Just (t, a) -> t
             Nothing -> error "Tried to get tag of non-existent constructor"

--true iff constructor is of a sum type
isSum :: ConstructorInfo -> Constructor -> Bool
isSum info c = if tag info c == -1 then False else True

--looks up the arity of a constructor
arity :: ConstructorInfo -> Constructor -> Arity
arity info constructor = case (lookup constructor (join (map snd info))) of
                         Just (t, a) -> t
                         Nothing -> error $ "Unknown constructor referenced in pattern match: " ++ constructor

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

irrefutable :: ConstructorInfo -> Pattern -> Bool
irrefutable _ (PatternVar v) = True
irrefutable _ (PatternConstant c) = False
irrefutable i (PatternConstructor c ps) = if not (isSum i c) && and (map (irrefutable i) ps) 
                                             then True
                                             else False

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

--translation function from ELC to LC. todo: finish
translate :: ConstructorInfo -> ELC -> LC
translate i = (translateInternal i) . (simplifyAllLets i)

--translateInternal handles the steps of translation AFTER simplification of let statements
translateInternal :: ConstructorInfo -> ELC -> LC 
translateInternal i (ELCConstant c) = LCConstant c
translateInternal i (ELCVar v) = LCVar v
translateInternal i (ELCApp x y) = LCApp (translateInternal i x) (translateInternal i y)
--Cases for pattern-matching lambda abstractions:
translateInternal i (ELCAbs (PatternConstant k) body) = LCAbs newVar $ LCApp (LCApp (LCApp LCIf (LCApp (LCApp (LCConstant C.EQUALS) (LCConstant k)) (LCVar "v"))) (translateInternal i body)) (LCConstant C.FAIL)
                                                 where newVar = head $ variables \\ freeVarsELC body
translateInternal i (ELCAbs (PatternConstructor c pats) body) = if isSum i c 
                                                         then LCApp (LCConstant (C.UNPACK_SUM (tag i c) (arity i c))) $ translateInternal i $ foldr ELCAbs body pats
                                                         else LCApp (LCConstant (C.UNPACK_PRODUCT (arity i c))) $ translateInternal i $ foldr ELCAbs body pats
--simple let case: only one that should be encountered here. All others handled by simplifyAllLets.
translateInternal i (ELCLet (PatternVar v) x y) = LCApp (LCAbs v (translateInternal i y)) (translateInternal i x)
translateInternal i (ELCAbs (PatternVar v) b) = LCAbs v $ translateInternal i b
translateInternal i (ELCLet pat x y) = error "non-simple let encountered after simplifyAllLets!"
translateInternal i (ELCLetRec bindings t) = error "letrec encountered after simplifyAllLets!"
translateInternal i (ELCFatBar x y) = undefined --todo
translateInternal i t@(ELCCase var cases) = translateCase i t --todo
translateInternal i (ELCIf) = LCIf
translateInternal i (ELCY) = LCY

--translates case expressions
--CLAUSE Constructor [Variable] ELC
translateCase :: ConstructorInfo -> ELC -> LC
translateCase i (ELCCase var cases) = if productCase i cases 
                                         then let [CLAUSE c vs body] = cases 
                                                   --todo: scary recursion here with translate use. If this loops forever, change
                                                  in translate i $ ELCApp (ELCApp (ELCConstant $ C.UNPACK_PRODUCT (arity i c)) (foldr ELCAbs body (map PatternVar vs))) (ELCVar var)
                                         else undefined --todo: finish

sortCases i (ELCCase var cases) = ELCCase var (sortBy (comparing (clauseSumId i)) cases)

--helper function for sorting clauses in a case expression into order
clauseSumId :: ConstructorInfo -> Clause -> Int
clauseSumId i (CLAUSE c vs t) = tag i c 

productCase :: ConstructorInfo -> [Clause] -> Bool
productCase i [CLAUSE c _ _] = not $ isSum i c

varsInPattern :: Pattern -> [Variable]
varsInPattern (PatternConstant _) = []
varsInPattern (PatternVar v) = [v]
varsInPattern (PatternConstructor c ps) = concatMap varsInPattern ps

--data Clause = CLAUSE Constructor [Variable] ELC
freeVarsInClause :: Clause -> [Variable]
freeVarsInClause (CLAUSE c vs t) = freeVarsELC t \\ vs

boundVarsInClause :: Clause -> [Variable]
boundVarsInClause (CLAUSE c vs t) = nub $ [v | v <- vs, elem v (freeVarsELC t)] ++ boundVarsELC t

--ELCELCELCfreeVars returns the free variables in a given ELC term
freeVarsELC :: ELC -> [Variable]
freeVarsELC (ELCConstant c) = []
freeVarsELC (ELCVar x) = [x]
freeVarsELC (ELCApp x y) = nub $ freeVarsELC x ++ freeVarsELC y
freeVarsELC (ELCAbs pat body) = freeVarsELC body \\ varsInPattern pat
freeVarsELC (ELCLet pat binding term) = nub (freeVarsELC binding ++ freeVarsELC term) \\ varsInPattern pat
--todo: if a variable is bound in one of a letrec's patterns, is it bound to that value in all of the terms being bound by that letrec?
freeVarsELC (ELCLetRec bindings term) = nub (freeVarsInBindings ++ freeVarsELC term) \\ patternBoundVars
                                         where pats = map fst bindings
                                               bs = map snd bindings
                                               patternBoundVars = concatMap varsInPattern pats
                                               freeVarsInBindings = concat $ zipWith (\p b -> freeVarsELC b \\ varsInPattern p) pats bs 
freeVarsELC (ELCFatBar x y) = nub $ freeVarsELC x ++ freeVarsELC y
freeVarsELC (ELCCase v cs) = nub (concatMap freeVarsInClause cs) \\ [v]
freeVarsELC ELCIf = []


--boundVarsELC returns the bound vars in a given ELC term
boundVarsELC :: ELC -> [Variable]
boundVarsELC (ELCConstant c) = []
boundVarsELC (ELCVar x) = []
boundVarsELC (ELCApp x y) = nub $ boundVarsELC x ++ boundVarsELC y
boundVarsELC (ELCAbs pat body) = nub $ [v | v <- (varsInPattern pat), elem v (freeVarsELC body)] ++ boundVarsELC body
boundVarsELC (ELCLet pat b t) = boundVarsELC (ELCAbs pat t) ++ boundVarsELC b
boundVarsELC (ELCLetRec bindings t) = nub $ [v | v <- patternVars, elem v (freeVarsELC t)] ++ concatMap boundVarsELC bs
                             where ps = map fst bindings
                                   bs = map snd bindings
                                   patternVars = concatMap varsInPattern ps  
boundVarsELC (ELCFatBar x y) = nub $ boundVarsELC x ++ boundVarsELC y
boundVarsELC (ELCCase v cs) = concatMap boundVarsInClause cs  
boundVarsELC ELCIf = []

--simplifyAllLets produces an ELC that contains only simple lets
simplifyAllLets :: ConstructorInfo -> ELC -> ELC
simplifyAllLets i = until (\x -> simplifyAllLetsInternal i x == x) (simplifyAllLetsInternal i)

--simplifyAllLetsInternal does the actual work of simplifyAllLets
simplifyAllLetsInternal :: ConstructorInfo -> ELC -> ELC
simplifyAllLetsInternal i (ELCApp t1 t2) = ELCApp (simplifyAllLetsInternal i t1) (simplifyAllLetsInternal i t2)
simplifyAllLetsInternal i (ELCAbs pat body) = ELCAbs pat (simplifyAllLetsInternal i body) --pattern-matching lambda abstraction
simplifyAllLetsInternal i (ELCLet pat bind body) = if irrefutable i pat 
                                                      then irrefutableLetToSimpleLet (ELCLet pat (simplifyAllLetsInternal i bind) (simplifyAllLetsInternal i body))
                                                      else conformalityTransform i (ELCLet pat (simplifyAllLetsInternal i bind) (simplifyAllLetsInternal i body))
simplifyAllLetsInternal i t@(ELCLetRec bs body) = (irrefutableLetRecToIrrefutableLet . (conformalityTransform i) . dependencyAnalysis) (ELCLetRec (map (\(p,b) -> (p, simplifyAllLetsInternal i b)) bs) (simplifyAllLetsInternal i body))
                                                     
simplifyAllLetsInternal i (ELCFatBar t1 t2) = ELCFatBar (simplifyAllLetsInternal i t1) (simplifyAllLetsInternal i t2)
simplifyAllLetsInternal i (ELCCase var cs) = ELCCase var (map (simplifyAllLetsClause i) cs) --case statement for executing code based on what constructor the input was constructed with.
simplifyAllLetsInternal i x = x

irrefutableLetRec :: ConstructorInfo -> ELC -> Bool
irrefutableLetRec i (ELCLetRec bs body) = if all (irrefutable i) (map fst bs)
                                             then True
                                             else False

simplifyAllLetsClause :: ConstructorInfo -> Clause -> Clause                                             
simplifyAllLetsClause i (CLAUSE c vars term) = CLAUSE c vars $ simplifyAllLets i term
------------------------------------------------------------
------------------LET TRANSFORMATIONS SECTION---------------
--The following transformations simplify let expressions as much as possible
--For simplicity, they assume that the input is a let or letrec. Making sure to
--recursively transform all let(rec) expressions in the actual program is the responsibility
--of the overall translation function calling the following functions properly.


--dependency analysis takes an expression with letrecs and transforms it
--so as to keep only the essential letrecs, converting the other letrecs to lets, and puts the
--let(rec)s in the optimal order to express only actual mutual recursion.
dependencyAnalysis :: ELC -> ELC
dependencyAnalysis (ELCLetRec bindings term) = generateSortedLets (topoSortedSCCs $ constructDigraph bindings) term
dependencyAnalysis _ = error "called dependencyAnalysis on non-letrec term"

constructDigraph :: [(Pattern, ELC)] -> Graph ( (Pattern, ELC), Int)
constructDigraph bindings = graphFromVerticesAndAdjacency vertices edges
                            where ps = map fst bindings
                                  bs = map snd bindings
                                  vertices = [(binding, hash binding) | binding <- bindings]
                                  edges = [(hash binding, out) | binding <- bindings, out <- (outEdges binding)] 
                                   where varsToHashes = concatMap varsToHash bindings --keyed collection of variable names to the binding they are bound in
                                         varsToHash binding@(pat, elc) = [(var, hash binding)| var <- varsInPattern pat]  
                                         outEdges binding@(pat, elc) = map fromJust $ map ((flip lookup) varsToHashes) $ (freeVarsELC elc :: [Variable])

--topologically sorted strongly connected components of the graph, as a list of lists.
--later elements depend on earlier ones. Thus, the first ones should be in the outermost let.
topoSortedSCCs :: Graph ((Pattern, ELC), Int) -> [[(Pattern,ELC)]]
topoSortedSCCs g = map (map fst) $ map flattenSCC $ stronglyConnCompG g

--generateSortedLets takes the output of topoSortedSCCs, and an innermost expression, and
--generates nested let(rec) statements that are in order of their inter-dependencies
generateSortedLets :: [[(Pattern, ELC)]] -> ELC -> ELC
generateSortedLets [] base = base
generateSortedLets (b:bs) base = if length b == 1 
                                    then let [(pat, elc)] = b in
                                             ELCLet pat elc (generateSortedLets bs base)
                                    else ELCLetRec b (generateSortedLets bs base) 

--conformalityTransform adds conformality checks to non-exhaustive let(rec)s
--basically just adds some fatbars to sum and constant patterns.
conformalityTransform :: ConstructorInfo -> ELC -> ELC
conformalityTransform i t@(ELCLet p t1 t2) = if irrefutable i p
                                                then t
                                                else ELCLet (PatternConstructor ("CONFORM_SUM" ++ show arity) (map PatternVar vs)) 
                                                            (convertBinding p t1)
                                                            t2 
                                                     where vs =  varsInPattern p
                                                           arity = length vs
                                                           
conformalityTransform i t@(ELCLetRec bs body) = ELCLetRec (map (\(p,b) -> if irrefutable i p
                                                                             then (p,b)
                                                                             else let vs = varsInPattern p in let arity = length vs in (PatternConstructor ("CONFORM_SUM" ++ show arity) (map PatternVar vs), convertBinding p b)
                                                           
                                                               )
                                                            bs
                                                           )
                                                           body
conformalityTransform _ _ = error "called conformalityTransform on non-let(rec) term"

convertBinding p b = ELCLet (PatternVar q) b $ ELCFatBar (ELCApp (ELCAbs p (foldl ELCApp constructor (map ELCVar vs) ) ) b) (ELCConstant C.FAIL)
         where vs = varsInPattern p 
               arity = length vs
               constructor = ELCConstant (C.PACK_PRODUCT arity)
               q = head $ variables \\ vs
               
--irrefutableLetRecToIrrefutableLet does as the clunky name implies. todo: find a better name.
irrefutableLetRecToIrrefutableLet :: ELC -> ELC 
irrefutableLetRecToIrrefutableLet = y_ify . productify
  where productify (ELCLetRec bs t) = ELCLetRec [(PatternConstructor "irrefutableLetRecProduct" $ map PatternVar vs, foldl ELCApp constructor (map ELCVar vs))] t
          where vs = map toVar $ map fst bs
                      where toVar (PatternVar x) = x
                            toVar _ = error "refutable letrec passed to irrefutableLetRecToIrrefutableLet"
                constructor = ELCConstant (C.PACK_PRODUCT (length vs))
        y_ify (ELCLetRec [(pat, binding)] body) = ELCLet pat (ELCApp ELCY (ELCAbs pat binding)) body

--irrefutableLetToSimpleLet does what it says.
irrefutableLetToSimpleLet :: ELC -> ELC
irrefutableLetToSimpleLet t@(ELCLet (PatternVar x) binding body) = t --already simple
irrefutableLetToSimpleLet (ELCLet (PatternConstructor c ps) binding body) = ELCLet (PatternVar q) binding $ recurseLets ps (ELCVar q)
    where q = head $ variables \\ (freeVarsELC body)
          recurseLets [] q = body
          recurseLets (pat:pats) q = ELCLet pat (ELCApp (ELCConstant (C.SEL (length ps - length pats))) q) (recurseLets pats q) 

          
----------------DEPENDENCY ANALYSIS TEST----------------
depTest :: ELC
depTest = ELCLetRec [ (PatternVar "a", ELCConstant C.PLUS),
                      (PatternVar "b", ELCVar "a" ),
                      (PatternVar "c", ELCApp (ELCApp (ELCVar "h") (ELCVar "b")) (ELCVar "d") ),
                      (PatternVar "d", ELCVar "c"),
                      (PatternVar "f", ELCApp (ELCApp (ELCVar "g") (ELCVar "h")) (ELCVar "a") ),
                      (PatternVar "g", ELCVar "f"),
                      (PatternVar "h", ELCVar "g")
                    ] 
                    (ELCApp (ELCVar "c") (ELCVar "h"))

-----------------MATCH TEST---------------------------
{-This is a representation of the following function:
mappairs f [] ys = []
mappairs f (x:xs) [] = []
mappairs f (x:xs) (y:ys) = f x y : mappairs f xs ys
-}

testInfo :: ConstructorInfo
testInfo = [("List", [("Cons",(0, 2)), ("Nil",(1,0))])]

testUs :: [Variable]
testUs = ["_u1", "_u2", "_u3"]

testQs :: [Equation]
testQs = [ ([PatternVar "f", PatternConstructor "Nil" [], PatternVar "ys"], ELCConstant NIL),
           ([PatternVar "f", PatternConstructor "Cons" [PatternVar "x", PatternVar "xs"], PatternConstructor "Nil" [] ], ELCConstant NIL),
           ([PatternVar "f", PatternConstructor "Cons" [PatternVar "x", PatternVar "xs"], PatternConstructor "Cons" [PatternVar "y", PatternVar "ys"]], ELCApp (ELCApp (ELCConstant CONS) (ELCApp (ELCApp (ELCVar "f") (ELCVar "x")) (ELCVar "y")) ) $ ELCApp (ELCApp (ELCApp (ELCVar "THISFUNCTION") (ELCVar "f")) (ELCVar "xs")) (ELCVar "ys") )
         ]
testMatch :: ELC
testMatch = match 3 testUs testQs (ELCVar "ERROR!!!") testInfo 
