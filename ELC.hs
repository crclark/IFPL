{-Author: Connor Clark
Description: Implements a basic "enriched lambda calculus"
for use as an intermediate language between a high-level 
functional language and the compiled/interpreted code.
todo: add letrecs to plain LC. IFPL p. 43 says it's more efficient.
todo: eliminate constructor names earlier in the process so I don't have to deal with them in ELC terms.
-}
module ELC where
import Prelude hiding (sum)
import Variables
import Constants as C
import LC 
import Data.List hiding (partition, sum)
import Data.Ord (comparing)
import Control.Monad
import Digraph --need to "sudo ghc-pkg expose ghc" for this to compile, now.
import Data.Hashable
import Data.Maybe (fromJust)
import Debug.Trace

--abstract syntax for Enriched Lambda Calculus
data ELC = ELCConstant C.Constant 
           | ELCVar Variable
           | ELCApp ELC ELC
           | ELCAbs Pattern ELC --pattern-matching lambda abstraction
           | ELCLet Pattern ELC ELC --read as "Let pattern = elc in elc."
           | ELCLetRec [(Pattern, ELC)] ELC --read as "let these patterns equal the corresponding ELCs in ELC.
           | ELCFatBar ELC ELC --used in pattern matching
           | ELCCase Variable [Clause] --case statement for executing code based on what constructor the input was constructed with.
           | ELCIf --built-in if statement. Constants.COND is deprecated.
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
type Constructor = String

type TypeName = String

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
             Nothing -> error $ "Tried to get tag of non-existent constructor:" ++ c

--true iff constructor is of a sum type
isSum :: ConstructorInfo -> Constructor -> Bool
isSum info c = not $ tag info c == -1

--looks up the arity of a constructor
arity :: ConstructorInfo -> Constructor -> Arity
arity info constructor = case lookup constructor (join (map snd info)) of
                         Just (t, a) -> a
                         Nothing -> error $ "Unknown constructor referenced in pattern match: " ++ constructor

--todo: verify that two types can't share a constructor name in legal Haskell/Miranda/whatever
--otherConstructors returns a list of all constructors of a type, given the name of one of its constructors
otherConstructors :: ConstructorInfo -> Constructor -> [Constructor]
otherConstructors info constructor = let constructorLists = (map (map fst . snd) info)
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
irrefutable i (PatternConstructor c ps) = not (isSum i c) && all (irrefutable i) ps 

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

matchVar k (u:us) qs def info = match k us [(ps, subst e u v) | (PatternVar v : ps, e) <-qs] def info
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
subst (ELCVar var) var1 var2 = ELCVar $ if var == var2 then var1 else var
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

--recurseOn handles named self-recursion by abstracting out the function's use of its own name and 
--applying the fixpoint combinator to the result.
recurseOn :: Variable -> ELC -> ELC
recurseOn var body = ELCApp ELCY $ ELCAbs (PatternVar var) body

--translation function from ELC to LC. 
translate :: ConstructorInfo -> ELC -> LC
translate i = translateInternal i . simplifyAllLets i . subConstructorNames i

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
translateInternal i t@(ELCFatBar x y) = LCFATBAR $ translateFatBarInternal i t--LCApp (LCApp (LCConstant C.FATBAR) (translateInternal i x)) $ translateInternal i y
translateInternal i t@(ELCCase var cases) = translateCase i t 
translateInternal i (ELCIf) = LCIf
translateInternal i (ELCY) = LCY

--translates ELC fatbars into list of LC statements corresponding to each fatbar case, excluding FAIL.
translateFatBarInternal :: ConstructorInfo -> ELC -> [LC]
translateFatBarInternal i (ELCFatBar x (ELCConstant C.FAIL)) = [translateInternal i x]
translateFatBarInternal i (ELCFatBar x y) = (translateInternal i x) : translateFatBarInternal i y

--translates case expressions
--CLAUSE Constructor [Variable] ELC
--todo: test with example on p. 123
translateCase :: ConstructorInfo -> ELC -> LC
translateCase i t@(ELCCase var cases) = if productCase i cases 
                                           then let [CLAUSE c vs body] = cases 
                                                     --todo: scary recursion here with translate use. If this loops forever, change
                                                      in translate i $ ELCApp (ELCApp (ELCConstant $ C.UNPACK_PRODUCT (arity i c)) (foldr (ELCAbs . PatternVar) body vs)) (ELCVar var)
                                           else translate i $ toCaseT i $ sortCases i t 

toCaseT :: ConstructorInfo -> ELC -> ELC
toCaseT i (ELCCase var cases) = foldl1 ELCApp $ [ELCConstant (C.CASE_T $ length cases), ELCVar var] ++ 
                                                [ELCApp (ELCApp (ELCConstant $ C.UNPACK_SUM (tag i c) (arity i c)) (foldr (ELCAbs . PatternVar) body vs)) (ELCVar var) 
                                                 | (CLAUSE c vs body) <- cases]

sortCases :: ConstructorInfo -> ELC -> ELC
sortCases i (ELCCase var cases) = ELCCase var (sortBy (comparing (clauseSumId i)) cases)

--helper function for sorting clauses in a case expression into order
clauseSumId :: ConstructorInfo -> Clause -> Int
clauseSumId i (CLAUSE c vs t) = tag i c 

productCase :: ConstructorInfo -> [Clause] -> Bool
productCase i (CLAUSE c _ _ : _) = not $ isSum i c

varsInPattern :: Pattern -> [Variable]
varsInPattern (PatternConstant _) = []
varsInPattern (PatternVar v) = [v]
varsInPattern (PatternConstructor c ps) = concatMap varsInPattern ps

--data Clause = CLAUSE Constructor [Variable] ELC
freeVarsInClause :: Clause -> [Variable]
freeVarsInClause (CLAUSE c vs t) = freeVarsELC t \\ vs

boundVarsInClause :: Clause -> [Variable]
boundVarsInClause (CLAUSE c vs t) = nub $ [v | v <- vs, v `elem` (freeVarsELC t)] ++ boundVarsELC t

--subConstructorNames takes a constructor info and a term and replaces all named instances of constructors in that term with their internal representations.
subConstructorNames :: ConstructorInfo -> ELC -> ELC
subConstructorNames i (ELCVar v) = if capitalized v 
                                      then if arity i v == 0
                                              then if isSum i v
                                                      then ELCApp (ELCConstant $ C.PACK_SUM (tag i v) 0) $ ELCConstant C.NULL_PACK_ARG
                                                      else ELCApp (ELCConstant $ C.PACK_PRODUCT (tag i v)) $ ELCConstant C.NULL_PACK_ARG
                                              else if isSum i v
                                                      then ELCConstant $ C.PACK_SUM (tag i v) (arity i v)
                                                      else ELCConstant $ C.PACK_PRODUCT (arity i v)
                                      else ELCVar v
                                       where capitalized (c:cs) = elem c ['A'..'Z']
subConstructorNames i (ELCApp t1 t2) = ELCApp (subConstructorNames i t1) (subConstructorNames i t2)
subConstructorNames i (ELCAbs p t) = ELCAbs p (subConstructorNames i t)
subConstructorNames i (ELCLet p b t) = ELCLet p b (subConstructorNames i t)
subConstructorNames i (ELCLetRec bs t) = ELCLetRec (zip (map fst bs) (map (subConstructorNames i . snd) bs)) (subConstructorNames i t)
subConstructorNames i (ELCFatBar t1 t2) = ELCFatBar (subConstructorNames i t1) (subConstructorNames i t2)
subConstructorNames i (ELCCase v cs) = ELCCase v (map (subConstructorNamesInClause i) cs)
                                        where subConstructorNamesInClause i (CLAUSE c vs t) = CLAUSE c vs $ subConstructorNames i t
subConstructorNames i t = t
  
        
--freeVarsELC returns the free variables in a given ELC term
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
freeVarsELC ELCY = []

--boundVarsELC returns the bound vars in a given ELC term
boundVarsELC :: ELC -> [Variable]
boundVarsELC (ELCConstant c) = []
boundVarsELC (ELCVar x) = []
boundVarsELC (ELCApp x y) = nub $ boundVarsELC x ++ boundVarsELC y
boundVarsELC (ELCAbs pat body) = nub $ [v | v <- varsInPattern pat, v `elem` (freeVarsELC body)] ++ boundVarsELC body
boundVarsELC (ELCLet pat b t) = boundVarsELC (ELCAbs pat t) ++ boundVarsELC b
boundVarsELC (ELCLetRec bindings t) = nub $ [v | v <- patternVars, v `elem` (freeVarsELC t)] ++ concatMap boundVarsELC bs
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
simplifyAllLetsInternal i t@(ELCLetRec bs body) = (irrefutableLetRecToIrrefutableLet . conformalityTransform i . dependencyAnalysis) (ELCLetRec (map (\(p,b) -> (p, simplifyAllLetsInternal i b)) bs) (simplifyAllLetsInternal i body))
                                                     
simplifyAllLetsInternal i (ELCFatBar t1 t2) = ELCFatBar (simplifyAllLetsInternal i t1) (simplifyAllLetsInternal i t2)
simplifyAllLetsInternal i (ELCCase var cs) = ELCCase var (map (simplifyAllLetsClause i) cs) --case statement for executing code based on what constructor the input was constructed with.
simplifyAllLetsInternal i x = x

irrefutableLetRec :: ConstructorInfo -> ELC -> Bool
irrefutableLetRec i (ELCLetRec bs body) = all (irrefutable i) (map fst bs)
                                             
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
                                  edges = [(hash binding, out) | binding <- bindings, out <- outEdges binding] 
                                   where varsToHashes = concatMap varsToHash bindings --keyed collection of variable names to the binding they are bound in
                                         varsToHash binding@(pat, elc) = [(var, hash binding)| var <- varsInPattern pat]  
                                         outEdges binding@(pat, elc) = map (safeFromJust . flip lookup varsToHashes) $ freeVarsELC elc
                                         safeFromJust x = case x of
                                                               Just y -> y
                                                               Nothing -> error "free variable in body of letrec not found in letrec bindings"
--topologically sorted strongly connected components of the graph, as a list of lists.
--later elements depend on earlier ones. Thus, the first ones should be in the outermost let.
topoSortedSCCs :: Graph ((Pattern, ELC), Int) -> [[(Pattern,ELC)]]
topoSortedSCCs g = map (map fst . flattenSCC) $ stronglyConnCompG g

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
irrefutableLetRecToIrrefutableLet t@(ELCLetRec p q) = (y_ify . productify) t
  where productify (ELCLetRec bs t) = ELCLetRec [(PatternConstructor "irrefutableLetRecProduct" $ map PatternVar vs, foldl ELCApp constructor (map ELCVar vs))] t
          where vs = map (toVar . fst) bs
                      where toVar (PatternVar x) = x
                            toVar _ = error "refutable letrec passed to irrefutableLetRecToIrrefutableLet"
                constructor = ELCConstant (C.PACK_PRODUCT (length vs))
        y_ify (ELCLetRec [(pat, binding)] body) = ELCLet pat (ELCApp ELCY (ELCAbs pat binding)) body
irrefutableLetRecToIrrefutableLet t@(ELCLet _ _ _) = t
irrefutableLetRecToIrrefutableLet x = error "non let(rec) passed to irrefutableLetRecToIrrefutableLet"

--irrefutableLetToSimpleLet does what it says.
irrefutableLetToSimpleLet :: ELC -> ELC
irrefutableLetToSimpleLet t@(ELCLet (PatternVar x) binding body) = t --already simple
irrefutableLetToSimpleLet (ELCLet (PatternConstructor c ps) binding body) = ELCLet (PatternVar q) binding $ recurseLets ps (ELCVar q)
    where q = head $ variables \\ freeVarsELC body
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


-----------------Case statement test------------------
--type ConstructorInfo = [(TypeName, [(Constructor, (Tag, Arity))])] 
caseTestInfo :: ConstructorInfo
caseTestInfo = [("Bool", [("True", (1,0)), ("False", (2,0))])]

--ELCCase Variable [Clause] 

--data Clause = CLAUSE Constructor [Variable] ELC
clause1 :: Clause
clause1 = CLAUSE "True" [] $ ELCVar "hello, true!"

clause2 :: Clause
clause2 = CLAUSE "False" [] $ ELCVar "hello, false!"

caseTest :: ELC
caseTest = ELCApp (ELCAbs (PatternVar "x") $ ELCCase "x" [clause1, clause2]) $ ELCApp (ELCConstant (C.PACK_SUM 2 0)) (ELCConstant (C.NULL_PACK_ARG))

-----------------letrec test--Should eval to 28--------------------------
--ELCLetRec [(Pattern, ELC)] ELC 
--translation of program on p. 118:
{-
letrec  x = fac z
        fac = \n -> IF (== n 0) 1 (* n (fac (- n 1)))
        z = 4
        sum = \x -> \y -> IF (== x 0) y (sum (- x 1) (+ y 1)
in sum x z

-}

letrecTestInfo :: ConstructorInfo
letrecTestInfo = undefined

letrecTest :: ELC
letrecTest = ELCLetRec [(PatternVar "x", ELCApp (ELCVar "fac") (ELCVar "z")),
                        (PatternVar "fac", fac),
                        (PatternVar "z", ELCConstant $ C.INT 4),
                        (PatternVar "sum", sum) 
                        ]
                        (ELCApp (ELCApp (ELCVar "sum") (ELCVar "x")) (ELCVar "z"))

fac :: ELC
fac = ELCApp ELCY $ ELCAbs (PatternVar "f") $ ELCAbs (PatternVar "n") $ ELCApp (ELCApp (ELCApp ELCIf facIf) facThen) facElse

facIf :: ELC
facIf = ELCApp (ELCApp (ELCConstant C.EQUALS) (ELCVar "n")) (ELCConstant $ C.INT 0)

facThen :: ELC
facThen = ELCConstant $ C.INT 1

facElse :: ELC
facElse = ELCApp (ELCApp (ELCConstant C.MULT) (ELCVar "n")) (ELCApp (ELCVar "f") nMinusOne)
           where nMinusOne = (ELCApp (ELCApp (ELCConstant C.MINUS) (ELCVar "n")) (ELCConstant $ C.INT 1))

sum :: ELC
sum = ELCApp ELCY $ ELCAbs (PatternVar "f") $ ELCAbs (PatternVar "x") $ ELCAbs (PatternVar "y") $ ELCApp (ELCApp (ELCApp ELCIf sumIf) sumThen) sumElse
           
sumIf :: ELC
sumIf = ELCApp (ELCApp (ELCConstant C.EQUALS) (ELCVar "x")) (ELCConstant $ C.INT 0)

sumThen :: ELC
sumThen = ELCVar "y"

sumElse :: ELC
sumElse = ELCApp (ELCApp (ELCVar "f") xMinusOne) yPlusOne
           where xMinusOne = ELCApp (ELCApp (ELCConstant C.MINUS) (ELCVar "x")) (ELCConstant $ C.INT 1)
                 yPlusOne = ELCApp (ELCApp (ELCConstant C.PLUS) (ELCVar "y")) (ELCConstant $ C.INT 1)


--------letrectest2----------Should eval to 49
letrecTest2Info :: ConstructorInfo
letrecTest2Info = undefined

{-
let x = y + 2
    y = 5
    in x * x
-}
letrecTest2 :: ELC
letrecTest2 = ELCLetRec [(PatternVar "x", ELCApp (ELCApp (ELCConstant C.PLUS) (ELCVar "y")) (ELCConstant $ C.INT 2)),
                         (PatternVar "y", ELCConstant $ C.INT 5)
                        ]
                        (ELCApp (ELCApp (ELCConstant C.MULT) (ELCVar "x")) (ELCVar "x"))

--todo: more nullary constructor testing. Packing, unpacking, use as patterns, etc.

--todo: write a plausible function with a pattern match failure
