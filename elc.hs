{-Author: Connor Clark
Description: Implements a basic "enriched lambda calculus"
for use as an intermediate language between a high-level 
functional language and the compiled/interpreted code.
-}

data ELC = Constant Char 
           | Var Char
           | App ELC ELC
           | Abs Pattern ELC
           | Let Pattern ELC ELC --read as "Let pattern = elc in elc."
           | LetRec [(Pattern, ELC)] ELC --read as "let these patterns equal the corresponding ELCs in ELC.
           | FatBar ELC ELC
           | Case Char [(Pattern, ELC)]
            deriving (Show, Read, Ord, Eq)
           
data Pattern = PatternConstant Char
               | PatternVar Char
               | PatternConstructor Constructor [Pattern]
                deriving (Show, Read, Ord, Eq)
               
type Constructor = [Char]
