module SKI ( 
            SKI(SKIConstant, S, K, I, SKIApp), 
            smallStep, 
            isNormalForm,
            eval, 
            parseSKI, 
            pretty) where

import Text.Parsec
import Text.Parsec.String
import Control.Applicative ((<$>))
import Constants as C

data SKI = SKIConstant C.Constant
           |S
           | K
           | I
           | SKIApp SKI SKI
            deriving (Show, Read, Eq, Ord)

--smallStep does one step of LMOM evaluation of an SKI term. To evaluate completely, use eval.
smallStep :: SKI -> SKI
smallStep (SKIConstant c) = SKIConstant $ C.constantEval c
smallStep (SKIApp I x) = x
smallStep (SKIApp (SKIApp K x) y) = x
smallStep (SKIApp (SKIApp (SKIApp S x) y) z) = SKIApp (SKIApp x z) (SKIApp y z)
smallStep (SKIApp (SKIConstant x) (SKIConstant y)) = SKIConstant $ C.ConstantApp x y
smallStep (SKIApp (SKIConstant x) y) = SKIApp (SKIConstant x) (smallStep y) --todo: test terms with constants
smallStep (SKIApp x y) = if smallStep x == x then SKIApp x (smallStep y) else SKIApp (smallStep x) y
smallStep x = x

isNormalForm :: SKI -> Bool
isNormalForm (SKIApp I _) = False
isNormalForm (SKIApp (SKIApp K _) _) = False
isNormalForm (SKIApp (SKIApp (SKIApp S _) _) _) = False
isNormalForm (SKIApp x y) = isNormalForm x && isNormalForm y
isNormalForm S = True
isNormalForm K = True
isNormalForm I = True
isNormalForm (SKIConstant c) = C.constantNormalForm c

eval :: SKI -> SKI
eval = until isNormalForm smallStep

---------------------------------
--Parser:
----Warning: this parser is for human-readable testing only! 
parseSKI :: String -> Either ParseError SKI
parseSKI = (runParser tree () "") . (filter (/= ' '))

unit :: Parser SKI
unit = paren <|> combinator <?> "grouped combinators or single combinator"

paren :: Parser SKI
paren = between (char '(') (char ')') tree

tree :: Parser SKI
tree = foldl1 SKIApp <$> many1 unit

combinator :: Parser SKI
combinator = do x <- oneOf ['S','K','I']
                case x of
                  'S' -> return S
                  'K' -> return K
                  'I' -> return I
             <?> "single combinator"

--Pretty printer: 
--Warning: for human-readable testing only!
pretty :: SKI -> String
pretty S = "S"
pretty K = "K"
pretty I = "I"
pretty (SKIApp x y) = "(" ++ pretty x ++ pretty y ++ ")"
