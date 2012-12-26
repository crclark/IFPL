module Parser where

import LangAST
import ELC (Constructor, TypeName, Pattern(..))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Control.Applicative ((<$>), (<*>))
import Control.Monad.Identity
import Data.Either (partitionEithers)
import Text.Parsec.Language (haskellDef)
import qualified Text.Parsec.Token as P
import Constants as C

lexer = P.makeTokenParser haskellDef

identifier =P.identifier lexer

reserved = P.reserved lexer

operator = P.operator lexer

reservedOp = P.reservedOp lexer

charLiteral = P.charLiteral lexer

stringLiteral = P.stringLiteral lexer

natural = P.natural lexer

integer = P.integer lexer 

float = P.float lexer

naturalOrFloat = P.naturalOrFloat lexer

decimal = P.decimal lexer

hexadecimal = P.hexadecimal lexer

octal = P.octal lexer

symbol = P.symbol lexer

lexeme = P.lexeme lexer

whiteSpace = P.whiteSpace lexer

parens = P.parens lexer

braces = P.braces lexer

angles = P.angles lexer

brackets = P.brackets lexer

semi = P.semi lexer

comma = P.comma lexer

colon = P.colon lexer

dot = P.dot lexer

semiSep = P.semiSep lexer

semiSep1 = P.semiSep1 lexer

commaSep = P.commaSep lexer

commaSep1 = P.commaSep1 lexer

--a program is a line-break separated list of declarations. Going to require that each decl is separated by one or more blank lines

program :: Parser ([Def],[ADTDef])
program = partitionEithers <$> sepBy decl (string "\n\n") --todo: using symbol instead of string consumes trailing whitespace; is that what I want here? 

--a declaration is either a ADT type def or a function def (constants are nullary functions)
decl :: Parser (Either Def ADTDef)
decl = do adt <- optionMaybe adtDecl
          case adt of
           Just x -> return $ Right x
           Nothing -> do func <- optionMaybe funcDecl
                         case func of
                          Just x -> return $ Left x
                          Nothing -> fail "expected a top-level declaration"

--an ADT type def is "data" ++a type name ++ "=" ++ a pipe-separated list of data constructors + their arg types
adtDecl :: Parser ADTDef
adtDecl = do symbol "data"
             ident <- identifier
             symbol "="
             clauses <- sepBy dataConstructorClause (symbol "|") 
             return $ ADTDef ident clauses
             
dataConstructorClause :: Parser (Constructor, [TypeName])
dataConstructorClause = do ident <- identifier
                           typeNames <- many identifier
                           return (ident, typeNames)

--a function is a line-break separated list of function cases
funcDecl :: Parser Def
funcDecl = helper <$> sepBy funcCase (symbol "\n")

helper :: [(Identifier, ([Pattern],Expr))] -> Def
helper xss@(x:xs) = if all (== (fst x)) (map fst xs)
                       then Def (fst x) (map snd xss) --all okay, translate
                       else error "defs from two functions consumed as one function."

--a function case is a function name, some patterns, "=", and then an expression
funcCase :: Parser (Identifier, ([Pattern],Expr))
funcCase = do ident <- identifier
              pats <- many pattern
              symbol "="
              expr <- rhsExpr
              return (ident, (pats, expr))

pattern :: Parser Pattern
pattern = patternConstantNum <|> patternConstantChar <|> patternVar <|> patternConstructor <?> "pattern"

patternConstantNum :: Parser Pattern
patternConstantNum = do num <- naturalOrFloat
                        case num of
                         Left int -> return $ PatternConstant $ C.INT $ fromIntegral int
                         Right float -> return $ PatternConstant $ C.DOUBLE float

patternConstantChar :: Parser Pattern
patternConstantChar = PatternConstant . C.CHAR <$> charLiteral

patternVar :: Parser Pattern
patternVar = PatternVar <$> identifier <?> "variable pattern"

patternConstructor :: Parser Pattern
patternConstructor = (parens $ PatternConstructor <$> identifier <*> (many pattern)) <?> "constructor pattern"

rhsExpr :: Parser Expr
rhsExpr = (lexeme $ buildExpressionParser table innerExpr) <?> "right-hand side expression"

table :: [[Operator String () Identity Expr]]
table = [
      [ op "*" (opify (ExprConstant C.MULT)) AssocLeft, op "/" (opify (ExprConstant C.DIV)) AssocLeft ],
      [ op "+" (opify (ExprConstant C.PLUS)) AssocLeft, op "-" (opify (ExprConstant C.MINUS)) AssocLeft ],
      [ op "==" (opify (ExprConstant C.EQUALS)) AssocLeft, op "<" (opify (ExprConstant C.LT)) AssocLeft, op ">" (opify (ExprConstant C.GT)) AssocLeft]
      ]
    where
      op s f assoc = Infix (do { string s ; return f }) assoc
      opify t = \l r -> ExprApp (ExprApp t l) r 
      
innerExpr :: Parser Expr
innerExpr = skipMany (symbol " ") >> (lexeme $ foldl1 ExprApp <$> many1 unit) <?> "subexpression that goes on either side of an infix operator"

unit :: Parser Expr
unit = (lexeme $ parens (prefixOp <|> rhsExpr) <|> literal <|> ident) <?> "expression"

literal :: Parser Expr --todo: add list and string sugar and list comprehensions
literal = numLit <|> charLit <?> "literal"

numLit :: Parser Expr
numLit = do 
                num <- naturalOrFloat
                return $ case num of
                          Left int -> ExprConstant $ C.INT (fromIntegral int)
                          Right float -> ExprConstant $ C.DOUBLE float

charLit :: Parser Expr
charLit = ExprConstant . C.CHAR <$> charLiteral


prefixOp :: Parser Expr --todo: add cons, and figure out why >> isn't working instead of do blocks
prefixOp = plusOp <|> divOp <|> subOp <|> multOp <|> expOp <|> eqOp <|> gtOp <|> ltOp  <?> "built-in math operator"
 where plusOp = do symbol "+"
                   return $ ExprConstant C.PLUS
       divOp = do symbol "/" 
                  return $ ExprConstant C.DIV
       subOp = do symbol "-" 
                  return $ ExprConstant C.MINUS
       multOp = do symbol "*"
                   return $ ExprConstant C.MULT
       expOp = do symbol "^" 
                  return $ ExprConstant C.EXP
       eqOp = do string "=="
                 return $ ExprConstant C.EQUALS
       gtOp = do symbol ">"
                 return $ ExprConstant C.GT
       ltOp = do symbol "<"
                 return $ ExprConstant C.LT
ident :: Parser Expr
ident = ExprVar <$> identifier

{-
stringLit :: Parser Expr --todo: use built-in Cons?
stringLit = stringLiteral >>= (\s -> foldr (C.ConstantApp Cons)
-}
