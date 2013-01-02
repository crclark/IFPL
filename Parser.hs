{-
Like Haskell, kind of, but each declaration ends with a ! and each case of a function ends with a ;

todo: type variables in data declarations (i.e., types with kinds other than *)
todo: let expressions
todo: string literals in Constants.hs and associated operators for dealing with them.
      Would make it much easier to define programs with comprehensible output.
-}
module Parser where

import LangAST
import ELC (ELC, Constructor, ConstructorInfo, TypeName, Pattern(..))
import Text.Parsec
import Text.Parsec.String
import Text.Parsec.Expr
import Text.Parsec.Token (commentStart)
import Text.Parsec.Language (haskellDef)
import Control.Applicative ((<$>), (<*>))
import Control.Monad.Identity
import Data.Either (partitionEithers)
import Data.List (intercalate)
import qualified Text.Parsec.Token as P
import Constants as C

lexer = P.makeTokenParser haskellDef

identifier =P.identifier lexer

capIdentifier :: Parser String
capIdentifier = do init <- oneOf ['A'..'Z']
                   rest <- identifier
                   return $ init:rest
                   <?> "Capitalized identifier"
                   
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

fromEither :: Show a => Either a b -> b
fromEither (Left x) = error $ show x
fromEither (Right x) = x


fileToELC :: String -> (ELC, ConstructorInfo)
fileToELC s = (expr, info)
               where (funcs, adts) = case runParser program () [] s of
                                      Left e -> error $ show e
                                      Right tuple -> tuple
                     info = buildConstructorInfo adts
                     expr = defsToELC funcs

--a program is a bang separated list of declarations. 
program :: Parser ([Def],[ADTDef])
program = partitionEithers <$> endBy1 decl (symbol "!") 

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
             ident <- capIdentifier
             symbol "="
             clauses <- sepBy dataConstructorClause (symbol "|")
             return $ ADTDef ident clauses
             
dataConstructorClause :: Parser (Constructor, [TypeName])
dataConstructorClause = do ident <- capIdentifier
                           typeNames <- many capIdentifier
                           return (ident, typeNames)

--a function is a line-break separated list of function cases
funcDecl :: Parser Def
funcDecl = helper <$> endBy funcCase (semi)

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
      [ op "==" (opify (ExprConstant C.EQUALS)) AssocLeft, op "<" (opify (ExprConstant C.LESS_THAN)) AssocLeft, op ">" (opify (ExprConstant C.GREATER_THAN)) AssocLeft]
      ]
    where
      op s f assoc = Infix (do { string s ; return f }) assoc
      opify t = \l r -> ExprApp (ExprApp t l) r 
      
innerExpr :: Parser Expr
innerExpr = whiteSpace >> lexeme (foldl1 ExprApp <$> many1 unit) <?> "subexpression that goes on either side of an infix operator"

unit :: Parser Expr
unit = (lexeme $ conditional <|> parens (prefixOp <|> rhsExpr) <|> literal <|> ident) <?> "expression"

conditional :: Parser Expr
conditional = do reserved "if"
                 a <- rhsExpr
                 reserved "then"
                 b <- rhsExpr
                 reserved "else"
                 c <- rhsExpr
                 return $ ExprApp (ExprApp (ExprApp ExprIf a) b) c

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
prefixOp = plusOp <|> divOp <|> subOp <|> multOp <|> eqOp <|> gtOp <|> ltOp  <?> "built-in math operator"
 where plusOp = do symbol "+"
                   return $ ExprConstant C.PLUS
       divOp = do symbol "/" 
                  return $ ExprConstant C.DIV
       subOp = do symbol "-" 
                  return $ ExprConstant C.MINUS
       multOp = do symbol "*"
                   return $ ExprConstant C.MULT
       eqOp = do string "=="
                 return $ ExprConstant C.EQUALS
       gtOp = do symbol ">"
                 return $ ExprConstant C.GREATER_THAN
       ltOp = do symbol "<"
                 return $ ExprConstant C.LESS_THAN
ident :: Parser Expr
ident = ExprVar <$> identifier

{-
stringLit :: Parser Expr --todo: use built-in Cons?
stringLit = stringLiteral >>= (\s -> foldr (C.ConstantApp Cons)
-}
