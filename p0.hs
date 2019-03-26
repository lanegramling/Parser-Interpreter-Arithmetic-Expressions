{-# LANGUAGE GADTs, FlexibleContexts #-}


-- NAME -- Lane Gramling
-- KUID -- 2766765
-- Comments:
--    I loaded it with ghci and ran manual testing through there. I wasn't able to break it,
-- so hopefully it holds up to more rigorous testing. I'd like to have provided some quickcheck
-- tests, but ended up spending more time getting the hang of it than I could afford before
-- the deadline.
--
-- Instructions for use:
--    1) Load in p0.hs
--    2) Evaluate an AE from a string using
--          interpAE "<string parseable as AE>"
--
-- Error handling details:
--    - interpAE (and thus evalM) will return Nothing on error cases, which will
--      occur on div/0 errors and when negatives are included in the AE since we
--      are dealing with naturals only.
--    - evalAE throws descriptive error messages using the error function for
--      these cases, since the Maybe monad is not utilized to allow for Nothing.


-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

--
-- Simple caculator over naturals with no identifiers
--
-- Author: Perry Alexander
-- Date: Tue Jan 23 17:54:44 CST 2018
--
-- Source files for the Arithmetic Expressions (AE) language from PLIH
--

-- AST Definition

data AE where
  Num :: Int -> AE
  Plus :: AE -> AE -> AE
  Minus :: AE -> AE -> AE
  Mult :: AE -> AE -> AE
  Div :: AE -> AE -> AE
  If0 :: AE -> AE -> AE -> AE
  deriving (Show,Eq)

-- AE Parser (Requires ParserUtils and Parsec included above)

languageDef =
  javaStyle { identStart = letter
            , identLetter = alphaNum
            , reservedNames = [ "if0"
                              , "then"
                              , "else"
                              ]
            , reservedOpNames = [ "+","-","*","/"]
            }

lexer = makeTokenParser languageDef

inFix o c a = (Infix (reservedOp lexer o >> return c) a)
preFix o c = (Prefix (reservedOp lexer o >> return c))
postFix o c = (Postfix (reservedOp lexer o >> return c))

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

expr :: Parser AE
expr = buildExpressionParser operators term

operators = [
  [ inFix "*" Mult AssocLeft
    , inFix "/" Div AssocLeft ]
  , [ inFix "+" Plus AssocLeft
  , inFix "-" Minus AssocLeft ]
  ]

numExpr :: Parser AE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

ifExpr :: Parser AE
ifExpr  = do reserved lexer "if0"
             c <- expr
             reserved lexer "then"
             t <- expr
             reserved lexer "else"
             e <- expr
             return (If0 c t e)


term = parens lexer expr
       <|> numExpr
       <|> ifExpr

-- Parser invocation
-- Call parseAE to parse a string into the AE data structure.

parseAE = parseString expr

-- Evaluation Functions
-- Replace the bodies of these functions with your implementations for
-- Exercises 1-4.  Feel free to add utility functions or testing functions as
-- you see fit, but do not change the function signatures.  Note that only
-- Exercise 4 requires you to integrate the parser above.

-- liftNum -- Allow operators to be used on AEs as they are on Ints
liftNum :: (Int -> Int -> Int) -> AE -> AE -> AE
liftNum op (Num l) (Num r) = (Num (op l r)) -- op identifies the operator


 -- evalAE -- Takes a parsed AE, recursively evaluates it, and returns an integer
 --           Each evaluator will handle div/0 and negative cases as errors.
evalAE :: AE -> Int
evalAE (Num n) = if n >= 0 then n else error "Naturals only - Negatives are not allowed!" -- Num will be the base case in each evaluator
evalAE (Plus l r) = (evalAE l) + (evalAE r)
evalAE (Minus l r) = evalAE (Num ((evalAE l) - (evalAE r))) -- sneakily feed result thru base case to catch negative results
evalAE (Div  l r) = if r==Num 0 then error "Divide by 0 error" else div (evalAE l) (evalAE r) -- Div in each evaluator will always truncate to ints because Naturals only
evalAE (Mult l r) = (evalAE l) * (evalAE r)
evalAE (If0 n t e) = if (evalAE n)==0 then evalAE t else evalAE e
-- evalAE _ = 0


-- evalAEMaybe -- Takes a parsed AE, evaluates it into a (Maybe) Int, and returns Just the final value,
--                   or Nothing in error cases
evalAEMaybe :: AE -> Maybe Int
evalAEMaybe (Num n) = if n >= 0 then Just n else Nothing
evalAEMaybe (Plus l r) = evalAEMaybe (liftNum (+) (Num (evalAE l)) (Num (evalAE r)))
evalAEMaybe (Minus l r) = evalAEMaybe (liftNum (-) (Num (evalAE l)) (Num (evalAE r)))
evalAEMaybe (Mult l r) = evalAEMaybe (liftNum (*) (Num (evalAE l)) (Num (evalAE r)))
evalAEMaybe (Div l r) = if r==Num 0 then Nothing else evalAEMaybe (liftNum (div) (Num (evalAE l)) (Num (evalAE r)))
evalAEMaybe (If0 n t e) = if (evalAE n)==0 then evalAEMaybe t else evalAEMaybe e
-- evalAEMaybe _ = Nothing


-- evalM -- Takes a parsed AE and evaluates it into a (Maybe) Int using do notation, returning Just the final value,
--             or Nothing in error cases
evalM :: AE -> Maybe Int
evalM (Num n) = if n >= 0 then Just n else Nothing
evalM (Plus l r) = do a1 <- (evalM l)
                      a2 <- (evalM r)
                      evalM (liftNum (+) (Num a1) (Num a2))
evalM (Minus l r) = do a1 <- (evalM l)
                       a2 <- (evalM r)
                       evalM (liftNum (-) (Num a1) (Num a2))
evalM (Mult l r) = do a1 <- (evalM l)
                      a2 <- (evalM r)
                      evalM (liftNum (*) (Num a1) (Num a2))
evalM (Div l r) = do a1 <- (evalM l)
                     a2 <- (evalM r)
                     if a2==0 then Nothing else (evalM (liftNum (div) (Num a1) (Num a2)))
evalM (If0 n t e) = do n1 <- (evalM n)
                       if n1==0 then evalM t else evalM e
-- evalM _ = Nothing


-- interpAE -- Takes a string, parses it into an AE, and evaluates it to a result, with Nothing indicating an error.
interpAE :: String -> Maybe Int
interpAE str = evalM (parseAE str)
-- interpAE _ = Nothing
