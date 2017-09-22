module Phil.Parser where

import Control.Applicative
import Data.Functor
import Data.List.NonEmpty (some1)
import Text.Trifecta
import Text.Trifecta.Indentation
import Text.Parser.Token.Highlight

import qualified Data.HashSet as HS
import qualified Data.Set as S

import Phil.AST.Binding
import Phil.AST.Definitions
import Phil.AST.Expr
import Phil.Core.AST.Identifier
import Phil.Core.AST.Literal
import Phil.Core.AST.Pattern
import Phil.Core.AST.ProdDecl
import Phil.Core.AST.Types

parseExpr :: String -> Result Expr
parseExpr = runParser expr

parseExprOrData :: String -> Result (Either Expr Definition)
parseExprOrData =
  runParser $
  fmap Left (try expr <?> "expression") <|>
  fmap Right (dataDefinition <?> "data definition")

parseProgram :: String -> Result [Definition]
parseProgram = runParser program

runParser :: IndentationParserT Char Parser a -> String -> Result a
runParser p =
  parseString
    (evalIndentationParserT p initialIndentationState)
    mempty

initialIndentationState :: IndentationState
initialIndentationState =
  mkIndentationState
    0
    infIndentation
    True
    Ge

program :: (TokenParsing m, IndentationParsing m, Monad m) => m [Definition]
program = many definition <* eof

definition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
definition =
  (try dataDefinition <?> "data definition") <|>
  (try functionDefinition <?> "function definition") <|>
  (try typeSignature <?> "type signature") <|>
  (try classDefinition <?> "class definition") <|>
  (instanceDefinition <?> "instance definition")

identStyle :: CharParsing m => IdentifierStyle m
identStyle =
  IdentifierStyle
  { _styleName = "identifier"
  , _styleStart = letter <|> char '_'
  , _styleLetter = alphaNum <|> char '_' <|> char '\''
  , _styleReserved =
    HS.fromList
      [ "data"
      , "class"
      , "instance"
      , "where"
      , "forall"
      , "let"
      , "in"
      , "true"
      , "false"
      , "rec"
      , "case"
      , "of"
      ]
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }

keyword :: (TokenParsing m, Monad m) => String -> m ()
keyword = token . reserve identStyle

identifier :: (TokenParsing m, Monad m) => m Ident
identifier = Ident <$> token (ident identStyle <?> "identifier")

constructor :: (TokenParsing m, Monad m) => m Ctor
constructor = Ctor <$> token (ident ctorStyle <?> "constructor")
  where
    ctorStyle =
      IdentifierStyle
      { _styleName = "constructor"
      , _styleStart = upper
      , _styleLetter = alphaNum <|> char '_' <|> char '\''
      , _styleReserved = HS.empty
      , _styleHighlight = Constructor
      , _styleReservedHighlight = ReservedConstructor
      }

type_ :: (TokenParsing m, IndentationParsing m, Monad m) => m Type
type_ =
  token $
  (try tyFun <?> "function type") <|>
  (chainl1 typeArg (pure TyApp) <?> "type application")
  where
    tyFun =
      TyFun <$>
      typeArg <*
      symbol "->" <*>
      type_

typeArg :: (TokenParsing m, IndentationParsing m, Monad m) => m Type
typeArg = token $ atomic <|> parens type_
  where
    atomic =
      (TyCon . TypeCon <$> constructor) <|>
      TyVar <$> identifier

dataDefinition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
dataDefinition = do
  keyword "data"
  tyCtor <- localIndentation Gt constructor
  tyArgs <- many identifier
  symbolic '='
  ctors <- sepByNonEmpty prodDecl (symbolic '|')
  pure $ Data tyCtor tyArgs ctors
  where
    prodDecl =
      localIndentation Ge $
      ProdDecl <$>
      constructor <*>
      many typeArg

functionDefinition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
functionDefinition =
  fmap Function $
  FunctionBinding <$>
  identifier <*>
  localIndentation Gt (many identifier) <*
  symbolic '=' <*>
  expr

typeSignature :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
typeSignature =
  TypeSignature <$>
  identifier <*
  localIndentation Gt colon <*>
  typeScheme

constraints :: (TokenParsing m, IndentationParsing m, Monad m) => m [Type]
constraints =
  (multiple <?> "one or more constraints") <|>
  (pure <$> type_ <?> "a single constraint")
  where
    multiple =
      between
        (symbolic '(')
        (symbolic ')')
        (sepBy1 type_ comma)

typeScheme :: (TokenParsing m, IndentationParsing m, Monad m) => m TypeScheme
typeScheme =
  (quantified <?> "quantified type scheme") <|>
  (unquantified <?> "unquantified type scheme")
  where
    quantified =
      Forall <$>
      (try (keyword "forall") *>
      (S.fromList <$> many identifier)) <*
      dot <*>
      ((try (constraints <* symbol "=>") <?> "constraints") <|> pure []) <*>
      type_

    unquantified =
      Forall S.empty [] <$> type_

classDefinition :: TokenParsing m => m Definition
classDefinition = undefined

instanceDefinition :: TokenParsing m => m Definition
instanceDefinition = undefined

variableBinding :: (TokenParsing m, IndentationParsing m, Monad m) => m (Binding Expr)
variableBinding =
  VariableBinding <$>
  identifier <*
  localIndentation Gt (symbolic '=') <*>
  expr

pattern_ :: (TokenParsing m, IndentationParsing m, Monad m) => m Pattern
pattern_ =
  token $
  (try patId <?> "variable pattern") <|>
  (patCon <?> "constructor pattern") <|>
  (patLit <?> "literal pattern") <|>
  (patWildcard <?> "wildcard pattern")
  where
    patId = PatId <$> identifier
    patCon = PatCon <$> constructor <*> many identifier
    patLit = PatLit <$> literal
    patWildcard = symbolic '_' $> PatWildcard
    

expr :: (TokenParsing m, IndentationParsing m, Monad m) => m Expr
expr =
  token $
  (lam <?> "lambda expression") <|>
  (let_ <?> "let expression") <|>
  (letrec <?> "let rec expression") <|>
  (case_ <?> "case expression") <|>
  (app <?> "function application")
  where
    lam =
      token $
      Abs <$>
      (symbolic '\\' *>
       identifier <*
       dot) <*>
      expr

    let_ =
      Let <$>
      (keyword "let" *>
      variableBinding) <*>
      (keyword "in" *> expr)

    letrec =
      Rec <$>
      (keyword "let" *>
       keyword "rec" *>
      variableBinding) <*>
      (keyword "in" *> expr)

    atom =
      (fmap Lit literal <?> "literal") <|>
      (Id <$> identifier) <|>
      (prod <?> "data constructor") <|>
      (parens expr <?> "parenthesised expression")

    case_ =
      Case <$>
      (keyword "case" *>
       expr <*
       keyword "of") <*>
      (localIndentation Gt branches)
      where
        branches =
          some1 .
          absoluteIndentation $
          liftA2
            (,)
            pattern_
            (symbol "->" *>
             expr)

    prod = Prod <$> constructor <*> many atom

    app = chainl1 atom (pure App)

literal :: (TokenParsing m, Monad m) => m Literal
literal =
  (LitInt <$> integer) <|>
  (LitString <$> stringLiteral) <|>
  (LitChar <$> charLiteral) <|>
  (keyword "true" $> LitBool True) <|>
  (keyword "false" $> LitBool False)
