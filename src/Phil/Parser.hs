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
    False
    Gt

program :: (TokenParsing m, IndentationParsing m, Monad m) => m [Definition]
program = many definition <* eof

definition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
definition =
  (dataDefinition <?> "data definition") <|>
  (classDefinition <?> "class definition") <|>
  (instanceDefinition <?> "instance definition") <|>
  (try typeSignature <?> "type signature") <|>
  (functionDefinition <?> "function definition")

identStyle :: CharParsing m => IdentifierStyle m
identStyle =
  IdentifierStyle
  { _styleName = "identifier"
  , _styleStart = lower <|> char '_'
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
type_ = token tyFun
  where
    tyApp = chainl1 (localIndentation Gt typeArg) (pure TyApp) <?> "type application"
    tyFun = chainr1 tyApp (localIndentation Gt $ symbol "->" $> TyFun) <?> "function type"

typeArg :: (TokenParsing m, IndentationParsing m, Monad m) => m Type
typeArg = token $ atomic <|> parens type_
  where
    atomic =
      (TyCon . TypeCon <$> constructor) <|>
      (TyVar <$> identifier)

dataDefinition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
dataDefinition = do
  keyword "data"
  tyCtor <- constructor
  tyArgs <- many identifier
  symbolic '='
  ctors <- localIndentation Gt $ sepByNonEmpty prodDecl (symbolic '|')
  pure $ Data tyCtor tyArgs ctors
  where
    prodDecl =
      ProdDecl <$>
      constructor <*>
      many typeArg

functionBinding
  :: ( TokenParsing m
     , IndentationParsing m
     , Monad m
     )
  => m (Binding Expr)
functionBinding =
  FunctionBinding <$>
  identifier <*>
  many identifier <*
  symbolic '=' <*>
  localIndentation Gt expr

functionDefinition :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
functionDefinition = Function <$> functionBinding

typeSignature :: (TokenParsing m, IndentationParsing m, Monad m) => m Definition
typeSignature =
  TypeSignature <$>
  identifier <*
  colon <*>
  typeScheme

constraints :: (TokenParsing m, IndentationParsing m, Monad m) => m [Type]
constraints = option [] (try someConstraints <?> "constraints")
  where
    someConstraints = 
      ((multiple <?> "one or more constraints") <|>
      (pure <$> type_ <?> "a single constraint")) <*
      localIndentation Gt (symbol "=>")

    multiple = parens (sepBy1 type_ comma)

typeScheme :: (TokenParsing m, IndentationParsing m, Monad m) => m TypeScheme
typeScheme =
  (quantified <?> "quantified type scheme") <|>
  (unquantified <?> "unquantified type scheme")
  where
    quantified =
      Forall <$>
      (try (localIndentation Gt $ keyword "forall") *>
      (S.fromList <$> localIndentation Gt (many identifier))) <*
      localIndentation Gt dot <*>
      constraints <*>
      type_

    unquantified =
      Forall S.empty [] <$> type_

classDefinition
  :: ( Monad m
     , IndentationParsing m
     , TokenParsing m
     )
  => m Definition
classDefinition =
  Class <$>
  (keyword "class" *> constraints) <*>
  (type_ <* keyword "where") <*>
  localIndentation Gt
    (many
      (absoluteIndentation
        (liftA2 (,) identifier (colon *> type_) <?>
        "type signature")))

instanceDefinition
  :: ( TokenParsing m
     , IndentationParsing m
     , Monad m
     )
  => m Definition
instanceDefinition =
  Instance <$>
  (keyword "instance" *> constraints) <*>
  (type_ <* keyword "where") <*>
  localIndentation Gt (many $ absoluteIndentation functionBinding)

variableBinding :: (TokenParsing m, IndentationParsing m, Monad m) => m (Binding Expr)
variableBinding =
  VariableBinding <$>
  identifier <*
  symbolic '=' <*>
  expr

pattern_ :: (TokenParsing m, IndentationParsing m, Monad m) => m Pattern
pattern_ =
  token $
  (try patWildcard <?> "wildcard pattern") <|>
  (patId <?> "variable pattern") <|>
  (patCon <?> "constructor pattern") <|>
  (patLit <?> "literal pattern")
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
      (Var . Left <$> identifier) <|>
      (Var . Right <$> constructor) <|>
      (parens expr <?> "parenthesised expression")

    case_ =
      Case <$>
      (keyword "case" *>
       expr <*
       keyword "of") <*>
      localIndentation Gt branches
      where
        branches =
          some1 .
          absoluteIndentation $
          liftA2
            (,)
            pattern_
            (symbol "->" *>
             expr)

    app = chainl1 atom (pure App)

literal :: (TokenParsing m, Monad m) => m Literal
literal =
  (LitInt <$> integer) <|>
  (LitString <$> stringLiteral) <|>
  (LitChar <$> charLiteral) <|>
  (keyword "true" $> LitBool True) <|>
  (keyword "false" $> LitBool False)
