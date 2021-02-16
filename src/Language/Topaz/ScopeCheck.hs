module Language.Topaz.ScopeCheck
  ( scopeCheck, ScopeError(..)
  ) where
import Relude
import Language.Topaz.Types.AST

data instance TTGIdent 'ScopeCheck
  = DuringCheck (TTGIdent 'ScopeChecked)
  | Unknown (Maybe ModulePath) Ident
  deriving Show
data instance TTGIdent 'ScopeChecked = LocalDef Ident | Known ModulePath Ident
  deriving Show

data Env = Env
  { unqualified ∷ Map Ident ModulePath
  , qualified ∷ Map ModulePath (Set Ident)
  , locals ∷ [Set Ident]
  }

newtype ChkM a = ChkM (State Env a)
  deriving newtype (Functor, Applicative, Monad)

data Result a = Ok a | Err (NonEmpty ScopeError)
  deriving Functor

instance Applicative Result where
  pure = Ok
  Ok f  <*> Ok x   = Ok $ f x
  Err e <*> Ok _   = Err e
  Ok _  <*> Err e  = Err e
  Err e <*> Err e' = Err $ e <> e'

data ScopeError
  = NoIdent (Maybe ModulePath) Ident
  | NoQual ModulePath

scopeCheck ∷ TopLevel 'Parsed
  → Either (NonEmpty ScopeError) (TopLevel 'ScopeChecked)
scopeCheck = undefined

phase1 ∷ TopLevel 'Parsed → ChkM (TopLevel 'ScopeCheck)
phase1 (TopLevel mp ds me) = TopLevel mp
  <$> traverse decl ds
  <*> traverse expr me

decl ∷ Decl 'Parsed a → ChkM (Decl 'ScopeCheck a)
decl = \case
  DImport s i → pure (DImport s i) -- TODO: handle imports
  DBind s sc i as t e → undefined

expr ∷ Expr 'Parsed → ChkM (Expr 'ScopeCheck)
expr = error "not implemented"

phase2 ∷ TopLevel 'ScopeCheck → Result (TopLevel 'ScopeChecked)
phase2 (TopLevel mp ds me) = TopLevel mp
  <$> traverse runDecl ds
  <*> traverse runExpr me

runDecl ∷ Decl 'ScopeCheck a → Result (Decl 'ScopeChecked a)
runDecl = error "not implemented"

runExpr ∷ Expr 'ScopeCheck → Result (Expr 'ScopeChecked)
runExpr = error "not implemented"
