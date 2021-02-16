module Language.Topaz.ScopeCheck (scopeCheck) where
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

data ScopeError
  = NoIdent (Maybe ModulePath) Ident
  | NoQual ModulePath

scopeCheck ∷ TopLevel 'Parse
  → Either (NonEmpty ScopeError) (TopLevel 'ScopeChecked)
scopeCheck = undefined

phase1 ∷ TopLevel 'Parse → ChkM (TopLevel 'ScopeCheck)
phase1 (TopLevel mp ds me) = TopLevel mp
  <$> traverse declTop ds
  <*> traverse expr me

declTop ∷ Decl 'Parse TopLevel → ChkM (Decl 'ScopeCheck TopLevel)
declTop = error "not implemented"

decl ∷ Decl 'Parse Block → ChkM (Decl 'ScopeCheck Block)
decl = error "not implemented"

expr ∷ Expr 'Parse → ChkM (Expr 'ScopeCheck)
expr = error "not implemented"
