module Language.Topaz.ScopeCheck where
import Relude
import Language.Topaz.Types.AST

data instance TTGIdent 'ScopeCheck = LocalDef Ident | Known ModulePath Ident
  deriving Show

data Env = Env
  { unqualified ∷ Map Ident ModulePath
  , qualified ∷ Map ModulePath (Set Ident)
  , locals ∷ [Set Ident]
  }
