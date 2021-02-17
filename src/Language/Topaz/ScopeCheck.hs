module Language.Topaz.ScopeCheck
  ( scopeCheck, ScopeError(..)
  ) where
import Relude hiding (local)
import Control.Lens
import Language.Topaz.Types.AST
import Language.Topaz.Desugar ()

import qualified Relude.Unsafe as Unsafe

type instance TTGIdent 'ScopeChecked = KnownIdent
type instance TTGArgs 'ScopeChecked = ()

data Env = Env
  { unqualified ∷ Map Ident ModulePath
  , qualified ∷ Map ModulePath (Set Ident)
  , locals ∷ Set Ident
  }

instance Semigroup Env where
  Env uq q l <> Env uq' q' l' = Env (uq <> uq') (q <> q') (l <> l')

instance Monoid Env where
  mappend = (<>)
  mempty = Env mempty mempty mempty

newtype ChkM a = ChkM (StateT [Env] Result a)
  deriving newtype (Functor, Applicative, Monad)

data Result a = Ok a | Err (NonEmpty ScopeError)
  deriving Functor

instance Applicative Result where
  pure = Ok
  Ok f  <*> Ok x   = Ok $ f x
  Err e <*> Ok _   = Err e
  Ok _  <*> Err e  = Err e
  Err e <*> Err e' = Err $ e <> e'

instance Monad Result where
  return = pure
  Err e >>= f = Err e
  Ok  x >>= f = f x

data ScopeError
  = NoIdent (Maybe ModulePath) Ident
  | NoQual ModulePath
  deriving Show

scopeCheck ∷ TopLevel 'Desugared
  → Either (NonEmpty ScopeError) (TopLevel 'ScopeChecked)
scopeCheck (TopLevel mp ds me) =
  TopLevel mp <$> traverse decl ds <*> traverse expr me
  & _

decl ∷ Decl 'Desugared a → ChkM (Decl 'ScopeChecked a)
decl = \case
  DImport s i → pure (DImport s i) -- TODO: handle imports
  DBind s sc i () t e →
    DBind s sc i () <$> expr t <*> (e & loc %%~ block)

block :: Block 'Desugared → ChkM (Block 'ScopeChecked)
block = error "not implemented"

expr ∷ Expr 'Desugared → ChkM (Expr 'ScopeChecked)
expr = error "not implemented"

local ∷ ChkM a → ChkM a
local ma = push *> ma <* pop where
  push = ChkM $ modify' (mempty :)
  pop = ChkM $ modify' Unsafe.tail
