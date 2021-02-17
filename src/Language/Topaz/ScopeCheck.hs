module Language.Topaz.ScopeCheck
  ( scopeCheck, ScopeError(..)
  ) where
import Relude hiding (local)
import Control.Lens
import Language.Topaz.Types.AST
import Language.Topaz.Desugar ()

import qualified Data.List.NonEmpty as NE

type instance TTGIdent 'ScopeChecked = KnownIdent
type instance TTGArgs 'ScopeChecked = ()
type instance TTGLam 'ScopeChecked = Loc (Arg 'ScopeChecked)

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

newtype ChkM a = ChkM (StateT (NonEmpty Env) Result a)
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
  & runChkM [mempty]
  where
    runChkM s (ChkM ma) = case evalStateT ma s of
      Ok a   → Right a
      Err es → Left es

decl ∷ Decl 'Desugared a → ChkM (Decl 'ScopeChecked a)
decl = \case
  DImport s i → pure (DImport s i) -- TODO: handle imports
  DBind s sc i () t e →
    DBind s sc i () <$> expr t <*> (e & loc %%~ block)

block ∷ Block 'Desugared → ChkM (Block 'ScopeChecked)
block (Block ds e) = local $ liftA2 Block (traverse decl ds) (expr e)

expr ∷ Expr 'Desugared → ChkM (Expr 'ScopeChecked)
expr = _unwrap %%~ \case
  Lit l → pure (Lit l)
  f :$ x → liftA2 (:$) (expr f) (expr x)
  f :$@ x → liftA2 (:$@) (expr f) (expr x)
  Lam a ty b → local $
    liftA3 Lam (loc arg a) (expr ty) (loc block b)
  Var (QIdent mmp i) → case mmp of
    Nothing → _
    Just mp → _
  Rec → _
  Hole → _

arg ∷ Arg 'Desugared → ChkM (Arg 'ScopeChecked)
arg (Arg mi e) = _
arg (Implicit i e) = _
arg (Instance mi e) = _

local ∷ ChkM a → ChkM a
local ma = push *> ma <* pop where
  push = ChkM $ modify' (NE.cons mempty)
  pop = ChkM $ modify' (NE.fromList . tail)
