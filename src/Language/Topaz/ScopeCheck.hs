module Language.Topaz.ScopeCheck
  ( scopeCheck, ScopeError(..)
  ) where

import Language.Topaz.Desugar ()
import Language.Topaz.Types.AST hiding (Local)

import Control.Lens
import Data.Generics.Labels ()
import qualified Data.List.NonEmpty as NE
import Relude hiding (local)

type instance TTGIdent 'ScopeChecked = KnownIdent
type instance TTGDecl 'ScopeChecked = ()
type instance TTGLam 'ScopeChecked = Loc (Arg 'ScopeChecked)
type instance ExprX 'ScopeChecked = Void

data NameSource = Imported ModulePath | Local
data WithFixity a = WithFixity FixityPrec a
  deriving (Functor, Foldable, Traversable)

pattern Unknown ∷ a -> WithFixity a
pattern Unknown a = WithFixity (FixityPrec Nothing Nothing) a

unFixity ∷ WithFixity a → a
unFixity (WithFixity _ a) = a

data Env = Env
  { unqualified ∷ Map Ident (WithFixity NameSource)
  , qualified ∷ Map ModulePath (Map Ident (WithFixity ModulePath))
  } deriving Generic

instance Semigroup Env where
  Env uq q <> Env uq' q' = Env (uq <> uq') (q <> q')

instance Monoid Env where
  mappend = (<>)
  mempty = Env mempty mempty

newtype ChkM a = ChkM (StateT (NonEmpty Env) Result a)
  deriving newtype (Functor, Applicative, Monad)

instance MonadState Env ChkM where
  get = ChkM $ gets head
  put = ChkM . assign neHead where
    neHead = lens head (\(_ :| xs) y → y :| xs)

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
  Err e >>= _ = Err e
  Ok  x >>= f = f x

data ScopeError
  = NoIdent (Maybe ModulePath) Ident
  | NoQual ModulePath
  | Ambiguous [ModulePath] Ident
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
  DBind s sc i t b f → do
    t' ← expr t
    #unqualified . at i ?= WithFixity f Local
    b' ← loc block b
    pure $ DBind s sc i t' b' ()

block ∷ Block 'Desugared → ChkM (Block 'ScopeChecked)
block (Block ds e) = local $ liftA2 Block (traverse decl ds) (expr e)

expr ∷ Expr 'Desugared → ChkM (Expr 'ScopeChecked)
expr = _unwrap %%~ \case
  Lit l → pure (Lit l)
  f :$ x → liftA2 (:$) (expr f) (expr x)
  f :$@ x → liftA2 (:$@) (expr f) (expr x)
  Lam a ty b → local $
    liftA3 Lam (loc arg a) (expr ty) (loc block b)
  Var i → Var <$> lookup i
  Rec → pure Rec
  Hole → pure Hole
  X ops → undefined

arg ∷ Arg 'Desugared → ChkM (Arg 'ScopeChecked)
arg (Arg mi e) = do
  e' ← expr e
  whenJust mi \i →
    #unqualified . at i ?= Unknown Local
  pure $ Arg mi e'
arg (Implicit i e) = do
  e' ← expr e
  #unqualified . at i ?= Unknown Local
  pure $ Implicit i e'
arg (Instance mi e) = do
  e' ← expr e
  whenJust mi \i →
    #unqualified . at i ?= Unknown Local
  pure $ Instance mi e'

local ∷ ChkM a → ChkM a
local ma = push *> ma <* pop where
  push = ChkM $ modify' (NE.cons mempty)
  pop = ChkM $ modify' (NE.fromList . tail)

lookup ∷ QIdent → ChkM KnownIdent
lookup (QIdent mmp i) = ChkM $ case mmp of
  Nothing →
    gets (firstOf $ folded . #unqualified . ix i . folded) >>= \case
      Nothing            → throw $ NoIdent mmp i
      Just Local         → pure $ LocalDef i
      Just (Imported mp) → pure $ Known mp i
  Just mp →
    gets (toListOf $ folded . #qualified . ix mp) >>= \case
      [] → throw $ NoQual mp
      xs → case xs ^.. folded . ix i . folded of
        []  → throw $ NoIdent mmp i
        [p] → pure $ Known p i
        ps  → throw $ Ambiguous ps i
  where throw = lift . Err . pure
