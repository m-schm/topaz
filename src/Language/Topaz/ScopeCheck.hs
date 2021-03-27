module Language.Topaz.ScopeCheck
  ( scopeCheck, ScopeError(..)
  ) where

import Language.Topaz.Desugar ()
import Language.Topaz.Types.AST hiding (Local)
import Language.Topaz.Types.Cofree

import Control.Lens hiding ((:<))
import Data.Generics.Labels ()
import qualified Data.List.NonEmpty as NE
import Data.Traversable
import Relude hiding (local)
import Language.Topaz.Utils

type instance TTGIdent 'ScopeChecked = KnownIdent
type instance TTGArgs 'ScopeChecked = Void
type instance TTGLam 'ScopeChecked = Loc (Arg 'ScopeChecked)
type instance ExprX 'ScopeChecked = Void
type instance PatX 'ScopeChecked = Void

data NameSource = Imported ModulePath | Local

data Arity = NotCtor | IsCtor Word

data NameInfo a = NameInfo
  { fixity ∷ FixityPrec
  , arity  ∷ Arity
  , bind   ∷ Span
  , val    ∷ a
  } deriving Generic

data Env = Env
  { unqualified ∷ Map Ident (NameInfo NameSource)
  , qualified ∷ Map ModulePath (Map Ident (NameInfo ModulePath))
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
  deriving (Functor, Foldable, Traversable)

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
  (>>) = (*>)

data ScopeError
  = NoIdent (Maybe ModulePath) Ident
  | NoQual ModulePath
  | Ambiguous [ModulePath] Ident
  | NameTaken (Loc Ident) Span
  | NotACtor QIdent
  | WrongArity (QIdent, Word) Word
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
decl (Decl s sc d) = Decl s sc <$> case d of
  DImport i → pure (DImport i) -- TODO: handle imports
  DBindFn ib t b () → do
    t' ← expr t
    insertLocal ib
    b' ← b & loc %%~ block
    let IdentBind _ (Loc _ s') = ib
    pure $ DBind (s' :< PVar ib) t' b'
  DBind p t b → do
    t' ← expr t
    p' ← pattern_ p
    b' ← b & loc %%~ block
    pure $ DBind p' t' b'
  DMutual ds → undefined
  DRecord ib t c → do
    insertLocal ib
    liftA2 (DRecord ib) (expr t) (ctor c)
  DType ib t cs → do
    insertLocal ib
    liftA2 (DType ib) (expr t) (traverse ctor cs)

ctor ∷ Ctor 'Desugared a → ChkM (Ctor 'ScopeChecked a)
ctor (Ctor s sc mib fs) = do
  fs' ← local $ traverse field fs
  whenJust mib \ib → insertCtor ib (length' fs)
  pure $ Ctor s sc mib fs'

field ∷ Field 'Desugared → ChkM (Field 'ScopeChecked)
field (Field t mib ty) = do
  whenJust mib insertLocal
  Field t mib <$> expr ty

block ∷ Block 'Desugared → ChkM (Block 'ScopeChecked)
block (Block ds e) = local $ liftA2 Block (traverse decl ds) (expr e)

expr ∷ Expr 'Desugared → ChkM (Expr 'ScopeChecked)
expr = _unwrap %%~ \case
  Lit l → pure (Lit l)
  f :$ x → liftA2 (:$) (expr f) (expr x)
  f :$@ x → liftA2 (:$@) (expr f) (expr x)
  Lam a ty b → local $
    liftA3 Lam (loc arg a) (expr ty) (loc block b)
  Pi a ty b → local $
    liftA3 Pi (loc arg a) (expr ty) (loc block b)
  Var i → Var . val <$> lookup i
  Rec → pure Rec
  Hole → pure Hole
  Match e cs → Match
    <$> expr e
    <*> for cs (bitraverse pattern_ $ loc block)
  X ops → undefined

arg ∷ Arg 'Desugared → ChkM (Arg 'ScopeChecked)
arg (Arg t p ty) = do
  ty' ← expr ty
  p' ← pattern_ p
  pure $ Arg t p' ty'

pattern_ ∷ Pattern 'Desugared → ChkM (Pattern 'ScopeChecked)
pattern_ = _unwrap %%~ \case
  PVar ib    → insertLocal ib $> PVar ib
  PHole      → pure PHole
  PTup ps    → PTup <$> traverse pattern_ ps
  PCtor c ps → do
    (ni, a) ← lookupArity c
    let a' = length' ps
    when (a /= a') $ throw $ WrongArity (c, a) a'
    PCtor (val ni) <$> traverse pattern_ ps
  PAnnot p ty → liftA2 PAnnot (pattern_ p) (expr ty)
  p :@ p'     → liftA2 (:@) (pattern_ p) (pattern_ p')
  PX pd       → undefined

insertLocal ∷ IdentBind → ChkM ()
insertLocal ib = insertLocal' ib NotCtor

insertCtor ∷ IdentBind → Word → ChkM ()
insertCtor ib = insertLocal' ib . IsCtor

insertLocal' ∷ IdentBind → Arity → ChkM ()
insertLocal' (IdentBind fp li@(Loc i s)) a = do
  assertFree li
  #unqualified . at i ?= NameInfo fp a s Local

local ∷ ChkM a → ChkM a
local ma = push *> ma <* pop where
  push = ChkM $ modify' (NE.cons mempty)
  pop = ChkM $ modify' (NE.fromList . tail)

lookup ∷ QIdent → ChkM (NameInfo KnownIdent)
lookup (QIdent mmp i) = ChkM $ case mmp of
  Nothing → gets (ifirstOf $ ifolded <. #unqualified . ix i)
    >>= maybe (throw' $ NoIdent mmp i) pure
    <&> \(d, v) → v & #val %~ \case
      Local       → LocalDef (fromIntegral d) i
      Imported mp → Known mp i
  Just mp → gets (toListOf $ folded . #qualified . ix mp) >>= \case
    [] → throw' $ NoQual mp
    xs → case xs ^.. folded . ix i of
      []  → throw' $ NoIdent mmp i
      [p] → pure $ p & #val %~ flip Known i
      ps  → throw' $ Ambiguous (fmap (view #val) ps) i

lookupArity ∷ QIdent → ChkM (NameInfo KnownIdent, Word)
lookupArity qi = do
  ni ← lookup qi
  case arity ni of
    NotCtor → throw $ NotACtor qi
    IsCtor a  → pure (ni, a)

throw ∷ ScopeError → ChkM a
throw = ChkM . throw'

throw' ∷ MonadTrans t ⇒ ScopeError → t Result a
throw' = lift . Err . pure

assertFree ∷ Loc Ident → ChkM ()
assertFree li@(Loc i _) =
  whenJustM prevBind $ throw . NameTaken li
  where
    prevBind ∷ ChkM (Maybe Span)
    prevBind = gets $ firstOf $ #unqualified . ix i . #bind
