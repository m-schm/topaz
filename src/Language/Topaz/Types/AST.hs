{-# LANGUAGE UndecidableInstances, TemplateHaskell #-}
module Language.Topaz.Types.AST where
import Relude
import Control.Lens
import Language.Topaz.Types

import Text.Megaparsec (SourcePos)
import Control.Comonad.Cofree (Cofree, _unwrap)
import Text.Show
import Data.Functor.Classes
import Text.Show.Deriving (makeLiftShowsPrec)
import Data.Functor.Foldable
import qualified Control.Comonad.Trans.Cofree as F

import Data.Generics.Multiplate

data Plate n f = Plate
  { p_expr  ∷ Expr n → f (Expr n)
  , p_block ∷ Block n → f (Block n)
  , p_decl  ∷ Decl n Block → f (Decl n Block)
  }

instance Multiplate (Plate n) where
  multiplate Plate{..} = Plate buildExpr buildBlock buildDecl where
    buildExpr = _unwrap %%~ \case
      f :$ x → liftA2 (:$) (p_expr f) (p_expr x)
      f :$@ x → liftA2 (:$@) (p_expr f) (p_expr x)
      Lam as ret b → liftA2 (Lam as) (p_expr ret) (loc %%~ p_block $ b)
      etc → pure etc
    buildBlock (Block ds e) = Block <$> traverse p_decl ds <*> p_expr e
    buildDecl = \case
      DImport s i → pure (DImport s i)
      DBind s sc i as ret b → DBind s sc i as <$> p_expr ret <*> p_block b

  mkPlate ret = Plate (ret p_expr) (ret p_block) (ret p_decl)

data Span = Span SourcePos SourcePos

instance Show Span where show _ = "<span>"

instance Semigroup Span where
  Span a b <> Span x y = Span (a `min` x) (b `max` y)

data Ident = Ident Text | Prefix Text
  deriving Show

newtype ModulePath = ModulePath (NonEmpty Text)
  deriving (Eq, Ord, Show)

data Stage = Parse

type TTGC (c ∷ Type → Constraint) n =
  (c (TTGIdent n), c (TTGLam n), c (TTGArgs n))

data family TTGIdent (n ∷ Stage)
data instance TTGIdent 'Parse = RawIdent (Maybe ModulePath) Ident
  deriving Show

type family TTGLam (n ∷ Stage)
type instance TTGLam 'Parse = NonEmpty (Loc (Arg 'Parse))

type Expr n = Cofree (ExprF n) Span

data ExprF (n ∷ Stage) r
  = Lit Literal
  | r :$ r
  | r :$@ r
  | Lam (TTGLam n) r (Loc (Block n))
  | Var (TTGIdent n)
  | Rec
  | Hole
  deriving (Functor, Foldable, Traversable)

deriving instance (Show r, TTGC Show n) ⇒ Show (ExprF n r)

instance TTGC Show n ⇒ Show1 (ExprF n) where
  liftShowsPrec showsPrec' showList' prec = \case
    Lit lit → showString "Lit " . showsPrec 10 lit
    f :$ x → showsPrec' 10 f . showString " :$ " . showsPrec' 10 x
    f :$@ x → showsPrec' 10 f . showString " :$@ " . showsPrec' 10 x
    Lam as ret b →
      showString "Lam " . showsPrec 10 as . showString " " .
      showsPrec' 10 ret . showString " " . showsPrec 10 b
    Var v → showsPrec prec v
    Rec → showString "Rec"
    Hole → showString "Hole"

type family TTGArgs (n ∷ Stage)
type instance TTGArgs 'Parse = [Loc (Arg 'Parse)]

data Decl (n ∷ Stage) a
  = DImport Span Import
  | DBind Span (Scope a) Ident (TTGArgs n) (Expr n) (Block n)

deriving instance TTGC Show n ⇒ Show (Decl n a)

data Arg (n ∷ Stage)
  = Arg (Maybe Ident) (Expr n)
  | Implicit Ident (Expr n)
  | Instance (Maybe Ident) (Expr n)

deriving instance TTGC Show n ⇒ Show (Arg n)

data Scope a where
  Local  ∷ Scope a
  Global ∷ Scope TopLevel

deriving instance Show (Scope a)

data Import = Import
  { public ∷ Bool
  , path ∷ ModulePath
  , qualifier ∷ Maybe Text
  , names ∷ ImportedNames
  } deriving Show

data ImportedNames
  = All
  | Hiding [Text]
  | Using [Text]
  deriving Show

data Loc a = Loc a Span
  deriving (Show, Functor, Foldable, Traversable)

unLoc ∷ Loc a → a
unLoc (Loc a _) = a

loc ∷ Lens (Loc a) (Loc b) a b
loc = lens unLoc (\(Loc _ s) b → Loc b s)

locSpan ∷ Lens' (Loc a) Span
locSpan = lens (\(Loc _ s) → s) (\(Loc a _) s' → Loc a s')

instance Applicative Loc where
  pure = error "Loc is only Apply"
  Loc f s <*> Loc x t = Loc (f x) (s <> t)

data Block (n ∷ Stage) = Block [Decl n Block] (Expr n)
deriving instance TTGC Show n ⇒ Show (Block n)

data TopLevel (n ∷ Stage) = TopLevel [Decl n TopLevel] (Maybe (Expr n))
deriving instance TTGC Show n ⇒ Show (TopLevel n)
