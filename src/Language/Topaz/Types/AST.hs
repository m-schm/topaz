{-# LANGUAGE UndecidableInstances #-}
module Language.Topaz.Types.AST where
import Relude

import Language.Topaz.Types.Literal

import Control.Comonad.Cofree (Cofree(..))
import Control.Lens hiding ((:<))
import Data.Functor.Classes
import Text.Megaparsec (SourcePos)
import Text.Show

data Span = Span SourcePos SourcePos

instance Show Span where show _ = "<span>"

instance Semigroup Span where
  Span a b <> Span x y = Span (a `min` x) (b `max` y)

data Ident = Ident Text | Prefix Text
  deriving (Eq, Ord, Show)

data QIdent = QIdent (Maybe ModulePath) Ident
  deriving Show

data KnownIdent = LocalDef Ident | Known ModulePath Ident
  deriving Show

data ModulePath = ModulePath (NonEmpty Text) | Main
  deriving (Eq, Ord, Show)

data Ops a
  = Pfx (Ops' a)
  | Ifx a (Ops' a)
  deriving Show

data Ops' a
  = Binop (NonEmpty (Loc Text)) a (Ops' a)
  | Done
  deriving Show

data Stage = Parsed | Desugared | ScopeChecked

type TTGC (c ∷ Type → Constraint) n =
  ( c (TTGIdent n), c (TTGLam n), c (ExprX n)
  , c (PatX n)
  , c (TTGDecl n)
  )

type family TTGIdent (n ∷ Stage)
type family TTGLam (n ∷ Stage)
type family TTGDecl (n ∷ Stage)
type family ExprX (n ∷ Stage)
type family PatX (n ∷ Stage)

type Expr n = Cofree (ExprF n) Span

data ExprF (n ∷ Stage) r
  = Lit Literal
  | r :$ r
  | r :$@ r
  | Lam (TTGLam n) r (Loc (Block n))
  | Var (TTGIdent n)
  | Rec
  | Hole
  | X (ExprX n)
  deriving (Functor, Foldable, Traversable)

deriving instance (Show r, TTGC Show n) ⇒ Show (ExprF n r)

instance TTGC Show n ⇒ Show1 (ExprF n) where
  liftShowsPrec showsPrec' _ prec = \case
    Lit lit → showString "Lit " . showsPrec 10 lit
    f :$ x → showsPrec' 10 f . showString " :$ " . showsPrec' 10 x
    f :$@ x → showsPrec' 10 f . showString " :$@ " . showsPrec' 10 x
    Lam as ret b →
      showString "Lam " . showsPrec 10 as . showString " " .
      showsPrec' 10 ret . showString " " . showsPrec 10 b
    Var v → showsPrec prec v
    Rec → showString "Rec"
    Hole → showString "Hole"
    X a → showsPrec prec a

data Decl (n ∷ Stage) a
  = DImport Span Import
  | DBind Span (Scope a) Ident (Expr n) (Loc (Block n)) (TTGDecl n)

deriving instance TTGC Show n ⇒ Show (Decl n a)

data Arg (n ∷ Stage)
  = Arg (Maybe Ident) (Expr n)
  | Implicit Ident (Expr n)
  | Instance (Maybe Ident) (Expr n)

deriving instance TTGC Show n ⇒ Show (Arg n)

data Pattern (n ∷ Stage)
  = PVar Ident
  | PHole
  | PTup (AtLeastTwo (Pattern n))
  | PCtor (TTGIdent n) [Pattern n]
  | PX (PatX n)

data AtLeastTwo a = AtLeastTwo a (NonEmpty a)
  deriving (Functor, Foldable, Traversable)

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

data TopLevel (n ∷ Stage) =
  TopLevel ModulePath [Decl n TopLevel] (Maybe (Expr n))
deriving instance TTGC Show n ⇒ Show (TopLevel n)

data FixityPrec = FixityPrec (Maybe Word) (Maybe Fixity)
data Fixity = Infixl | Infixr

_unwrap ∷ Lens (Cofree f a) (Cofree g a) (f (Cofree f a)) (g (Cofree g a))
_unwrap f (x :< xs) = (x :<) <$> f xs
