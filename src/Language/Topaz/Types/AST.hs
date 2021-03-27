{-# LANGUAGE UndecidableInstances #-}
module Language.Topaz.Types.AST where
import Relude

import Language.Topaz.Types.Literal
import Language.Topaz.Types.Cofree

import Control.Lens hiding ((:<))
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

data KnownIdent
  = LocalDef     -- ^ A locally bound name
      Word       -- ^ How many scope "groups" (e.g. patterns) away it's bound
      Ident      -- ^ The actual name;
                 -- Linearity of names in patterns is already checked
  | Known        -- ^ An imported name
      ModulePath -- ^ What module it's imported from
      Ident      -- ^ The name imported from the module
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
  , c (TTGArgs n)
  )

type family TTGIdent (n ∷ Stage)
type family TTGLam (n ∷ Stage)
type family TTGArgs (n ∷ Stage)
type family ExprX (n ∷ Stage)
type family PatX (n ∷ Stage)

type Expr n = Cofree (ExprF n) Span
data ExprF (n ∷ Stage) r
  = Lit Literal
  | r :$ r
  | r :$@ r
  | Lam (TTGLam n) r (Loc (Block n))
  | Pi (TTGLam n) r (Loc (Block n))
  | Tuple [r]
  | TupleT [(Pattern n, r)]
  | Row (Map Ident (IdentBind, r))
  | Var (TTGIdent n)
  | Rec
  | Hole
  | Match r [(Pattern n, Loc (Block n))]
  | X (ExprX n)
  deriving (Functor, Foldable, Traversable)

deriving instance (Show r, Show (Pattern n), TTGC Show n) ⇒ Show (ExprF n r)

data Decl (n ∷ Stage) a
  = Decl Span (Scope a) (Decl' n a)
  | Mutual Span [Decl n a]
deriving instance TTGC Show n ⇒ Show (Decl n a)

data Decl' (n ∷ Stage) a
  = DImport Import
  | DBindFn IdentBind (Expr n) (Loc (Block n)) (TTGArgs n)
  | DBind (Pattern n) (Expr n) (Loc (Block n))
  | DRecord IdentBind (Expr n) (Ctor n a)
  | DType IdentBind (Expr n) [Ctor n a]
deriving instance TTGC Show n ⇒ Show (Decl' n a)

data Ctor (n ∷ Stage) a = Ctor Span (Scope a) (Maybe IdentBind) [Field n]
deriving instance TTGC Show n ⇒ Show (Ctor n a)

data Field (n ∷ Stage) = Field ArgType (Maybe IdentBind) (Expr n)
deriving instance TTGC Show n ⇒ Show (Field n)

data IdentBind = IdentBind FixityPrec (Loc Ident)
  deriving Show

data Arg (n ∷ Stage) = Arg ArgType (Pattern n) (Expr n)
deriving instance TTGC Show n ⇒ Show (Arg n)

data ArgType = Visible | Implicit | Instance
  deriving Show

type Pattern n = Cofree (PatternF n) Span
data PatternF (n ∷ Stage) r
  = PVar IdentBind
  | PHole
  | PTup (AtLeastTwo r)
  | PCtor (TTGIdent n) [r]
  | PAnnot r (Expr n)
  | r :@ r
  | PX (PatX n)
  deriving (Functor, Foldable, Traversable)
infix 5 :@

deriving instance (Show r, TTGC Show n, Show (Expr n)) ⇒ Show (PatternF n r)

data AtLeastTwo a = AtLeastTwo a (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

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
  deriving Show
data Fixity = Infixl | Infixr
  deriving Show
