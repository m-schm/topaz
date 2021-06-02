{-# LANGUAGE UndecidableInstances #-}
module Language.Topaz.Types.AST where
import Relude

import Language.Topaz.Types.Literal
import Language.Topaz.Types.Cofree

import Control.Lens hiding ((:<))
import Text.Megaparsec (SourcePos)
import Text.Show
import GHC.Exts (IsList(..))

data Span = Span SourcePos SourcePos

instance Show Span where show _ = "<span>"

instance Semigroup Span where
  Span a b <> Span x y = Span (a `min` x) (b `max` y)

data Ident = Ident Text | Prefix Text
  deriving (Eq, Ord, Show)

data QIdent = QIdent (Maybe ModulePath) Ident
  deriving (Eq, Show)

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

-- | Empty list -> 'Main'
instance IsList ModulePath where
  type Item ModulePath = Text
  fromList = maybe Main ModulePath . nonEmpty
  toList Main = []
  toList (ModulePath xs) = Relude.toList xs

data Ops a
  = Pfx (Ops' a)
  | Ifx a (Ops' a)
  deriving (Show, Functor)

data Ops' a
  = Binop (NonEmpty (Loc Text)) a (Ops' a)
  | Done
  deriving (Show, Functor)

data Stage = Parsed | Desugared | Checked

type TTGC (c ∷ Type → Constraint) f n =
  ( c (TTGIdent n f), c (TTGLam n f), c (ExprX n f)
  , c (PatX n f)
  , c (TTGArgs n f)
  )

type family TTGIdent (n ∷ Stage) (f ∷ NodeType → Type)
type family TTGLamF (n ∷ Stage) (f ∷ NodeType → Type)
type family TTGArgs (n ∷ Stage) (f ∷ NodeType → Type)
type family ExprX (n ∷ Stage) (f ∷ NodeType → Type)
type family PatX (n ∷ Stage) (f ∷ NodeType → Type)
type family TTGTupleF (n ∷ Stage) ∷ Type → Type

data NodeType
  = EXP | PAT | BLK | ARG
  | DEC IsTopLevel | DEC' IsTopLevel | CTOR IsTopLevel | FIELD
  | BIND | RAWIDENT

data ASTF (s ∷ Stage) (f ∷ NodeType → Type) (i ∷ NodeType) where
  Lit         ∷ Literal → ASTF s f 'EXP
  (:$), (:$@) ∷ f 'EXP → f 'EXP → ASTF s f 'EXP
  Lam, Pi     ∷ TTGLamF n (f 'ARG) → f 'EXP → f 'BLK → ASTF s f 'EXP
  Tuple       ∷ TTGTupleF n (f 'EXP) → ASTF s f 'EXP
  TupleT      ∷ TTGTupleF n (f 'PAT, f 'EXP) → ASTF s f 'EXP
  Row         ∷ Map Ident (f 'BIND, f 'EXP) → ASTF s f 'EXP
  Var         ∷ TTGIdent n f → ASTF s f 'EXP
  Rec, Hole   ∷ ASTF s f 'EXP
  Match       ∷ f 'EXP → [(f 'PAT, f 'BLK)] → ASTF s f 'EXP
  X           ∷ ExprX n f → ASTF s f 'EXP

  PVar   ∷ f 'BIND → ASTF s f 'PAT
  PHole  ∷ ASTF s f 'PAT
  PTup   ∷ TTGTupleF n (f 'EXP) → ASTF s f 'PAT
  PCtor  ∷ TTGIdent n f → [f 'PAT] → ASTF s f 'PAT
  PAnnot ∷ f 'PAT → f 'EXP → ASTF s f 'PAT
  (:@)   ∷ f 'PAT → f 'PAT → ASTF s f 'PAT
  PX     ∷ PatX n f → ASTF s f 'PAT

  Decl   ∷ Scope a → f ('DEC' a) → ASTF s f ('DEC a)
  Mutual ∷ [f ('DEC a)] → ASTF s f ('DEC a)

  DImport ∷ Import → ASTF s f ('DEC' a)
  DBindFn ∷ f 'BIND → f 'EXP → f 'BLK → TTGArgs n f → ASTF s f ('DEC' a)
  DBind   ∷ f 'PAT → f 'EXP → f 'BLK → ASTF s f ('DEC' a)
  DRecord ∷ f 'BIND → f 'EXP → f 'BLK → f ('CTOR a) → ASTF s f ('DEC' a)
  DType   ∷ f 'BIND → f 'EXP → f 'BLK → [f ('CTOR a)] → ASTF s f ('DEC' a)

  Ctor  ∷ Scope a → Maybe (f 'BIND) → [f 'FIELD] → ASTF s f ('CTOR a)
  Field ∷ ArgType → Maybe (f 'BIND) → f 'EXP → ASTF s f 'FIELD

  Bind     ∷ FixityPrec → f 'RAWIDENT → ASTF s f 'BIND
  RawIdent ∷ Ident → ASTF s f 'RAWIDENT

  Arg ∷ ArgType → f 'PAT → f 'EXP → ASTF s f 'ARG

infix 5 :@
infixl 3 :$, :$@

data Expr n
data Pattern n
data Decl n a
data Decl' n a

data ArgType = Visible | Implicit | Instance
  deriving (Show, Eq)

data AtLeastTwo a = AtLeastTwo a (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

data IsTopLevel = ItsTopLevel | NotTopLevel

data Scope (a ∷ IsTopLevel) where
  Local  ∷ Scope a
  Global ∷ Scope ItsTopLevel

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
