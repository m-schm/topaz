{-# LANGUAGE UndecidableInstances #-}
module Language.Topaz.Types.AST where
import Relude

import Language.Topaz.Types.Literal

import Control.Lens hiding ((:<))
import Text.Megaparsec (SourcePos)
import Text.Show
import GHC.Exts (IsList(..))
import Language.Topaz.Types.Indexed (ICofree)

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

type family TTGIdent (n ∷ Stage) (f ∷ NodeType → Type)
type family TTGArgs (n ∷ Stage) (f ∷ NodeType → Type)
type family ExprX (n ∷ Stage) (f ∷ NodeType → Type)
type family PatX (n ∷ Stage) (f ∷ NodeType → Type)

type family TTGLamF (n ∷ Stage) ∷ Type → Type
type family TTGTupleF (n ∷ Stage) ∷ Type → Type

-- you can't put quantified constraints inside type synonyms, for some reason
type Forall ∷ (Type → Constraint) → (Type → Type) → Constraint
class (∀ a. c (f a)) ⇒ Forall c f
instance (∀ a. c (f a)) ⇒ Forall c f

-- https://gitlab.haskell.org/ghc/ghc/-/issues/14860
-- can't quantify constraints involving type families
-- but newtype wrapper around it is ok
newtype TupleF s a = TupleF (TTGTupleF s a)
deriving instance Show (TTGTupleF s a) ⇒ Show (TupleF s a)
deriving instance Functor (TTGTupleF s) ⇒ Functor (TupleF s)

newtype LamF s a = LamF (TTGLamF s a)
deriving instance Show (TTGLamF s a) ⇒ Show (LamF s a)
deriving instance Functor (TTGLamF s) ⇒ Functor (LamF s)

type TTGC ∷ (Type → Constraint) → Stage → (NodeType → Type) → Constraint
type TTGC c s f =
  ( c (TTGIdent s f), c (ExprX s f), c (PatX s f), c (TTGArgs s f)
  , Forall c (LamF s), Forall c (TupleF s)
  )

data NodeType
  = EXP | PAT | BLK | ARG
  | DEC IsTopLevel | DEC' IsTopLevel | CTOR IsTopLevel | FIELD
  | BIND | RAWIDENT

data ASTF (s ∷ Stage) (f ∷ NodeType → Type) (i ∷ NodeType) where
  Lit         ∷ Literal → ASTF s f 'EXP
  (:$), (:$@) ∷ f 'EXP → f 'EXP → ASTF s f 'EXP
  Lam, Pi     ∷ LamF s (f 'ARG) → f 'EXP → f 'BLK → ASTF s f 'EXP
  Tuple       ∷ TupleF s (f 'EXP) → ASTF s f 'EXP
  TupleT      ∷ TupleF s (f 'PAT, f 'EXP) → ASTF s f 'EXP
  Row         ∷ Map Ident (f 'BIND, f 'EXP) → ASTF s f 'EXP
  Var         ∷ TTGIdent s f → ASTF s f 'EXP
  Rec, Hole   ∷ ASTF s f 'EXP
  Match       ∷ f 'EXP → [(f 'PAT, f 'BLK)] → ASTF s f 'EXP
  X           ∷ ExprX s f → ASTF s f 'EXP

  PVar   ∷ f 'BIND → ASTF s f 'PAT
  PHole  ∷ ASTF s f 'PAT
  PTup   ∷ TupleF s (f 'PAT) → ASTF s f 'PAT
  PCtor  ∷ TTGIdent s f → [f 'PAT] → ASTF s f 'PAT
  PAnnot ∷ f 'PAT → f 'EXP → ASTF s f 'PAT
  (:@)   ∷ f 'PAT → f 'PAT → ASTF s f 'PAT
  PX     ∷ PatX s f → ASTF s f 'PAT

  Decl   ∷ Scope a → f ('DEC' a) → ASTF s f ('DEC a)
  Mutual ∷ [f ('DEC a)] → ASTF s f ('DEC a)

  DImport ∷ Import → ASTF s f ('DEC' a)
  DBindFn ∷ f 'BIND → f 'EXP → f 'BLK → TTGArgs s f → ASTF s f ('DEC' a)
  DBind   ∷ f 'PAT → f 'EXP → f 'BLK → ASTF s f ('DEC' a)
  DRecord ∷ f 'BIND → f 'EXP → f ('CTOR a) → ASTF s f ('DEC' a)
  DType   ∷ f 'BIND → f 'EXP → [f ('CTOR a)] → ASTF s f ('DEC' a)

  Ctor  ∷ Scope a → Maybe (f 'BIND) → [f 'FIELD] → ASTF s f ('CTOR a)
  Field ∷ ArgType → Maybe (f 'BIND) → f 'EXP → ASTF s f 'FIELD

  Bind     ∷ FixityPrec → f 'RAWIDENT → ASTF s f 'BIND
  RawIdent ∷ Ident → ASTF s f 'RAWIDENT

  Block ∷ [f ('DEC 'NotTopLevel)] → f 'EXP → ASTF s f 'BLK

  Arg ∷ ArgType → f 'PAT → f 'EXP → ASTF s f 'ARG

infix 5 :@
infixl 3 :$, :$@

deriving instance
  ( ∀ j. Show (f j)
  , TTGC Show s f
  ) ⇒ Show (ASTF s f i)

type Expr n = ICofree Span (ASTF n) 'EXP
type Pattern n = ICofree Span (ASTF n) 'PAT
type Decl n a = ICofree Span (ASTF n) ('DEC a)
type Decl' n a = ICofree Span (ASTF n) ('DEC' a)

data ArgType = Visible | Implicit | Instance
  deriving (Show, Eq)

data AtLeastTwo a = AtLeastTwo a (NonEmpty a)
  deriving (Show, Eq, Functor, Foldable, Traversable)

data IsTopLevel = AtTopLevel | NotTopLevel

data Scope (a ∷ IsTopLevel) where
  Local  ∷ Scope a
  Global ∷ Scope 'AtTopLevel

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

data TopLevel (n ∷ Stage) =
  TopLevel ModulePath [Decl n 'AtTopLevel] (Maybe (Expr n))
-- deriving instance TTGC Show n ⇒ Show (TopLevel n)

data FixityPrec = FixityPrec (Maybe Word) (Maybe Fixity)
  deriving Show
data Fixity = Infixl | Infixr
  deriving Show
