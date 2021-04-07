module Language.Topaz.Desugar (desugar) where

import Language.Topaz.Parser ()
import Language.Topaz.Types.AST
import Language.Topaz.Types.Cofree

import Control.Lens hiding ((:<))
import Relude

type instance TTGIdent 'Desugared = QIdent
type instance TTGArgs 'Desugared = ()
type instance TTGLam 'Desugared = Loc (Arg 'Desugared)
type instance ExprX 'Desugared = Ops (Expr 'Desugared)
type instance PatX 'Desugared = Ops (Pattern 'Desugared)

desugar ∷ TopLevel 'Parsed → TopLevel 'Desugared
desugar (TopLevel mp ds me) = TopLevel mp (fmap decl ds) (fmap expr me)

block ∷ Block 'Parsed → Block 'Desugared
block (Block ds e) = Block (fmap decl ds) (expr e)

decl ∷ Decl 'Parsed a → Decl 'Desugared a
decl (Mutual s ds) = Mutual s (fmap decl ds)
decl (Decl s sc d) = Decl s sc $ case d of
  DImport i → DImport i -- TODO: modules
  DBindFn i t b as →
    let as' = as & mapped . loc %~ arg
        (t', b') = flattenArgs as' (expr t, over loc block b)
    in DBindFn i t' b' ()
  DBind pat ty b → undefined
  DRecord i ty c → undefined
  DType i ty cs → undefined

flattenArgs ∷ [Loc (Arg 'Desugared)]
  → (Expr 'Desugared, Loc (Block 'Desugared))
  → (Expr 'Desugared, Loc (Block 'Desugared))
flattenArgs = flip $ foldr go where
  go ∷ Loc (Arg 'Desugared)
    → (Expr 'Desugared, Loc (Block 'Desugared))
    → (Expr 'Desugared, Loc (Block 'Desugared))
  go a@(Loc _ sa) (t@(st :< _), b@(Loc _ sb)) =
    let b' = Block [] $ (sa <> sb) :< Lam a t b
    in ((sa <> st) :< Hole, Loc b' (sa <> sb))

expr ∷ Expr 'Parsed → Expr 'Desugared
expr = _unwrap %~ \case
  Lit l → Lit l
  f :$ x → expr f :$ expr x
  f :$@ x → expr f :$@ expr x
  Lam as t b →
    let as' = as & mapped . loc %~ arg
        t' = expr t
        b' = b & loc %~ block
    in unwrap $ flattenLam as' t' b'
  Var v → Var v
  Rec → Rec
  Hole → Hole
  X es → X (fmap expr es)

arg ∷ Arg 'Parsed → Arg 'Desugared
arg (Arg t pat ty) = Arg t (pattern_ pat) (expr ty)

pattern_ ∷ Pattern 'Parsed → Pattern 'Desugared
pattern_ = _unwrap %~ \case
  PVar ib → PVar ib
  PHole → PHole
  PTup ps → PTup (fmap pattern_ ps)
  PCtor c ps → PCtor c $ fmap pattern_ ps
  PAnnot p t → PAnnot (pattern_ p) (expr t)
  p :@ p' → pattern_ p :@ pattern_ p'
  PX ps → PX (fmap pattern_ ps)

flattenLam ∷ NonEmpty (Loc (Arg 'Desugared))
  → Expr 'Desugared
  → Loc (Block 'Desugared)
  → Expr 'Desugared
flattenLam as t b@(Loc _ sb) = foldr go innermost (init as) where
  innermost =
    let a@(Loc _ sa) = last as
    in (sa <> sb) :< Lam a t b

  go ∷ Loc (Arg 'Desugared) → Expr 'Desugared → Expr 'Desugared
  go a@(Loc _ sa) e@(se :< _) =
    let s = sa <> se
    in s :< Lam a (s :< Hole) (Loc (Block [] e) se)
