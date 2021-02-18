module Language.Topaz.Desugar (desugar) where

import Language.Topaz.Parser ()
import Language.Topaz.Types.AST

import Control.Comonad.Cofree (unwrap, Cofree(..))
import Control.Lens hiding ((:<))
import Relude

type instance TTGIdent 'Desugared = QIdent
type instance TTGArgs 'Desugared = ()
type instance TTGLam 'Desugared = Loc (Arg 'Desugared)

desugar ∷ TopLevel 'Parsed → TopLevel 'Desugared
desugar (TopLevel mp ds me) = TopLevel mp (fmap decl ds) (fmap expr me)

block ∷ Block 'Parsed → Block 'Desugared
block (Block ds e) = Block (fmap decl ds) (expr e)

decl ∷ Decl 'Parsed a → Decl 'Desugared a
decl (DImport s i) = DImport s i
decl (DBind s sc i as t b) =
  let as' = as & mapped . loc %~ arg
      (t', b') = flattenArgs as' (expr t, over loc block b)
  in DBind s sc i () t' b'

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

arg ∷ Arg 'Parsed → Arg 'Desugared
arg (Arg mi t) = Arg mi (expr t)
arg (Implicit i t) = Implicit i (expr t)
arg (Instance mi t) = Instance mi (expr t)

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
