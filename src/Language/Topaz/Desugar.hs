module Language.Topaz.Desugar (desugar) where
import Relude
import Control.Lens hiding ((:<))
import Language.Topaz.Types.AST
import Language.Topaz.Parser ()

import Control.Comonad.Cofree (unwrap, Cofree(..))
import Control.Comonad

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
  let (t', b') = flattenArgs as (t, b)
  in DBind s sc i () t' b'

flattenArgs ∷ TTGArgs 'Parsed
  → (Expr 'Parsed, Block 'Parsed)
  → (Expr 'Desugared, Block 'Desugared)
flattenArgs = error "not implemented"

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
arg = error "not implemented"

flattenLam ∷ NonEmpty (Loc (Arg 'Desugared))
  → Expr 'Desugared
  → Loc (Block 'Desugared)
  → Expr 'Desugared
flattenLam as t b@(Loc _ sb) = foldr go innermost (init as) where
  innermost =
    let a@(Loc _ sa) = last as
    in (sa <> sb) :< Lam a t b

  go ∷ Loc (Arg 'Desugared) → Expr 'Desugared → Expr 'Desugared
  go a@(Loc _ sa) e = (sa <> extract e) :< _
