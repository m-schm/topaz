module Language.Topaz.Desugar (desugar) where

import Language.Topaz.Parser ()
import Language.Topaz.Types.AST
import Language.Topaz.Types.Indexed

import Control.Lens hiding ((:<))
import Relude
import Control.Arrow ((***))

type instance TTGIdent 'Desugared _ = QIdent
type instance TTGArgs 'Desugared _ = ()
type instance ExprX 'Desugared f = Ops (f 'EXP)
type instance PatX 'Desugared f = Ops (f 'PAT)

type instance TTGTupleF 'Desugared = []
type instance TTGLamF 'Desugared = Identity

type SP = ICofree Span (ASTF 'Parsed)
type SD = ICofree Span (ASTF 'Desugared)

desugar ∷ TopLevel 'Parsed → TopLevel 'Desugared
desugar (TopLevel mp ds me) = TopLevel mp (fmap decl ds) (fmap expr me)

block ∷ SP 'BLK → SD 'BLK
block = _iunwrap %~ \(Block ds e) → Block (fmap decl ds) (expr e)

decl ∷ Decl 'Parsed a → Decl 'Desugared a
decl = _iunwrap %~ \case
  Mutual ds → Mutual (fmap decl ds)
  Decl sc d → Decl sc $ d & _iunwrap %~ \case
    DImport i → DImport i -- TODO: modules
    DBindFn i t b as →
      let as' = fmap arg as
          (t', b') = flattenArgs as' (expr t, block b)
      in DBindFn (coerceBind i) t' b' ()
    DBind pat ty b → undefined
    DRecord i ty c → undefined
    DType i ty cs → undefined

flattenArgs ∷ [SD 'ARG]
  → (Expr 'Desugared, SD 'BLK)
  → (Expr 'Desugared, SD 'BLK)
flattenArgs = flip $ foldr go where
  go ∷ SD 'ARG → (Expr 'Desugared, SD 'BLK) → (Expr 'Desugared, SD 'BLK)
  go a@(sa :@< _) (t@(st :@< _), b@(sb :@< _)) =
    let b' = Block [] $ (sa <> sb) :@< Lam (LamF $ Identity a) t b
    in ((sa <> st) :@< Hole, (sa <> sb) :@< b')

expr ∷ Expr 'Parsed → Expr 'Desugared
expr = _iunwrap %~ \case
  Lit l → Lit l
  f :$ x → expr f :$ expr x
  f :$@ x → expr f :$@ expr x
  Lam as t b →
    let LamF as' = fmap arg as
    in iunwrap $ flattenLam as' (expr t) (block b)
  Pi _ _ _ -> undefined
  Match _ _ -> undefined
  Var v → Var v
  Rec → Rec
  Hole → Hole
  Tuple xs → Tuple $ coerce $ fmap expr xs
  TupleT xs → undefined
  Row r → Row $ fmap (coerceBind *** expr) r
  X es → X (fmap expr es)

arg ∷ SP 'ARG → SD 'ARG
arg = _iunwrap %~ \case Arg t pat ty → Arg t (pattern_ pat) (expr ty)

pattern_ ∷ Pattern 'Parsed → Pattern 'Desugared
pattern_ = _iunwrap %~ \case
  PVar ib → PVar $ coerceBind ib
  PHole → PHole
  PTup ps → PTup (coerce $ fmap pattern_ ps)
  PCtor c ps → PCtor c $ fmap pattern_ ps
  PAnnot p t → PAnnot (pattern_ p) (expr t)
  p :@ p' → pattern_ p :@ pattern_ p'
  PX ps → PX (fmap pattern_ ps)

flattenLam ∷ NonEmpty (SD 'ARG)
  → Expr 'Desugared
  → SD 'BLK
  → Expr 'Desugared
flattenLam as t b@(sb :@< _) = foldr go innermost (init as) where
  innermost =
    let a@(sa :@< _) = last as
    in (sa <> sb) :@< Lam (LamF $ Identity a) t b

  go ∷ SD 'ARG → Expr 'Desugared → Expr 'Desugared
  go a@(sa :@< _) e@(se :@< _) =
    let s = sa <> se
    in s :@< Lam (LamF $ Identity a) (s :@< Hole) (se :@< Block [] e)

coerceBind ∷ ICofree a (ASTF s) 'BIND → ICofree a (ASTF s') 'BIND
coerceBind (sp :@< Bind fp ri) = sp :@< Bind fp (coerceRawIdent ri)

coerceRawIdent :: ICofree a (ASTF s) 'RAWIDENT -> ICofree a (ASTF s') 'RAWIDENT
coerceRawIdent (sp :@< RawIdent i) = sp :@< RawIdent i
