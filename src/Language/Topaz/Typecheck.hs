{-# LANGUAGE TemplateHaskell #-}
module Language.Topaz.Typecheck where

import Control.Lens hiding ((:<), (:>))
import Control.Monad.Trans.Except
import Data.List (lookup)
import qualified Data.Text as T
import Language.Topaz.Eval
import Language.Topaz.ScopeCheck ()
import Language.Topaz.Types.AST
import Language.Topaz.Types.Cofree
import Language.Topaz.Types.Literal
import Language.Topaz.Types.Result
import Language.Topaz.Types.Value
import Relude hiding (force)
import Data.Traversable


data MetaCtx = MetaCtx
  { _nextMeta ∷ Meta
  , _solvedMetas ∷ IntMap Value
  }
makeLenses ''MetaCtx

newtype MetaMap = MetaMap { _metaMap ∷ IntMap Value }
makeLenses ''MetaMap

type instance Index MetaMap = Meta
type instance IxValue MetaMap = Value
instance Ixed MetaMap
instance At MetaMap where
  at (Meta i) = metaMap . at i
  {-# INLINE at #-}

-- TODO
newtype ChkM a = ChkM (StateT MetaCtx (ReaderT Env (Result TypeError)) a)
  deriving newtype (Functor, Applicative, Monad, MonadReader Env)

instance MonadState MetaMap ChkM where
  state f = ChkM do
    (x, MetaMap s') ← f . MetaMap <$> use solvedMetas
    (solvedMetas .= s') $> x

data TypeError
  = CantUnify Value Value
  | -- | probably caught by scopechecking, doesn't hurt to be sure
    Unbound KnownIdent

newMeta ∷ ChkM Meta
newMeta = ChkM $ nextMeta <<%= succ

throw ∷ TypeError → ChkM a
throw = ChkM . lift . lift . Err . pure

eval' ∷ Expr 'Checked → ChkM Value
eval' = liftA2 eval ask . pure

fresh ∷ MonadReader Env m ⇒ Ident → m QIdent
fresh n = asks (isJust . lookup q)
  >>= bool (pure q) (fresh (addTick n))
  where
    q = QIdent Nothing n
    addTick (Ident t)  = Ident $ T.snoc t '\''
    addTick (Prefix t) = Prefix $ T.snoc t '\''

withNeutral ∷ MonadReader Env m ⇒ Ident → (Value → m a) → m a
withNeutral n f = do
  q ← fresh n
  let v = VVar q
  local ((q, v) :) $ f v

app ∷ ArgType → Value → Value → Value
app a (VLam a' _ _ f) x
  | a == a'             = f x
  | otherwise           = error "mismatched argument visibility"
app a (VFlex m sp)    x = VFlex m (SSnoc sp a x)
app a (VRigid q sp)   x = VRigid q (SSnoc sp a x)
app _ _               _ = error "`app` called without apply-able lhs"

appSp ∷ Value → Spine → Value
appSp = foldSp (flip app)

force ∷ Value → ChkM Value
force v = fmap (fromMaybe v) $ runMaybeT do
  VFlex m sp ← pure v
  Just v' ← use (at m)
  pure $ v' `appSp` sp

-- | unify two Values
(~?) ∷ Value → Value → ExceptT (Value, Value) ChkM ()
_v ~? _v' = do
  (v, v') ← lift $ liftA2 (,) (force _v) (force _v')
  let unifyIf = bool (throwE (v, v')) (pure ())
  case (v, v') of
    (VLit l, VLit l') → unifyIf (l == l')

    (VPi a n dom cod, VPi a' _ dom' cod') → do
      unifyIf (a == a')
      dom ~? dom'
      withNeutral n $ liftA2 (~?) cod cod'

    (VLam a n dom cod, VLam a' _ dom' cod') → do
      unifyIf (a == a')
      dom ~? dom'
      withNeutral n $ liftA2 (~?) cod cod'

    (VLam a n _ cod, _) → withNeutral n $ liftA2 (~?) cod (app a v')
    (_, VLam a n _ cod) → withNeutral n $ liftA2 (~?) (app a v) cod

    (VRigid q sp, VRigid q' sp') → do
      unifyIf (q == q')
      unifyIf =<< sp ~~? sp'
    (VFlex m sp, VFlex m' sp') → do
      unifyIf (m == m')
      unifyIf =<< sp ~~? sp'

    (VFlex m sp, _) → _
    (_, VFlex m sp) → _

    (VType, VType) → pure ()
    (_, _) → throwE (v, v')

-- | unify two 'Spine's, returning 'False' if something was wrong with the
-- spines themselves (e.g. mismatched lengths)
(~~?) ∷ Spine → Spine → ExceptT (Value, Value) ChkM Bool
SNil        ~~? SNil           = pure True
SSnoc s a v ~~? SSnoc s' a' v'
  | a == a'                    = do v ~? v'; s ~~? s'
  | otherwise                  = pure False
_           ~~? _              = pure False

(~!) ∷ Value → Value → ChkM ()
v ~! v' = v ~? v'
  &   runExceptT
  >>= either (throw . uncurry CantUnify) pure

check ∷ Expr 'Checked → Value → ChkM (Expr 'Checked)
check expr v_ = case (unwrap expr, v_) of

  (Tuple xs, VType) → do
    xs' ← for xs \x → (extract x :< PHole ,) <$> check x VType
    pure $ extract expr :< TupleT xs'

  (_, v) → do
    (e', v') ← infer expr
    v ~! v'
    pure $ e'

-- | @(prim)@ "module" for primitive types
primType ∷ Ident → Value
primType i = VRigid (QIdent (Just ["(prim)"]) i) SNil

infer ∷ Expr 'Checked → ChkM (Expr 'Checked, Value)
infer expr@(s :< e) = case e of
  Lit l → pure $ (expr ,) $ case l of
    LInt _   → primType (Ident "Int")
    LNat _   → primType (Ident "Nat")
    LFloat _ → primType (Ident "Float")
    LStr _   → primType (Ident "String")
    LChar _  → primType (Ident "Char")

  f :$ x → infer f >>= \case
    (f', VPi Visible _ dom cod) → do
      x' ← check x dom
      t ← cod <$> eval' x
      pure (s :< (f' :$ x'), t)
    _ → error "type error" -- TODO

  f :$@ x → infer f >>= \case
    (f', VPi Implicit _ dom cod) → do
      x' ← check x dom
      t ← cod <$> eval' x
      pure (s :< (f' :$ x'), t)
    _ → error "type error" -- TODO

  Lam ts cess lbs → undefined
  Pi ts cess lbs → undefined

  Tuple xs → do
    (xs', ts) ← unzip <$> traverse infer xs
    let pats = fmap (_ :< PHole ,) xs'
    pure $ if all isVType ts
      then (s :< Tuple xs', _)
      else (s :< TupleT pats, VType)
  TupleT ts → _

  Row mip_icess → undefined

  Var i → undefined

  Rec → undefined
  Hole → undefined
  Match cess l_p_cpsslbs → undefined

  X v → absurd v

isVType ∷ Value → Bool
isVType = \case VType → True; _ → False
