module Language.Topaz.Types.Value where

import Relude

import Language.Topaz.Types.Literal
import Language.Topaz.Types.AST

type Env = [(QIdent, Value)]

newtype Meta = Meta Int
  deriving newtype (Eq, Ord, Enum)

data Spine = SSnoc Spine ArgType Value | SNil

-- | Strict left fold on 'Spine's
foldSp ∷ (a → ArgType → Value → a) → a → Spine → a
foldSp f !z (SSnoc s a v) = foldSp f (f z a v) s
foldSp _ !z SNil          = z

data Value
  = VLit Literal
  | VFlex Meta Spine
  | VRigid QIdent Spine
  | VLam ArgType Ident Value (Value → Value)
  | VPi ArgType Ident Value (Value → Value)
  | VType

pattern VVar ∷ QIdent → Value
pattern VVar q = VRigid q SNil

infixl 4 :>
pattern (:>) ∷ [a] → a → [a]
pattern xs :> x = x : xs
{-# COMPLETE (:>), [] #-}

-- data ExprF (n ∷ Stage) r
--   = Lit Literal
--   | r :$ r
--   | r :$@ r
--   | Lam (TTGLam n) r (Loc (Block n))
--   | Pi (TTGLam n) r (Loc (Block n))
--   | Var (TTGIdent n)
--   | Rec
--   | Hole
--   | Match r [(Pattern n, Loc (Block n))]
