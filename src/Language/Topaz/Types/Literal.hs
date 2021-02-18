module Language.Topaz.Types.Literal where
import Relude

data Literal
  = LInt Integer
  | LNat Natural
  | LFloat Double
  | LStr Text
  | LChar Char
  deriving (Eq, Ord, Show)
