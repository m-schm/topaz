module Language.Topaz.Types where
import Relude

data Literal
  = LInt Integer
  | LNat Natural
  | LFloat Double
  | LStr Text
  | LChar Char
  deriving (Eq, Ord, Show)
