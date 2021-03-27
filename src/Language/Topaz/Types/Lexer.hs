module Language.Topaz.Types.Lexer
  ( Token(..), pattern TEquals
  , AbsIndent(..)
  , Lexeme(..), unLexeme
  , Literal(..)
  ) where
import Relude

import Language.Topaz.Types.Literal

import qualified Data.List as Str
import Text.Megaparsec (VisualStream(..))
import Text.Show (showsPrec)

data Lexeme a = L a Token a
  deriving (Eq, Ord)

instance Show (Lexeme a) where
  showsPrec p = showsPrec p . unLexeme

instance Ord a ⇒ VisualStream [Lexeme a] where
  tokensLength p = length . showTokens p
  showTokens _ = Str.unwords . fmap show . toList

unLexeme ∷ Lexeme a → Token
unLexeme (L _ t _) = t

data Token
  = TImport | TLet | TPub | TRec | TDo | TRecord | TType | TMutual
  | TMatch | TIn
  | TColon | TAt | THole | TComma | TPipe | TPeriod
  | TArrowL | TArrowR | TArrowR'
  | TBraceL | TBraceR | TBracketL | TBracketR | TParenL | TParenR
  | TVar Text | TOp Text | TInfix Text | TPrefix Text | TSymbol Text
  | TIndent | TDedent | TSemicolon | TNewline
  | TLit Literal
  deriving (Eq, Ord, Show)

pattern TEquals :: Token
pattern TEquals = TOp "="

data AbsIndent = AbsIndent { tabs ∷ Int, spcs ∷ Int }
  deriving (Eq, Ord, Show)
