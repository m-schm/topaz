module Language.Topaz.Lexer where

import Language.Topaz.Types.Lexer

import Control.Lens hiding (lastOf, noneOf)
import Data.Char
import Data.Generics.Labels ()
import qualified Data.Set as S
import qualified Data.Text as T
import Relude hiding (many, some)
import qualified Relude.Unsafe as Unsafe
import Text.Megaparsec hiding (State, Token, count)
import Text.Megaparsec.Char

data ParseErr
  = InvalidIndent AbsIndent
  | UnopenedCloseBrace
  deriving (Eq, Ord)

instance ShowErrorComponent ParseErr where
  showErrorComponent = \case
    InvalidIndent ai → "Invalid indent depth: " <> show ai
    UnopenedCloseBrace → "No matching open-brace for this close-brace"

type Parser' = Parsec ParseErr Text

type Parser = StateT LexState Parser'

data LexState = LexState
  { indents ∷ [Indent]
  , lastNonWs ∷ Int
  } deriving Generic

data Indent
  = Implicit AbsIndent
  | Explicit

lex ∷ Parser' [Lexeme SourcePos]
lex = do
  begin ← statePosState <$> getParserState
  toks ← evalStateT go $ LexState [] 0
  pure $ attachLexemePos begin toks
  where

    go ∷ Parser [Lexeme Int]
    go = (<>) <$> (fmap join $ many tok) <* hidden eof <*> unwind

    unwind ∷ Parser [Lexeme Int]
    unwind = annotIndent $ dedent $ AbsIndent 0 0

    tokenLoc ∷ Parser (Lexeme Int)
    tokenLoc = do
      begin ← getOffset
      t ← aToken
      end ← subtract 1 <$> getOffset
      #lastNonWs .= end
      pure $ L begin t end

    annotIndent ∷ Parser [Token] → Parser [Lexeme Int]
    annotIndent p = do
      loc ← use #lastNonWs
      fmap (\t → L loc t loc) <$> p

    tok ∷ Parser [Lexeme Int]
    tok = mempty <$  takeWhile1P Nothing (== ' ')
      <|> mempty <$  lineComment
      <|> pure   <$> tokenLoc
      <|> annotIndent indent

attachLexemePos ∷ Traversable t ⇒
  PosState Text → t (Lexeme Int) → t (Lexeme SourcePos)
attachLexemePos posst xs = evalState (traverse go xs) posst where
  go ∷ Lexeme Int → State (PosState Text) (Lexeme SourcePos)
  go (L x t y) = do
    px ← reachOffsetNoLine x <$> get
    let py = reachOffsetNoLine y px
    put py
    pure $ L (pstateSourcePos px) t (pstateSourcePos py)

aToken ∷ Parser Token
aToken = choice @[]
  [ TLit       <$> literal
  , TIndent    <$  string "{{" <* pushIndent Explicit
  , TDedent    <$  string "}}" <* tryToDedent
  , TSemicolon <$  string ";"
  , TBraceL    <$  string "{"
  , TBraceR    <$  string "}"
  , TParenL    <$  string "("
  , TParenR    <$  string ")"
  , TBracketL  <$  string "["
  , TBracketR  <$  string "]"
  , TComma     <$  string ","
  , symbol "." TPeriod
  , symbol "@" TAt
  , symbol ":" TColon
  , symbol "<-" TArrowL
  , symbol "->" TArrowR
  , symbol "=>" TArrowR'
  , symbol "|" TPipe
  , keyword "_" THole
  , keyword "do" TDo
  , keyword "import" TImport
  , keyword "in" TIn
  , keyword "let" TLet
  , keyword "match" TMatch
  , keyword "pub" TPub
  , keyword "rec" TRec
  , keyword "record" TRecord
  , keyword "type" TRecord
  , TSymbol <$  char '\'' <*> ident
  , TVar    <$> ident
  , TOp     <$> operator
  , TInfix  <$> try (backtick operator)
  , TOp     <$> backtick ident
  , TPrefix <$  char '`' <*> operator
  ]

  where
    tryToDedent = getIndent >>= \case
      Explicit   → popIndent
      Implicit _ → customFailure UnopenedCloseBrace
    mkKeyword p x tok = try do
      y ← p
      guard $ x == y
      pure tok
    symbol = mkKeyword operator
    keyword = mkKeyword ident

backtick ∷ Parser a → Parser a
backtick p = char '`' *> p <* char '`'
{-# INLINE backtick #-}

literal ∷ Parser Literal
literal = label "literal" $
      LNat . Unsafe.read <$> some digitChar
  <|> try do (s1, s2) ← sign
             ds ← some digitChar
             frac s1 ds <|> pure (LInt . s2 $ Unsafe.read ds)
  <|> LStr . T.pack <$ char '"' <*> many (strChar '"') <* char '"'
  <|> try (LChar <$ char '\'' <*> strChar '\'' <* char '\'')
  where
    -- impredicative polymorphism when
    sign ∷ (Num a, Num b) ⇒ Parser (a → a, b → b)
    sign = option (id, id) ((negate, negate) <$ char '-')
    {-# INLINE sign #-}
    frac f s = do
      p ← char '.'
      ds ← T.unpack <$> takeWhile1P Nothing isDigit
      pure $ LFloat . f . Unsafe.read $ p : ds ++ s
    {-# INLINE frac #-}
{-# INLINE literal #-}

strChar ∷ Char → Parser Char
strChar c = noneOf @[] ['\\', c] <|> char '\\' *> escChar where
  escChar ∷ Parser Char
  escChar = anySingle >>= \case
    c' | c == c' → pure c
    'n'  → pure '\n'
    'e'  → pure '\ESC'
    '\\' → pure '\\'
    '0'  → pure '\NUL'
    'r'  → pure '\r'
    't'  → pure '\t'
    'x'  → hexEsc 2
    'u'  → hexEsc 4
    'U'  → hexEsc 8
    c'   → failure (Just (Tokens [c']))
                    (S.fromList $ fmap (Tokens . pure) escChars)
    where escChars = "ne\\\"'0rtxuU" ∷ [Char]
          {-# INLINE escChars #-}
          hexEsc n = chr . readHex <$> replicateM n hexDigitChar
          readHex ∷ String → Int
          readHex = foldr (\n acc → digitToInt n + 16*acc) 0
  {-# INLINE escChar #-}

lineComment ∷ Parser ()
lineComment = () <$ string ";;" <* takeWhile1P Nothing (/= '\n')

operator ∷ Parser Text
operator = takeWhile1P Nothing isOpChar <?> "operator" where
  isOpChar c = c `notElem` specialCase && generalCategory c `elem` letters
  letters ∷ [GeneralCategory]
  letters =
    [ OtherPunctuation, DashPunctuation
    , MathSymbol, CurrencySymbol, OtherSymbol
    ]
  specialCase = "\"',;" ∷ String

ident, ident' ∷ Parser Text
ident  = takeWhile1P Nothing isIdentChar                 <?> "identifier"
ident' = takeWhile1P Nothing ((== '\'') ||^ isIdentChar) <?> "identifier"

isIdentChar ∷ Char → Bool
isIdentChar c = generalCategory c `elem` letters where
  letters ∷ [GeneralCategory]
  letters =
    [ UppercaseLetter, LowercaseLetter, TitlecaseLetter, ModifierLetter
    , OtherLetter, DecimalNumber ]

indent ∷ Parser [Token]
indent = do
  ind ← lastOf $ char '\n' *> absIndent <* optional lineComment
  getIndent >>= \case
    Explicit   → pure []
    Implicit i → case ind `compare` i of
      LT → dedent ind
      EQ → pure [TNewline]
      GT → pushIndent (Implicit ind) $> [TIndent]
  where
    absIndent = AbsIndent <$> count (char '\t') <*> count (char ' ')

dedent ∷ AbsIndent → Parser [Token]
dedent ind = go [] where
  go acc = getIndent >>= \case
    Explicit   → pure acc
    Implicit i → case ind `compare` i of
      LT → popIndent *> go (TDedent : acc)
      EQ → pure acc
      GT → customFailure (InvalidIndent ind)

getIndent ∷ Parser Indent
getIndent = gets $
  indents >>> \case [] → Implicit (AbsIndent 0 0); x:_ → x

pushIndent ∷ Indent → Parser ()
pushIndent = (#indents %=) . (:)

popIndent ∷ Parser ()
popIndent = #indents %= \case [] → []; _:xs → xs

lastOf ∷ MonadParsec e s m ⇒ m a → m a
lastOf p = do
  x ← p
  (x <$ notFollowedBy p) <|> lastOf p
{-# INLINE lastOf #-}

count ∷ MonadParsec e s m ⇒ m a → m Int
count p = go 0 where
  go n = option n $ p *> go (succ n)
