{-# LANGUAGE CPP #-}
module Language.Topaz.Parser where
import Relude hiding (All, many, some)
import Control.Lens hiding ((:<))
import Language.Topaz.Types.AST
import Language.Topaz.Types.Lexer (unLexeme, Lexeme(..), Token(..))

import Control.Applicative.Combinators.NonEmpty
import Control.Comonad
import Control.Comonad.Cofree
import qualified Data.List.NonEmpty as UnsafeNE
import qualified Data.Set as S
import Relude.Extra (foldMap1, foldl1')
import qualified Text.Megaparsec as MP
import Text.Megaparsec hiding (Token, token, some, sepBy1, satisfy)

#define DEBUG
#ifdef DEBUG
import Text.Megaparsec.Debug
#else
dbg _ x = x
{-# INLINE dbg #-}
#endif

data instance TTGIdent 'Parse = RawIdent (Maybe ModulePath) Ident
  deriving Show
type instance TTGLam 'Parse = NonEmpty (Loc (Arg 'Parse))
type instance TTGArgs 'Parse = [Loc (Arg 'Parse)]

type Parser = Parsec Void [Lexeme SourcePos]

topLevel ∷ Parser (TopLevel 'Parse)
topLevel = TopLevel
  <$> many (decl pub <* many (token TNewline))
  <*> optional (expr AnythingGoes)
  <*  many (token TNewline)
  <*  eof
  where
    pub ∷ Parser (Loc (Scope TopLevel))
    pub = Loc Global <$> token TPub

block ∷ Parser (Loc (Block 'Parse))
block = indented big
    <|> inline
  where
    big = Block
      <$> many (decl empty <* some (token TNewline))
      <*> expr AnythingGoes
    inline = expr AnythingGoes
      <&> \e → Loc (Block mempty e) (extract e)

data EqualsBehavior = AnythingGoes | NoEquals | NoLambda
  deriving Eq

decl ∷ Parser (Loc (Scope a)) → Parser (Decl 'Parse a)
decl pub = let_ <|> import_
  where

    let_ = do
      Loc s beg ← pub <|> (Loc Local <$> token TLet)
      Loc i _ ← ident
      as ← many arg
      mret ← optional $ token TColon *> expr NoEquals
      eq ← token (TOp "=")
      let ret = fromMaybe (eq :< Hole) mret
      Loc b end ← block
      pure $ DBind (beg <> end) s i as ret b

    import_ = do
      (sc, ms, is) ← try do
        (sc, ms) ← option (False, Nothing) $
          (True ,) . Just . view locSpan <$> pub
        (sc, ms, ) <$> token TImport
      undefined

arg ∷ Parser (Loc (Arg 'Parse))
arg = (\(Loc i s) → Loc (Arg i (s :< Hole)) s) <$> bare
  <|> parens explicit
  <|> braces implicit
  <|> brackets instance_
  where
    bare = over loc Just <$> ident
       <|> Loc Nothing <$> token THole

    explicit = do
      Loc i s ← bare
      ty ← option (s :< Hole) $ token TColon *> expr AnythingGoes
      pure $ Loc (Arg i ty) (s <> extract ty)

    implicit = do
      Loc i s ← ident
      ty ← option (s :< Hole) $ token TColon *> expr AnythingGoes
      pure $ Loc (Implicit i ty) (s <> extract ty)

    instance_ = do
      name ← optional (ident <* token TColon)
      ty ← expr AnythingGoes
      let s = maybe id ((<>) . view locSpan) name
      pure $ Loc (Instance (fmap unLoc name) ty) (s $ extract ty)

-- TODO: operators
expr ∷ EqualsBehavior → Parser (Expr 'Parse)
expr eqb = dbg "expr" $
      when' (eqb /= NoLambda) lam
  <|> foldl1' (.$) <$> some (expr1 eqb)
  where

    lam = do
      (as, mret, s) ← try $ liftA3 (,,)
        (some arg)
        (optional $ token TColon *> expr NoLambda)
        (token TArrowR')
      let ret = fromMaybe (s :< Hole) mret
      body@(Loc _ bs) ← block
      pure $ (view locSpan (head as) <> bs)
        :< Lam as ret body

    f .$ x = (extract f <> extract x) :< (f :$ x)

expr1 ∷ EqualsBehavior → Parser (Expr 'Parse)
expr1 eqb = dbg "expr1" $
      var
  <|> (\(Loc e s) → s :< e) <$> literal
  <|> parens (expr eqb)
  where

    var ∷ Parser (Expr 'Parse)
    var = do
      path ← pathPart `endBy'` token TPeriod
      Loc name end ← ident
      let mp = viaNonEmpty ModulePath $ fmap unLoc path
          beg = path ^? _head . locSpan
      pure $ maybe id (<>) beg end :< Var (RawIdent mp name)

    literal = satisfy ('l':|"iteral") \case
      TLit l → Just $ Lit l
      _      → Nothing


satisfy ∷ NonEmpty Char → (Token → Maybe a) → Parser (Loc a)
satisfy = satisfy' . S.singleton . Label

satisfy' ∷ Set (ErrorItem (Lexeme SourcePos)) → (Token → Maybe a)
  → Parser (Loc a)
satisfy' err pred = MP.token lex err where
  lex (L x t y) = fmap (\a → Loc a (Span x y)) $ pred t

token ∷ Token → Parser Span
token t = do
  here ← pstateSourcePos . statePosState <$> getParserState
  view locSpan <$> satisfy' (err here) (guard . (== t))
  where err pos = S.singleton $ Tokens [L pos t pos]

ident ∷ Parser (Loc Ident)
ident = satisfy ('i':|"dentifier") \case
  TVar    v → Just $ Ident v
  TInfix  v → Just $ Ident v
  TPrefix v → Just $ Prefix v
  _         → Nothing

pathPart ∷ Parser (Loc Text)
pathPart = MP.token lex err where
  err = S.singleton $ Label ('i':|"dentifier")
  lex (L x t y) = case t of
    TVar v → Just $ Loc v $ Span x y
    _      → Nothing

mkSurround ∷ Parser Span → Parser Span → Parser a → Parser (Loc a)
mkSurround l r = \p → do
  sl ← l
  x ← p
  sr ← r
  pure $ Loc x (sl <> sr)

indented, parens', brackets', braces' ∷ Parser a → Parser (Loc a)
indented = mkSurround (token TIndent) (token TDedent)
{-# INLINE indented #-}
parens' = mkSurround (token TParenL) (token TParenR)
{-# INLINE parens' #-}
brackets' = mkSurround (token TBracketL) (token TBracketR)
{-# INLINE brackets' #-}
braces' = mkSurround (token TBraceL) (token TBraceR)
{-# INLINE braces' #-}

parens, brackets, braces ∷ Parser a → Parser a
parens = between (token TParenL) (token TParenR)
{-# INLINE parens #-}
brackets = between (token TBracketL) (token TBracketR)
{-# INLINE brackets #-}
braces = between (token TBraceL) (token TBraceR)
{-# INLINE braces #-}

when' ∷ Alternative f ⇒ Bool → f a → f a
when' True x = x
when' False _ = empty
{-# INLINE when' #-}

unMaybe ∷ MonadPlus f ⇒ f (Maybe a) → f a
unMaybe = (>>= maybe empty pure)
{-# INLINE unMaybe #-}

endBy' ∷ Parser a → Parser sep → Parser [a]
endBy' p sep = many $ try (p >>= \x → x <$ sep)
{-# INLINE endBy' #-}
