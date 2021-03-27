{-# LANGUAGE CPP #-}
module Language.Topaz.Parser where

import Language.Topaz.Types.AST
import Language.Topaz.Types.Cofree
import Language.Topaz.Types.Lexer (pattern TEquals, Lexeme(..), Token(..))

import Control.Applicative.Combinators.NonEmpty
import Control.Lens hiding ((:<), op)
import qualified Data.Set as S
import Relude hiding (All, many, some)
import Relude.Extra (foldMap1, foldl1', fold1)
import qualified Text.Megaparsec as MP
import Text.Megaparsec hiding (Token, token, some, sepBy1, satisfy)

-- #define DEBUG
#ifdef DEBUG
import Text.Megaparsec.Debug
#else
dbg ∷ String → a → a
dbg _ x = x
{-# INLINE dbg #-}
#endif

type instance TTGIdent 'Parsed = QIdent
type instance TTGLam 'Parsed = NonEmpty (Loc (Arg 'Parsed))
type instance TTGArgs 'Parsed = [Loc (Arg 'Parsed)]
type instance ExprX 'Parsed = Ops (Expr 'Parsed)
type instance PatX 'Parsed = Ops (Pattern 'Parsed)

type Parser = Parsec Void [Lexeme SourcePos]

topLevel ∷ ModulePath → Parser (TopLevel 'Parsed)
topLevel mp = TopLevel mp
  <$> many (decl pub <* many (token TNewline))
  <*> optional (expr AnythingGoes)
  <*  many (token TNewline)
  <*  eof
  where
    pub ∷ Parser (Loc (Scope TopLevel))
    pub = Loc Global <$> token TPub

block ∷ Parser (Loc (Block 'Parsed))
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

decl ∷ Parser (Loc (Scope a)) → Parser (Decl 'Parsed a)
decl pub = import_ <|> let_
  where

    let_ = (pub <|> fmap (Loc Local) (token TLet))
      >>= \h → letVal h <|> letFn h

    letVal (Loc sc beg) = do
      pat ← try $ pattern1 <* lookAhead (token TColon <|> token TEquals)
      mty ← optional $ token TColon *> expr NoEquals
      eq ← token TEquals
      let ty = fromMaybe (eq :< Hole) mty
      b@(Loc _ end) ← block
      pure $ Decl (beg <> end) sc $ DBind pat ty b

    letFn (Loc sc beg) = do
      i ← ident
      as ← many arg
      mret ← optional $ token TColon *> expr NoEquals
      eq ← token TEquals
      let ret = fromMaybe (eq :< Hole) mret
      b@(Loc _ end) ← block
      pure $ Decl (beg <> end) sc $
        DBindFn (IdentBind (FixityPrec Nothing Nothing) i) ret b as

    import_ = do
      (ms, is) ← try $ (,)
        <$> optional (view locSpan <$> pub)
        <*> token TImport
      undefined

arg ∷ Parser (Loc (Arg 'Parsed))
arg = arg' Visible
  <|> (locSpan <>~) <$> token TAt <*> arg' Implicit
  <|> brackets instance_
  where
    arg' t = do
        pat ← pattern1
        let s = extract pat
        pure $ Loc (Arg t pat (s :< Hole)) s
      <|> parens do
        pat ← pattern_
        ty ← option (extract pat :< Hole) $
          token TColon *> expr AnythingGoes
        pure $ Loc (Arg t pat ty) (extract pat <> extract ty)

    instance_ = do
      pat ← pattern_
      ty ← token TColon *> expr AnythingGoes
      pure $ Loc (Arg Instance pat ty) (extract ty)

data ColonBehavior = AnnotsOk | NoAnnots
  deriving Eq

pattern_ ∷ Parser (Pattern 'Parsed)
pattern_ = dbg "pattern_" $ label "pattern" do
  p ← pattern'
  optional (token TColon *> expr AnythingGoes)
    <&> maybe p (onCofree PAnnot p)

pattern' ∷ Parser (Pattern 'Parsed)
pattern' = dbg "pattern'" do
      liftA2 mkCtor qident1 (many pattern1)
  <|> try (liftA2 mkCtor' qident (some pattern1))
  <|> mkTuple
    <$> try (token TParenL *> pattern_ <* lookAhead (token TComma))
    <*> some (token TComma *> pattern_)
    <*  token TParenR
  <|> pattern1
  where
    mkCtor (Loc c s) as = fold1 (s :| fmap extract as) :< PCtor c as
    mkCtor' (Loc c s) as = (s <> extract (last as)) :< PCtor c (toList as)
    mkTuple p ps = (extract p <> extract (last ps)) :< PTup (AtLeastTwo p ps)

pattern1 ∷ Parser (Pattern 'Parsed)
pattern1 = (:< PHole) <$> token THole
       <|> liftC (flip PCtor []) <$> qident1
       <|> liftA2 (\fp li@(Loc _ s) → s :< PVar (IdentBind fp li)) fixityPrec ident
       <|> parens pattern_

fixityPrec ∷ Parser FixityPrec
fixityPrec = pure $ FixityPrec Nothing Nothing

expr ∷ EqualsBehavior → Parser (Expr 'Parsed)
expr eqb = dbg "expr" $ try (opExpr eqb) <|> expr' eqb

expr' ∷ EqualsBehavior → Parser (Expr 'Parsed)
expr' eqb = dbg "expr'" $ when' (eqb /= NoLambda) lam
        <|> app eqb
  where
    lam = do
      (as, mret, s) ← try $ (,,)
        <$> some arg
        <*> optional (token TColon *> expr NoLambda)
        <*> token TArrowR'
      let ret = fromMaybe (s :< Hole) mret
      body@(Loc _ bs) ← block
      pure $ (view locSpan (head as) <> bs)
        :< Lam as ret body

opExpr ∷ EqualsBehavior → Parser (Expr 'Parsed)
opExpr eqb = dbg "opExpr" $
  mkOp
  <$> optional (app eqb)
  <*> some (try $ liftA2 (,) (some op) (app eqb))
  where
    op = satisfy ('o':|"perator") \case
      TOp t → Just t
      _     → Nothing

    mkOp ∷
      Maybe (Expr 'Parsed)
      → NonEmpty (NonEmpty (Loc Text), Expr 'Parsed)
      → Expr 'Parsed
    mkOp ml xs = s :< X (maybe Pfx Ifx ml xs') where
      s = maybe id ((<>) . extract) ml $ foldMap1 (extract . snd) xs
      xs' = foldr (uncurry Binop) Done xs

app ∷ EqualsBehavior → Parser (Expr 'Parsed)
app eqb = foldl1' (onCofree (:$)) <$> some (expr1 eqb) where

expr1 ∷ EqualsBehavior → Parser (Expr 'Parsed)
expr1 eqb = dbg "expr1" $
      (:< Hole) <$> token THole
  <|> var
  <|> liftC id <$> literal
  <|> parens (expr eqb)
  where
    var ∷ Parser (Expr 'Parsed)
    var = liftC Var <$> qident

    literal = satisfy ('l':|"iteral") \case
      TLit l → Just $ Lit l
      _      → Nothing

qident ∷ Parser (Loc QIdent)
qident = qident' $ pathPart `tryEndBy` token TPeriod

qident1 ∷ Parser (Loc QIdent)
qident1 = qident' $ fmap toList $ pathPart `tryEndBy1` token TPeriod

qident' ∷ Parser [Loc Text] → Parser (Loc QIdent)
qident' ppath = do
  path ← ppath
  Loc name end ← ident
  let mp = viaNonEmpty ModulePath $ fmap unLoc path
      beg = path ^? _head . locSpan
  pure $ Loc (QIdent mp name) (maybe id (<>) beg end)

satisfy ∷ NonEmpty Char → (Token → Maybe a) → Parser (Loc a)
satisfy = satisfy' . S.singleton . Label

satisfy' ∷ Set (ErrorItem (Lexeme SourcePos)) → (Token → Maybe a)
  → Parser (Loc a)
satisfy' err cond = MP.token lex err where
  lex (L x t y) = fmap (\a → Loc a (Span x y)) $ cond t

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
pathPart = satisfy ('i':|"dentifier") \case
  TVar v → Just v
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

tryEndBy ∷ Parser a → Parser sep → Parser [a]
tryEndBy p sep = many $ try (p <* sep)
{-# INLINE tryEndBy #-}

tryEndBy1 ∷ Parser a → Parser sep → Parser (NonEmpty a)
tryEndBy1 p sep = some $ try (p <* sep)
{-# INLINE tryEndBy1 #-}

uncurryLoc ∷ (a → Span → c) → Loc a → c
uncurryLoc f = \(Loc x s) → f x s
{-# INLINE uncurryLoc #-}

onCofree ∷ Semigroup a ⇒
  (Cofree f a → Cofree g a → h (Cofree h a))
  → Cofree f a → Cofree g a → Cofree h a
onCofree f = \x@(s :< _) y@(s' :< _) → (s <> s') :< f x y
{-# INLINE onCofree #-}

liftC ∷ (a → f (Cofree f Span)) → Loc a → Cofree f Span
liftC f = \(Loc x s) → s :< f x
{-# INLINE liftC #-}
