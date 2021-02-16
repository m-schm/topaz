module Main where
import Relude

import qualified Data.ByteString as BS
import Text.Megaparsec (runParser, errorBundlePretty)

import Language.Topaz.Lexer (lex)
import Language.Topaz.Parser (topLevel)
import Language.Topaz.Types.AST (ModulePath(Main))

main ∷ IO ()
main = do
  let file = "test.tp"
  let mp = Main
  bs ← BS.readFile file
  case decodeUtf8' bs of
    Left ue → print ue
    Right t → case runParser (lex mp) file t of
      Left peb → putStr $ errorBundlePretty peb
      Right toks → case runParser topLevel file toks of
        Left peb → print peb
        Right ast → print ast
