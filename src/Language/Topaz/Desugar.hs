module Language.Topaz.Desugar (desugar) where
import Relude
import Language.Topaz.Types.AST

desugar ∷ TopLevel 'Parse → TopLevel 'Desugared
desugar = _
