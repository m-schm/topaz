module Language.Topaz.Eval where
import Relude

import Language.Topaz.Types.Value
import Language.Topaz.Types.AST
import Language.Topaz.Types.Cofree

eval ∷ Env → Expr 'Checked → Value
eval env (_ :< e) = case e of
  Lit l → undefined
  cets :$ cets3 → undefined
  cets :$@ cets3 → undefined
  Lam tt cets lbt → undefined
  Pi tt cets lbt → undefined
  Tuple l_cets → undefined
  TupleT l_p_cptscets → undefined
  Row mip_icets → undefined
  Var tt → undefined
  Rec → undefined
  Hole → undefined
  Match cets l_p_cptslbt → undefined
  X et → undefined
