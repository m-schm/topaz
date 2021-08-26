module Language.Topaz.Types.Indexed where
import Relude

type IFix ∷ ((k → Type) → k → Type) → k → Type
newtype IFix f i = IFix (f (IFix f) i)

type ICofree ∷ Type → ((k → Type) → k → Type) → k → Type
data ICofree a f i = a :@< f (ICofree a f) i

iextract ∷ ICofree a f i → a
iextract (a :@< _) = a

iunwrap ∷ ICofree a f i → f (ICofree a f) i
iunwrap (_ :@< xs) = xs

deriving instance
  ( Show a
  , ∀ r j. (∀ k. Show (r k)) ⇒ Show (f r j)
  ) ⇒ Show (ICofree a f i)
