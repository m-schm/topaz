module Language.Topaz.Types.Indexed where
import Relude
import Control.Lens (Lens, Lens')

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

_iextract ∷ Lens' (ICofree a f i) a
_iextract f (x :@< xs) = (:@< xs) <$> f x

_iunwrap ∷
  Lens (ICofree a f i) (ICofree a g i) (f (ICofree a f) i) (g (ICofree a g) i)
_iunwrap f (x :@< xs) = (x :@<) <$> f xs
{-# INLINE _iunwrap #-}
