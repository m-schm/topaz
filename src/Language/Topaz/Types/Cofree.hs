module Language.Topaz.Types.Cofree
  ( module M
  , Cofree(..), unwrap
  , _unwrap
  ) where

import Relude
import Control.Lens (Lens)
import Control.Comonad as M
import Control.Comonad.Cofree (ComonadCofree(..))
import Text.Show

infixr 5 :<

data Cofree f a = a :< f (Cofree f a)
  deriving (Functor, Foldable, Traversable)

instance Functor f ⇒ Comonad (Cofree f) where
  extract (x :< _) = x
  extend f w@(_ :< xs) = f w :< fmap (extend f) xs
  duplicate w@(_ :< xs) = w :< fmap duplicate xs

instance Functor f ⇒ ComonadCofree f (Cofree f) where
  unwrap (_ :< xs) = xs

instance (Show a, ∀ x. Show x ⇒ Show (f x)) ⇒ Show (Cofree f a) where
  showsPrec p (x :< xs) = showParen (p > 5) $
    showsPrec 6 x . showString " :< " . showsPrec 6 xs

_unwrap ∷ Lens (Cofree f a) (Cofree g a) (f (Cofree f a)) (g (Cofree g a))
_unwrap f (x :< xs) = (x :<) <$> f xs
