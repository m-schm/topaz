module Language.Topaz.Types.Cofree
  ( module M
  , Cofree(..), unwrap
  , _unwrap
  ) where

import Relude
import Control.Lens (Lens)
import Control.Comonad as M
import Control.Comonad.Cofree (ComonadCofree(..))

infixr 5 :<

data Cofree f a = a :< f (Cofree f a)
  deriving (Functor, Foldable, Traversable)

instance Functor f ⇒ Comonad (Cofree f) where
  extract (x :< _) = x
  {-# INLINE extract #-}
  extend f w@(_ :< xs) = f w :< fmap (extend f) xs
  {-# INLINE extend #-}
  duplicate w@(_ :< xs) = w :< fmap duplicate xs
  {-# INLINE duplicate #-}

instance Functor f ⇒ ComonadCofree f (Cofree f) where
  unwrap (_ :< xs) = xs
  {-# INLINE unwrap #-}

deriving instance (Show a, ∀ x. Show x ⇒ Show (f x)) ⇒ Show (Cofree f a)

_unwrap ∷ Lens (Cofree f a) (Cofree g a) (f (Cofree f a)) (g (Cofree g a))
_unwrap f (x :< xs) = (x :<) <$> f xs
{-# INLINE _unwrap #-}
