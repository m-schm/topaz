module Language.Topaz.Utils where

import Relude
import Control.Lens

infixr 8 .:
(.:) ∷ (c → d) → (a → b → c) → a → b → d
f .: g = \x y → f (g x y)
{-# INLINE (.:) #-}

ifirstOf ∷ IndexedGetting i (First (i, a)) s a → s → Maybe (i, a)
ifirstOf l = getFirst . ifoldMapOf l (pure .: (,))
{-# INLINE ifirstOf #-}

length' ∷ [a] → Word
length' = go 0 where
  go !n []     = n
  go !n (_:xs) = go (n+1) xs
{-# INLINE length' #-}
