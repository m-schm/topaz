module Language.Topaz.Types.Result where

import Relude

data Result e a = Ok a | Err (NonEmpty e)
  deriving (Functor, Foldable, Traversable)

instance Applicative (Result e) where
  pure = Ok
  Ok f  <*> Ok x   = Ok $ f x
  Err e <*> Ok _   = Err e
  Ok _  <*> Err e  = Err e
  Err e <*> Err e' = Err $ e <> e'

instance Monad (Result e) where
  return = pure
  Err e >>= _ = Err e
  Ok  x >>= f = f x
  (>>) = (*>)
