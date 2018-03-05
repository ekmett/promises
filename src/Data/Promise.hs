{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
#if MIN_VERSION_base(4,7,0)
{-# LANGUAGE RoleAnnotations #-}
#endif
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE Trustworthy #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Lazy demand-driven promises.
--
-----------------------------------------------------------------------------

module Data.Promise
  ( Lazy
  , runLazy
  , runLazy_
  , runLazyIO
  , runLazyIO_
  , Promise(..)
  , promise, promise_
  , (!=)
  , demand
  , BrokenPromise(..)
  ) where

#if __GLASGOW_HASKELL__ < 710
import Control.Applicative
#endif
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad (ap)
import Control.Monad.Fix
import Control.Monad.Primitive
import Control.Monad.ST.Unsafe
import Data.Typeable
import System.IO.Unsafe
import Unsafe.Coerce

-- | Thrown when the answer for an unfulfillable promise is demanded.
data BrokenPromise = BrokenPromise deriving (Show, Typeable)
instance Exception BrokenPromise

--------------------------------------------------------------------------------
-- * Demand driven computations
--------------------------------------------------------------------------------

-- | A lazy, demand-driven calculation that can create and fulfill promises.
newtype Lazy s a = Lazy { getLazy :: forall x. MVar (Maybe (IO (K s x))) -> IO (K s a) }
  deriving Typeable

#if MIN_VERSION_base(4,7,0)
type role Lazy nominal representational
#endif

instance Functor (Lazy s) where
  fmap f (Lazy m) = Lazy $ \mv -> fmap go (m mv) where
    go (Pure a)        = Pure (f a)
    go (Fulfilled v k) = Fulfilled v (fmap (fmap f) k)

instance Applicative (Lazy s) where
  pure a = Lazy $ \_ -> return $ Pure a
  (<*>) = ap

instance Monad (Lazy s) where
  return = pure
  m >>= f = Lazy $ \mv -> let
      go (Pure a) = getLazy (f a) mv
      go (Fulfilled v k) = return $ Fulfilled v (k >>= go)
    in getLazy m mv >>= go

instance PrimMonad (Lazy s) where
  type PrimState (Lazy s) = s
  primitive m = Lazy $ \_ -> Pure <$> unsafeSTToIO (primitive m)

instance MonadFix (Lazy s) where
  mfix f = do
    a <- promise_
    r <- f (demand a)
    a != r
    return r

--------------------------------------------------------------------------------
-- * Promises, Promises
--------------------------------------------------------------------------------

-- | A lazy I-Var.
data Promise s a where
  Promise :: MVar a -> a -> Promise s a
  deriving Typeable

-- | Demand the result of a promise.
demand :: Promise s a -> a
demand (Promise _ a) = a

-- | Promise that by the end of the computation we'll provide a "real" answer, or we'll fall back and give you this answer
promise :: a -> Lazy s (Promise s a)
promise d = Lazy $ \mv -> do
  v <- newEmptyMVar
  return $ Pure $ Promise v (drive d mv v)

-- | Create an empty promise. If you observe the demanded answer of this promise then either by the end of the current lazy
-- computation we'll provide a "real" answer, or you'll get an error.
--
-- @
-- 'promise_' ≡ 'promise' ('throw' 'BrokenPromise')
-- @
promise_ :: Lazy s (Promise s a)
promise_ = promise $ throw BrokenPromise

infixl 0 !=

-- | Fulfill a promise. Each promise should only be fulfilled once.
--
-- >>> runLazy_ $ \p -> p != "good"
-- "good"
--
-- >>> runLazy_ $ \p -> do q <- promise_; p != "yay! " ++ demand q; q != "it works."
-- "yay! it works."
--
-- >>> runLazy_ $ \p -> return ()
-- *** Exception: BrokenPromise
--
-- >>> runLazy (\p -> return ()) "default"
-- "default"
--
(!=) :: Promise s a -> a -> Lazy s ()
Promise v _ != a = Lazy $ \ _ -> do
  putMVar v a
  return $ Fulfilled v $ return (Pure ())

--------------------------------------------------------------------------------
-- * Running It All
--------------------------------------------------------------------------------

runLazyIO :: (forall s. Promise s a -> Lazy s b) -> a -> IO a
runLazyIO f d = do
  mv <- newEmptyMVar
  v <- newEmptyMVar
  let iv = Promise v (drive d mv v)
  putMVar mv (Just (getLazy (f iv) mv))
  return $ demand iv

runLazyIO_ :: (forall s. Promise s a -> Lazy s b) -> IO a
runLazyIO_ k = runLazyIO k $ throw BrokenPromise

-- | Run a lazy computation. The final answer is given in the form of a promise to be fulfilled.
-- If the promise is unfulfilled then a user supplied default value will be returned.
runLazy :: (forall s. Promise s a -> Lazy s b) -> a -> a
runLazy f d = unsafePerformIO (runLazyIO f d)
{-# NOINLINE runLazy #-}

-- | Run a lazy computation. The final answer is given in the form of a promise to be fulfilled.
-- If the promise is unfulfilled then a 'BrokenPromise' will be thrown.
--
-- @
-- 'runLazy_' k ≡ 'runLazy' k ('throw' 'BrokenPromise')
-- @
runLazy_ :: (forall s. Promise s a -> Lazy s b) -> a
runLazy_ k = runLazy k $ throw BrokenPromise

--------------------------------------------------------------------------------
-- * Internals
--------------------------------------------------------------------------------

meq :: MVar a -> MVar b -> Bool
meq a b = a == unsafeCoerce b

data K s a where
  Pure      :: a -> K s a
  Fulfilled :: MVar x -> IO (K s a) -> K s a

instance Functor (K s) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Fulfilled m k) = Fulfilled m (fmap (fmap f) k)

pump :: a -> IO (K s x) -> MVar a -> IO (Maybe (IO (K s x)))
pump d m v = m >>= \case
  Pure _ -> return Nothing
  Fulfilled u n
    | meq u v   -> return (Just n)
    | otherwise -> pump d n v

drive :: a -> MVar (Maybe (IO (K s x))) -> MVar a -> a
drive d mv v = unsafePerformIO $ tryTakeMVar v >>= \case
  Just a -> return a -- if we're satisfied give the answer
  Nothing -> takeMVar mv >>= \case -- grab the lock on this computation
    Nothing -> do -- it has nothing left to do, so we fail to the default answer
      putMVar mv Nothing
      return d
    Just k -> tryTakeMVar v >>= \case -- ok, check to make sure we haven't been satisfied in the meantime
      Just a -> do
        putMVar mv (Just k) -- if so, restore the continuation, and return the answer
        return a
      Nothing -> do
        mk <- pump d k v
        putMVar mv mk
        case mk of
          Nothing -> return d
          Just _  -> takeMVar v
{-# NOINLINE drive #-}
