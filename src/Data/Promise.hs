{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}

-- | Lazy promises

module Data.Promise
  ( Lazy, runLazy, runLazy_
  , Promise(..)
  , promise, promise_
  , (!=)
  , demand
  , BrokenPromise(..)
  ) where

import Control.Applicative
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad (ap)
import Control.Monad.Fix
import Control.Monad.ST.Class
import Control.Monad.ST.Unsafe
import Data.Typeable
import System.IO.Unsafe
import Unsafe.Coerce

data BrokenPromise = BrokenPromise deriving (Show, Typeable)
instance Exception BrokenPromise

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

--------------------------------------------------------------------------------
-- * Demand driven computations
--------------------------------------------------------------------------------

newtype Lazy s a = Lazy { getLazy :: forall x. MVar (Maybe (IO (K s x))) -> IO (K s a) }

type role Lazy nominal representational

instance Functor (Lazy s) where
  fmap f (Lazy m) = Lazy $ \mv -> fmap go (m mv) where
    go (Pure a)        = Pure (f a)
    go (Fulfilled v k) = Fulfilled v (fmap (fmap f) k)

instance Applicative (Lazy s) where
  pure = return
  (<*>) = ap

instance Monad (Lazy s) where
  return a = Lazy $ \_ -> return $ Pure a
  m >>= f = Lazy $ \mv -> let
      go (Pure a) = getLazy (f a) mv
      go (Fulfilled v k) = return $ Fulfilled v (k >>= go)
    in getLazy m mv >>= go

instance MonadST (Lazy s) where
  type World (Lazy s) = s
  liftST m = Lazy $ \_ -> Pure <$> unsafeSTToIO m

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

-- | Demand the result of an I-Var
demand :: Promise s a -> a
demand (Promise _ a) = a

-- | Promise that by the end of the computation we'll provide a "real" answer, or we'll fall back and give you this answer
promise :: a -> Lazy s (Promise s a)
promise d = Lazy $ \mv -> do
  v <- newEmptyMVar
  return $ Pure $ Promise v (drive d mv v)

-- | Promise that by the end of the computation we'll provide a "real" answer, or you'll get an error.
promise_ :: Lazy s (Promise s a)
promise_ = promise $ throw BrokenPromise

infixl 0 !=

-- | Fulfill a promise.
(!=) :: Promise s a -> a -> Lazy s ()
Promise v _ != a = Lazy $ \ _ -> do
  putMVar v a
  return $ Fulfilled v $ return (Pure ())

--------------------------------------------------------------------------------
-- * Running It All
--------------------------------------------------------------------------------

runLazy :: (forall s. Promise s a -> Lazy s b) -> a -> a
runLazy f d = unsafePerformIO $ do
  mv <- newEmptyMVar
  v <- newEmptyMVar
  let iv = Promise v (drive d mv v)
  putMVar mv (Just (getLazy (f iv) mv))
  return $ demand iv
{-# NOINLINE runLazy #-}

runLazy_ :: (forall s. Promise s a -> Lazy s b) -> a
runLazy_ k = runLazy k $ throw BrokenPromise
