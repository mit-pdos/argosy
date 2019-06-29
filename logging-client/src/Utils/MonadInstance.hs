{-# OPTIONS_GHC -fno-warn-orphans #-}
module Utils.MonadInstance where

import           Proc                    hiding ( unsafeCoerce )
import           Unsafe.Coerce

instance Functor (Coq_proc op) where
  fmap f p = coq_Bind (unsafeCoerce p) (Ret . f . unsafeCoerce)

instance Applicative (Coq_proc op) where
  pure = Ret
  af <*> x = coq_Bind (unsafeCoerce af) (\f -> unsafeCoerce f x)

instance Monad (Coq_proc op) where
  x >>= f = coq_Bind (unsafeCoerce x) (f . unsafeCoerce)
