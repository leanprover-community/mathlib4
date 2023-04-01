/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

/-!
# Missing `MonadLift (StateT α m) (StateT α n)` instance given `MonadLiftT m n`.

Perhaps there is some generalization beyond `StateT` to some class of lawful monad transformers
that I'm missing?
-/

instance [MonadLiftT m n] : MonadLift (StateT α m) (StateT α n) where
  monadLift := fun f s => f s
