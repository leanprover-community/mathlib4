/-
Copyright (c) 2022 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: E.W.Ayers
-/

/-!

# Basic instances and functions for monads and other structures.

-/

instance : Monad id where
  seq := fun f x => f $ x ()
  bind := fun a f => f a
  pure := id
  map := id
