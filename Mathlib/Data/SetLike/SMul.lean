
/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.Algebra.Group.Operations
import Mathlib.Data.SetLike.Basic

/-!
# Typeclass for scalar multiplication of set-like objects

-/

variable (R A : Type*) [SMul R A] (S : Type*) [SetLike S R] (s : S)

@[to_additive]
instance : SMul s A where
  smul r a := (r : R) • a
