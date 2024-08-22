/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.ENat.Basic
/-!
# Bundled ordered algebra instance for `ℕ∞`

-/

deriving instance CanonicallyOrderedCommSemiring,
  CanonicallyLinearOrderedAddCommMonoid, LinearOrderedAddCommMonoidWithTop for ENat
