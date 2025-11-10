/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.NNRat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Nonneg.Ring

/-!
# Bundled ordered algebra structures on `ℚ≥0`

-/

instance : IsStrictOrderedRing ℚ≥0 := Nonneg.isStrictOrderedRing

-- TODO: `deriving instance OrderedSub for NNRat` doesn't work yet, so we add the instance manually
instance NNRat.instOrderedSub : OrderedSub ℚ≥0 := Nonneg.orderedSub
instance NNRat.instCanonicallyOrderedAdd : CanonicallyOrderedAdd ℚ≥0 := Nonneg.canonicallyOrderedAdd
