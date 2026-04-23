/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Data.NNRat.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.Nonneg.Ring
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive

/-!
# Bundled ordered algebra structures on `ℚ≥0`

-/

@[expose] public section

instance : IsStrictOrderedRing ℚ≥0 := Nonneg.isStrictOrderedRing

-- TODO: `deriving instance OrderedSub for NNRat` doesn't work yet, so we add the instance manually
instance NNRat.instOrderedSub : OrderedSub ℚ≥0 := Nonneg.orderedSub
instance NNRat.instCanonicallyOrderedAdd : CanonicallyOrderedAdd ℚ≥0 := Nonneg.canonicallyOrderedAdd
