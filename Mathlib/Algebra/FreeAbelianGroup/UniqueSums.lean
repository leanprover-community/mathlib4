/-
Copyright (c) 2025 Yaël Dillies, Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Paul Lezeau
-/
module

public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.UniqueProds.Basic

/-!
# Free abelian groups have unique sums
-/

@[expose] public section

assert_not_exists Cardinal StarModule

instance {σ : Type*} : TwoUniqueSums (FreeAbelianGroup σ) :=
  (FreeAbelianGroup.equivFinsupp σ).twoUniqueSums_iff.mpr inferInstance
