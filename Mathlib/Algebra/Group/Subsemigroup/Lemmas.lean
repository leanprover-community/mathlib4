/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Basic
public import Mathlib.Data.Finset.Defs
import Mathlib.Algebra.Group.Subsemigroup.Membership
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.CompleteLattice.Finset

/-!
# Subsemigroup lemmas
-/

public section

variable {M : Type*} [Mul M]

namespace Subsemigroup

@[to_additive]
theorem coe_iSup_eq_iUnion_finset_coe_biSup {ι : Type*} (S : ι → Subsemigroup M) :
    ((⨆ i, S i : Subsemigroup M) : Set M) = ⋃ s : Finset ι, (⨆ i ∈ s, S i : Subsemigroup M) := by
  rw [iSup_eq_iSup_finset, coe_iSup_of_directed <| Monotone.directed_le ?_]
  simp_rw [← Finset.sup_eq_iSup]
  exact fun _ _ ↦ Finset.sup_mono

end Subsemigroup
