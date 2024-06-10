/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.GroupTheory.Subsemigroup.Center
import Mathlib.Algebra.Group.Centralizer

#align_import group_theory.subsemigroup.centralizer from "leanprover-community/mathlib"@"cc67cd75b4e54191e13c2e8d722289a89e67e4fa"

/-!
# Centralizers in semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/


variable {M : Type*} {S T : Set M}
namespace Subsemigroup

section

variable [Semigroup M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive "The centralizer of a subset of an additive semigroup."]
def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' := Set.mul_mem_centralizer
#align subsemigroup.centralizer Subsemigroup.centralizer
#align add_subsemigroup.centralizer AddSubsemigroup.centralizer

@[to_additive (attr := simp, norm_cast)]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl
#align subsemigroup.coe_centralizer Subsemigroup.coe_centralizer
#align add_subsemigroup.coe_centralizer AddSubsemigroup.coe_centralizer

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align subsemigroup.mem_centralizer_iff Subsemigroup.mem_centralizer_iff
#align add_subsemigroup.mem_centralizer_iff AddSubsemigroup.mem_centralizer_iff

@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff
#align subsemigroup.decidable_mem_centralizer Subsemigroup.decidableMemCentralizer
#align add_subsemigroup.decidable_mem_centralizer AddSubsemigroup.decidableMemCentralizer

@[to_additive]
theorem center_le_centralizer (S) : center M ≤ centralizer S :=
  S.center_subset_centralizer
#align subsemigroup.center_le_centralizer Subsemigroup.center_le_centralizer
#align add_subsemigroup.center_le_centralizer AddSubsemigroup.center_le_centralizer

@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h
#align subsemigroup.centralizer_le Subsemigroup.centralizer_le
#align add_subsemigroup.centralizer_le AddSubsemigroup.centralizer_le

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s ⊆ center M :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align subsemigroup.centralizer_eq_top_iff_subset Subsemigroup.centralizer_eq_top_iff_subset
#align add_subsemigroup.centralizer_eq_top_iff_subset AddSubsemigroup.centralizer_eq_top_iff_subset

variable (M)
@[to_additive (attr := simp)]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)
#align subsemigroup.centralizer_univ Subsemigroup.centralizer_univ
#align add_subsemigroup.centralizer_univ AddSubsemigroup.centralizer_univ

end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
