/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.GroupTheory.Subsemigroup.Center
import Mathlib.Algebra.Group.Center

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

@[to_additive (attr := simp, norm_cast)]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl

@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff

@[to_additive]
theorem center_le_centralizer (S) : center M ≤ centralizer S :=
  S.center_subset_centralizer

@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s ⊆ center M :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

variable (M)
@[to_additive (attr := simp)]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)

end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
