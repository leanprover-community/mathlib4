/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Subsemigroup.Centralizer
import Mathlib.GroupTheory.Submonoid.Center

#align_import group_theory.submonoid.centralizer from "leanprover-community/mathlib"@"cc67cd75b4e54191e13c2e8d722289a89e67e4fa"

/-!
# Centralizers of magmas and monoids

## Main definitions

* `Submonoid.centralizer`: the centralizer of a subset of a monoid
* `AddSubmonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `Subgroup.centralizer`, `AddSubgroup.centralizer` in other files.
-/


variable {M : Type*} {S T : Set M}

namespace Submonoid

section

variable [Monoid M] (S)

/-- The centralizer of a subset of a monoid `M`. -/
@[to_additive "The centralizer of a subset of an additive monoid."]
def centralizer : Submonoid M where
  carrier := S.centralizer
  one_mem' := S.one_mem_centralizer
  mul_mem' := Set.mul_mem_centralizer
#align submonoid.centralizer Submonoid.centralizer
#align add_submonoid.centralizer AddSubmonoid.centralizer

@[to_additive (attr := simp, norm_cast)]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl
#align submonoid.coe_centralizer Submonoid.coe_centralizer
#align add_submonoid.coe_centralizer AddSubmonoid.coe_centralizer

theorem centralizer_toSubsemigroup : (centralizer S).toSubsemigroup = Subsemigroup.centralizer S :=
  rfl
#align submonoid.centralizer_to_subsemigroup Submonoid.centralizer_toSubsemigroup

theorem _root_.AddSubmonoid.centralizer_toAddSubsemigroup {M} [AddMonoid M] (S : Set M) :
    (AddSubmonoid.centralizer S).toAddSubsemigroup = AddSubsemigroup.centralizer S :=
  rfl
#align add_submonoid.centralizer_to_add_subsemigroup AddSubmonoid.centralizer_toAddSubsemigroup

attribute [to_additive existing AddSubmonoid.centralizer_toAddSubsemigroup]
  Submonoid.centralizer_toSubsemigroup

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align submonoid.mem_centralizer_iff Submonoid.mem_centralizer_iff
#align add_submonoid.mem_centralizer_iff AddSubmonoid.mem_centralizer_iff

@[to_additive]
theorem center_le_centralizer (s) : center M ≤ centralizer s :=
  s.center_subset_centralizer
#align submonoid.center_le_centralizer Submonoid.center_le_centralizer
#align add_submonoid.center_le_centralizer AddSubmonoid.center_le_centralizer

@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff
#align submonoid.decidable_mem_centralizer Submonoid.decidableMemCentralizer
#align add_submonoid.decidable_mem_centralizer AddSubmonoid.decidableMemCentralizer

@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h
#align submonoid.centralizer_le Submonoid.centralizer_le
#align add_submonoid.centralizer_le AddSubmonoid.centralizer_le

@[to_additive (attr := simp)]
theorem centralizer_eq_top_iff_subset {s : Set M} : centralizer s = ⊤ ↔ s ⊆ center M :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset
#align submonoid.centralizer_eq_top_iff_subset Submonoid.centralizer_eq_top_iff_subset
#align add_submonoid.centralizer_eq_top_iff_subset AddSubmonoid.centralizer_eq_top_iff_subset

variable (M)

@[to_additive (attr := simp)]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)
#align submonoid.centralizer_univ Submonoid.centralizer_univ
#align add_submonoid.centralizer_univ AddSubmonoid.centralizer_univ

@[to_additive]
lemma le_centralizer_centralizer {s : Submonoid M} : s ≤ centralizer (centralizer (s : Set M)) :=
  Set.subset_centralizer_centralizer

@[to_additive (attr := simp)]
lemma centralizer_centralizer_centralizer {s : Set M} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

end

end Submonoid

-- Guard against import creep
assert_not_exists Finset
