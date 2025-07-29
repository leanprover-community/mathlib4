/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.GroupTheory.Subsemigroup.Centralizer
import Mathlib.GroupTheory.Submonoid.Center

/-!
# Centralizers of magmas and monoids

## Main definitions

* `Submonoid.centralizer`: the centralizer of a subset of a monoid
* `AddSubmonoid.centralizer`: the centralizer of a subset of an additive monoid

We provide `Subgroup.centralizer`, `AddSubgroup.centralizer` in other files.
-/

-- Guard against import creep
assert_not_exists Finset

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

@[to_additive (attr := simp, norm_cast)]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl

@[to_additive AddSubmonoid.centralizer_toAddSubsemigroup]
theorem centralizer_toSubsemigroup : (centralizer S).toSubsemigroup = Subsemigroup.centralizer S :=
  rfl

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl

@[to_additive]
theorem center_le_centralizer (s) : center M ≤ centralizer s :=
  s.center_subset_centralizer

@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff

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

@[to_additive]
lemma le_centralizer_centralizer {s : Submonoid M} : s ≤ centralizer (centralizer (s : Set M)) :=
  Set.subset_centralizer_centralizer

@[to_additive (attr := simp)]
lemma centralizer_centralizer_centralizer {s : Set M} :
    centralizer s.centralizer.centralizer = centralizer s := by
  apply SetLike.coe_injective
  simp only [coe_centralizer, Set.centralizer_centralizer_centralizer]

variable {M} in
@[to_additive]
lemma closure_le_centralizer_centralizer (s : Set M) :
    closure s ≤ centralizer (centralizer s) :=
  closure_le.mpr Set.subset_centralizer_centralizer

/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive
      "If all the elements of a set `s` commute, then `closure s` forms an additive
      commutative monoid."]
abbrev closureCommMonoidOfComm {s : Set M} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommMonoid (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun ⟨_, h₁⟩ ⟨_, h₂⟩ ↦
      have := closure_le_centralizer_centralizer s
      Subtype.ext <| Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂) }

end

end Submonoid
