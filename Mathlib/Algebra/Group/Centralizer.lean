/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.Algebra.Group.Center

#align_import group_theory.subsemigroup.centralizer from "leanprover-community/mathlib"@"cc67cd75b4e54191e13c2e8d722289a89e67e4fa"

/-!
# Centralizers of magmas and semigroups

## Main definitions

* `Set.centralizer`: the centralizer of a subset of a magma
* `Set.addCentralizer`: the centralizer of a subset of an additive magma

See `Mathlib.GroupTheory.Subsemigroup.Centralizer` for the definition of the centralizer
as a subsemigroup:
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `AddSubsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `Monoid.centralizer`, `AddMonoid.centralizer`, `Subgroup.centralizer`, and
`AddSubgroup.centralizer` in other files.
-/


variable {M : Type*} {S T : Set M}

namespace Set

variable (S)

/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer " The centralizer of a subset of an additive magma. "]
def centralizer [Mul M] : Set M :=
  { c | ∀ m ∈ S, m * c = c * m }
#align set.centralizer Set.centralizer
#align set.add_centralizer Set.addCentralizer

variable {S}

@[to_additive mem_addCentralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m :=
  Iff.rfl
#align set.mem_centralizer_iff Set.mem_centralizer_iff
#align set.mem_add_centralizer Set.mem_addCentralizer

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff
#align set.decidable_mem_centralizer Set.decidableMemCentralizer
#align set.decidable_mem_add_centralizer Set.decidableMemAddCentralizer

variable (S)

@[to_additive (attr := simp) zero_mem_addCentralizer]
theorem one_mem_centralizer [MulOneClass M] : (1 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.one_mem_centralizer Set.one_mem_centralizer
#align set.zero_mem_add_centralizer Set.zero_mem_addCentralizer

@[simp]
theorem zero_mem_centralizer [MulZeroClass M] : (0 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.zero_mem_centralizer Set.zero_mem_centralizer

variable {S} {a b : M}

@[to_additive (attr := simp) add_mem_addCentralizer]
theorem mul_mem_centralizer [Semigroup M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg => by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]
#align set.mul_mem_centralizer Set.mul_mem_centralizer
#align set.add_mem_add_centralizer Set.add_mem_addCentralizer

@[to_additive (attr := simp) neg_mem_addCentralizer]
theorem inv_mem_centralizer [Group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  fun g hg => by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]
#align set.inv_mem_centralizer Set.inv_mem_centralizer
#align set.neg_mem_add_centralizer Set.neg_mem_addCentralizer

@[simp]
theorem inv_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer S)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]
#align set.inv_mem_centralizer₀ Set.inv_mem_centralizer₀

@[to_additive (attr := simp) sub_mem_addCentralizer]
theorem div_mem_centralizer [Group M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer hb)
#align set.div_mem_centralizer Set.div_mem_centralizer
#align set.sub_mem_add_centralizer Set.sub_mem_addCentralizer

@[simp]
theorem div_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)
#align set.div_mem_centralizer₀ Set.div_mem_centralizer₀

@[to_additive addCentralizer_subset]
theorem centralizer_subset [Mul M] (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun _ ht s hs =>
  ht s (h hs)
#align set.centralizer_subset Set.centralizer_subset
#align set.add_centralizer_subset Set.addCentralizer_subset

@[to_additive addCenter_subset_addCentralizer]
theorem center_subset_centralizer [Mul M] (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ => (hx.comm m).symm
#align set.center_subset_centralizer Set.center_subset_centralizer
#align set.add_center_subset_add_centralizer Set.addCenter_subset_addCentralizer

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
theorem centralizer_eq_top_iff_subset {s : Set M} [Semigroup M] :
    centralizer s = Set.univ ↔ s ⊆ center M :=
  eq_top_iff.trans <| ⟨
    fun h _ hx => Semigroup.mem_center_iff.mpr fun _ => by rw [h trivial _ hx],
    fun h _ _ _ hm => (h hm).comm _⟩
#align set.centralizer_eq_top_iff_subset Set.centralizer_eq_top_iff_subset
#align set.add_centralizer_eq_top_iff_subset Set.addCentralizer_eq_top_iff_subset

variable (M)

@[to_additive (attr := simp) addCentralizer_univ]
theorem centralizer_univ [Semigroup M] : centralizer univ = center M :=
  Subset.antisymm (fun _ ha => Semigroup.mem_center_iff.mpr fun b => ha b (Set.mem_univ b))
  fun _ ha b _ => (ha.comm b).symm
#align set.centralizer_univ Set.centralizer_univ
#align set.add_centralizer_univ Set.addCentralizer_univ

variable {M} (S)

@[to_additive (attr := simp) addCentralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y _ => mul_comm y x
#align set.centralizer_eq_univ Set.centralizer_eq_univ
#align set.add_centralizer_eq_univ Set.addCentralizer_eq_univ

end Set

-- Guard against import creep
assert_not_exists Finset
assert_not_exists Distrib
