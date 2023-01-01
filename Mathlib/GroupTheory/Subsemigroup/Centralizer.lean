/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux

! This file was ported from Lean 3 source module group_theory.subsemigroup.centralizer
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Subsemigroup.Center
import Mathbin.Algebra.GroupWithZero.Units.Lemmas

/-!
# Centralizers of magmas and semigroups

## Main definitions

* `set.centralizer`: the centralizer of a subset of a magma
* `subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `set.add_centralizer`: the centralizer of a subset of an additive magma
* `add_subsemigroup.centralizer`: the centralizer of a subset of an additive semigroup

We provide `monoid.centralizer`, `add_monoid.centralizer`, `subgroup.centralizer`, and
`add_subgroup.centralizer` in other files.
-/


variable {M : Type _} {S T : Set M}

namespace Set

variable (S)

/-- The centralizer of a subset of a magma. -/
@[to_additive add_centralizer " The centralizer of a subset of an additive magma. "]
def centralizer [Mul M] : Set M :=
  { c | ∀ m ∈ S, m * c = c * m }
#align set.centralizer Set.centralizer

variable {S}

@[to_additive mem_add_centralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m :=
  Iff.rfl
#align set.mem_centralizer_iff Set.mem_centralizer_iff

@[to_additive decidable_mem_add_centralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff
#align set.decidable_mem_centralizer Set.decidableMemCentralizer

variable (S)

@[simp, to_additive zero_mem_add_centralizer]
theorem one_mem_centralizer [MulOneClass M] : (1 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.one_mem_centralizer Set.one_mem_centralizer

@[simp]
theorem zero_mem_centralizer [MulZeroClass M] : (0 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]
#align set.zero_mem_centralizer Set.zero_mem_centralizer

variable {S} {a b : M}

@[simp, to_additive add_mem_add_centralizer]
theorem mul_mem_centralizer [Semigroup M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg => by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]
#align set.mul_mem_centralizer Set.mul_mem_centralizer

@[simp, to_additive neg_mem_add_centralizer]
theorem inv_mem_centralizer [Group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S := fun g hg =>
  by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]
#align set.inv_mem_centralizer Set.inv_mem_centralizer

@[simp]
theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]
#align set.add_mem_centralizer Set.add_mem_centralizer

@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ centralizer S) :
    -a ∈ centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]
#align set.neg_mem_centralizer Set.neg_mem_centralizer

@[simp]
theorem inv_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer S)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]
#align set.inv_mem_centralizer₀ Set.inv_mem_centralizer₀

@[simp, to_additive sub_mem_add_centralizer]
theorem div_mem_centralizer [Group M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer hb)
#align set.div_mem_centralizer Set.div_mem_centralizer

@[simp]
theorem div_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)
#align set.div_mem_centralizer₀ Set.div_mem_centralizer₀

@[to_additive add_centralizer_subset]
theorem centralizer_subset [Mul M] (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun t ht s hs =>
  ht s (h hs)
#align set.centralizer_subset Set.centralizer_subset

variable (M)

@[simp, to_additive add_centralizer_univ]
theorem centralizer_univ [Mul M] : centralizer univ = center M :=
  Subset.antisymm (fun a ha b => ha b (Set.mem_univ b)) fun a ha b hb => ha b
#align set.centralizer_univ Set.centralizer_univ

variable {M} (S)

@[simp, to_additive add_centralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  (Subset.antisymm (subset_univ _)) fun x hx y hy => mul_comm y x
#align set.centralizer_eq_univ Set.centralizer_eq_univ

end Set

namespace Subsemigroup

section

variable {M} [Semigroup M] (S)

/-- The centralizer of a subset of a semigroup `M`. -/
@[to_additive "The centralizer of a subset of an additive semigroup."]
def centralizer : Subsemigroup M where
  carrier := S.centralizer
  mul_mem' a b := Set.mul_mem_centralizer
#align subsemigroup.centralizer Subsemigroup.centralizer

@[simp, norm_cast, to_additive]
theorem coe_centralizer : ↑(centralizer S) = S.centralizer :=
  rfl
#align subsemigroup.coe_centralizer Subsemigroup.coe_centralizer

variable {S}

@[to_additive]
theorem mem_centralizer_iff {z : M} : z ∈ centralizer S ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align subsemigroup.mem_centralizer_iff Subsemigroup.mem_centralizer_iff

@[to_additive]
instance decidableMemCentralizer (a) [Decidable <| ∀ b ∈ S, b * a = a * b] :
    Decidable (a ∈ centralizer S) :=
  decidable_of_iff' _ mem_centralizer_iff
#align subsemigroup.decidable_mem_centralizer Subsemigroup.decidableMemCentralizer

@[to_additive]
theorem centralizer_le (h : S ⊆ T) : centralizer T ≤ centralizer S :=
  Set.centralizer_subset h
#align subsemigroup.centralizer_le Subsemigroup.centralizer_le

variable (M)

@[simp, to_additive]
theorem centralizer_univ : centralizer Set.univ = center M :=
  SetLike.ext' (Set.centralizer_univ M)
#align subsemigroup.centralizer_univ Subsemigroup.centralizer_univ

end

end Subsemigroup

-- Guard against import creep
assert_not_exists finset

