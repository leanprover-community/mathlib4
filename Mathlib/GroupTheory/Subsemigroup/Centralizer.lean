/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Jireh Loreaux
-/
import Mathlib.GroupTheory.Subsemigroup.Center
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

#align_import group_theory.subsemigroup.centralizer from "leanprover-community/mathlib"@"cc67cd75b4e54191e13c2e8d722289a89e67e4fa"

/-!
# Centralizers of magmas and semigroups

## Main definitions

* `Set.centralizer`: the centralizer of a subset of a magma
* `Subsemigroup.centralizer`: the centralizer of a subset of a semigroup
* `Set.addCentralizer`: the centralizer of a subset of an additive magma
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

variable {S}

@[to_additive mem_addCentralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ ∀ m ∈ S, m * c = c * m :=
  Iff.rfl

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| ∀ b ∈ S, b * a = a * b] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff

variable (S)

@[to_additive (attr := simp) zero_mem_addCentralizer]
theorem one_mem_centralizer [MulOneClass M] : (1 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]

@[simp]
theorem zero_mem_centralizer [MulZeroClass M] : (0 : M) ∈ centralizer S := by
  simp [mem_centralizer_iff]

variable {S} {a b : M}

@[to_additive (attr := simp) add_mem_addCentralizer]
theorem mul_mem_centralizer [Semigroup M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S := fun g hg => by
  rw [mul_assoc, ← hb g hg, ← mul_assoc, ha g hg, mul_assoc]

@[to_additive (attr := simp) neg_mem_addCentralizer]
theorem inv_mem_centralizer [Group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S := fun g hg =>
  by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]

@[simp]
theorem add_mem_centralizer [Distrib M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a + b ∈ centralizer S := fun c hc => by rw [add_mul, mul_add, ha c hc, hb c hc]

@[simp]
theorem neg_mem_centralizer [Mul M] [HasDistribNeg M] (ha : a ∈ centralizer S) :
    -a ∈ centralizer S := fun c hc => by rw [mul_neg, ha c hc, neg_mul]

@[simp]
theorem inv_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S :=
  (eq_or_ne a 0).elim
    (fun h => by
      rw [h, inv_zero]
      exact zero_mem_centralizer S)
    fun ha0 c hc => by
    rw [mul_inv_eq_iff_eq_mul₀ ha0, mul_assoc, eq_inv_mul_iff_mul_eq₀ ha0, ha c hc]

@[to_additive (attr := simp) sub_mem_addCentralizer]
theorem div_mem_centralizer [Group M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer hb)

@[simp]
theorem div_mem_centralizer₀ [GroupWithZero M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a / b ∈ centralizer S := by
  rw [div_eq_mul_inv]
  exact mul_mem_centralizer ha (inv_mem_centralizer₀ hb)

@[to_additive addCentralizer_subset]
theorem centralizer_subset [Mul M] (h : S ⊆ T) : centralizer T ⊆ centralizer S := fun _ ht s hs =>
  ht s (h hs)

@[to_additive addCenter_subset_addCentralizer]
theorem center_subset_centralizer [Mul M] (S : Set M) : Set.center M ⊆ S.centralizer :=
  fun _ hx m _ => hx m

@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
theorem centralizer_eq_top_iff_subset {s : Set M} [Mul M] :
    centralizer s = Set.univ ↔ s ⊆ center M :=
  eq_top_iff.trans <| ⟨fun h _ hx _ => (h trivial _ hx).symm, fun h x _ _ hm => (h hm x).symm⟩

variable (M)

@[to_additive (attr := simp) addCentralizer_univ]
theorem centralizer_univ [Mul M] : centralizer univ = center M :=
  Subset.antisymm (fun _ ha b => ha b (Set.mem_univ b)) fun _ ha b _ => ha b

variable {M} (S)

@[to_additive (attr := simp) addCentralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y _ => mul_comm y x

end Set

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
