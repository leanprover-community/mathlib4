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

structure IsAddCentralizer [Add M] (z : M) : Prop where
  comm (a : S) : z + a = a + z
  lmulc_mul_lmuls_lmul_lmul (a : S) (b : M) : z + (a + b) = (z + a) + b -- L_zL_a = L_{za}
  lmuls_mul_lmulc_lmul_rmul (a : S) (b : M) : a + (z + b) = (a + z) + b -- L_aL_z = L_{az}
  rmuls_mul_rmulc_rmul_rmul (a : S) (b : M) : (b + z) + a = b + (a + z) -- R_aR_z = R_{az}
  rmulc_mul_rmuls_rmul_lmul (a : S) (b : M) : (b + a) + z = b + (z + a) -- R_zR_a = R_{za}
  rmulc_comm_lmuls (a : S) (b : M) : (a + b) + z = a + (b + z) -- R_zL_a = L_aR_z
  lmulc_comm_rmuls (a : S) (b : M) : z + (b + a) = (z + b) + a -- L_zR_a = R_aL_z

-- lmulc - left multiplication by an element of the centralizer of the set
-- lmuls - left multiplication by an element of the set
@[to_additive]
structure IsMulCentralizer [Mul M] (z : M) : Prop where
  comm (a : S) : z * a = a * z
  lmulc_mul_lmuls_lmul_lmul (a : S) (b : M) : z * (a * b) = (z * a) * b -- L_zL_a = L_{za}
  lmuls_mul_lmulc_lmul_rmul (a : S) (b : M) : a * (z * b) = (a * z) * b -- L_aL_z = L_{az}
  rmuls_mul_rmulc_rmul_rmul (a : S) (b : M) : (b * z) * a = b * (a * z) -- R_aR_z = R_{az}
  rmulc_mul_rmuls_rmul_lmul (a : S) (b : M) : (b * a) * z = b * (z * a) -- R_zR_a = R_{za}
  rmulc_comm_lmuls (a : S) (b : M) : (a * b) * z = a * (b * z) -- R_zL_a = L_aR_z
  lmulc_comm_rmuls (a : S) (b : M) : z * (b * a) = (z * b) * a -- L_zR_a = R_aL_z

-- L_zL_a = L_aL_z
lemma lmulc_comm_lmuls [Mul M] {z : M} {a : S} {b : M} (h : IsMulCentralizer S z) :
  z * (a * b) = a * (z * b) := by
  rw [h.lmulc_mul_lmuls_lmul_lmul, h.comm, h.lmuls_mul_lmulc_lmul_rmul]

-- R_zR_a = R_aR_z
lemma rmulc_comm_rmuls [Mul M] (z : M) (a : S) (b : M) (h : IsMulCentralizer S z) :
  (b * a) * z = (b * z) * a := by
  rw [h.rmulc_mul_rmuls_rmul_lmul, h.comm, h.rmuls_mul_rmulc_rmul_rmul]

/-- The centralizer of a subset of a magma. -/
@[to_additive addCentralizer " The centralizer of a subset of an additive magma. "]
def centralizer [Mul M] : Set M :=
  { c | IsMulCentralizer S c }
#align set.centralizer Set.centralizer
#align set.add_centralizer Set.addCentralizer

variable {S}

@[to_additive mem_addCentralizer]
theorem mem_centralizer_iff [Mul M] {c : M} : c ∈ centralizer S ↔ IsMulCentralizer S c :=
  Iff.rfl
#align set.mem_centralizer_iff Set.mem_centralizer_iff
#align set.mem_add_centralizer Set.mem_addCentralizer

@[to_additive decidableMemAddCentralizer]
instance decidableMemCentralizer [Mul M] [∀ a : M, Decidable <| IsMulCentralizer S a] :
    DecidablePred (· ∈ centralizer S) := fun _ => decidable_of_iff' _ mem_centralizer_iff
#align set.decidable_mem_centralizer Set.decidableMemCentralizer
#align set.decidable_mem_add_centralizer Set.decidableMemAddCentralizer

variable (S)

@[to_additive (attr := simp) zero_mem_addCentralizer]
theorem one_mem_centralizer [MulOneClass M] : (1 : M) ∈ centralizer S where
  comm _  := by rw [one_mul, mul_one]
  lmulc_mul_lmuls_lmul_lmul _ _ := by rw [one_mul, one_mul]
  lmuls_mul_lmulc_lmul_rmul _ _ := by rw [one_mul, mul_one]
  rmuls_mul_rmulc_rmul_rmul _ _ := by rw [mul_one, mul_one]
  rmulc_mul_rmuls_rmul_lmul _ _ := by rw [one_mul, mul_one]
  rmulc_comm_lmuls _ _ := by rw [mul_one, mul_one]
  lmulc_comm_rmuls _ _ := by rw [one_mul, one_mul]
#align set.one_mem_centralizer Set.one_mem_centralizer
#align set.zero_mem_add_centralizer Set.zero_mem_addCentralizer

@[simp]
theorem zero_mem_centralizer [MulZeroClass M] : (0 : M) ∈ centralizer S where
  comm _ := by rw [zero_mul, mul_zero]
  lmulc_mul_lmuls_lmul_lmul _ _ := by rw [zero_mul, zero_mul, zero_mul]
  lmuls_mul_lmulc_lmul_rmul _ _ := by rw [zero_mul, mul_zero, zero_mul]
  rmuls_mul_rmulc_rmul_rmul _ _ := by rw [mul_zero, mul_zero, zero_mul, mul_zero]
  rmulc_mul_rmuls_rmul_lmul _ _ := by rw [zero_mul, mul_zero, mul_zero]
  rmulc_comm_lmuls _ _ := by rw [mul_zero, mul_zero, mul_zero]
  lmulc_comm_rmuls _ _ := by rw [zero_mul, zero_mul, zero_mul]
#align set.zero_mem_centralizer Set.zero_mem_centralizer

variable {S} {a b : M}

@[to_additive (attr := simp) add_mem_addCentralizer]
theorem mul_mem_centralizer [Mul M] (ha : a ∈ centralizer S) (hb : b ∈ centralizer S) :
    a * b ∈ centralizer S where
  comm c := calc
    (a * b) * c = a * (b * c) := by rw [ha.lmulc_comm_rmuls]
    _ = a * (c * b) := by rw [hb.comm]
    _ = c * (a * b) := by rw [(lmulc_comm_lmuls S ha)]
  lmulc_mul_lmuls_lmul_lmul c d :=
/-
      a * b * c = b * a * c := by rw [ha.comm]
      _ = b * (a * c) := by rw [ha.mid_assoc b]
      _ = (c * a) * b := by rw [ha.comm, hb.comm]
      _ = c * (a * b) := by rw [hb.right_assoc c a]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  mid_assoc (a c : M) := calc
    a * (z₁ * z₂) * c = ((a * z₁) * z₂) * c := by rw [hz₁.mid_assoc]
    _ = (a * z₁) * (z₂ * c) := by rw [hz₂.mid_assoc]
    _ = a * (z₁ * (z₂ * c)) := by rw [hz₁.mid_assoc]
    _ = a * (z₁ * z₂ * c) := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]-/
#align set.mul_mem_centralizer Set.mul_mem_centralizer
#align set.add_mem_add_centralizer Set.add_mem_addCentralizer

@[to_additive (attr := simp) neg_mem_addCentralizer]
theorem inv_mem_centralizer [Group M] (ha : a ∈ centralizer S) : a⁻¹ ∈ centralizer S := fun g hg =>
  by rw [mul_inv_eq_iff_eq_mul, mul_assoc, eq_inv_mul_iff_mul_eq, ha g hg]
#align set.inv_mem_centralizer Set.inv_mem_centralizer
#align set.neg_mem_add_centralizer Set.neg_mem_addCentralizer

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

/-
@[to_additive (attr := simp) addCentralizer_eq_top_iff_subset]
theorem centralizer_eq_top_iff_subset {s : Set M} [Mul M] :
    centralizer s = Set.univ ↔ s ⊆ center M :=
  eq_top_iff.trans <| ⟨fun h _ hx _ => (h trivial _ hx).symm, fun h x _ _ hm => (h hm x).symm⟩
#align set.centralizer_eq_top_iff_subset Set.centralizer_eq_top_iff_subset
#align set.add_centralizer_eq_top_iff_subset Set.addCentralizer_eq_top_iff_subset
-/

variable (M)

/-
@[to_additive (attr := simp) addCentralizer_univ]
theorem centralizer_univ [Mul M] : centralizer univ = center M :=
  Subset.antisymm (fun _ ha b => ha b (Set.mem_univ b)) fun _ ha b _ => ha b
#align set.centralizer_univ Set.centralizer_univ
#align set.add_centralizer_univ Set.addCentralizer_univ
-/

variable {M} (S)

@[to_additive (attr := simp) addCentralizer_eq_univ]
theorem centralizer_eq_univ [CommSemigroup M] : centralizer S = univ :=
  (Subset.antisymm (subset_univ _)) fun x _ y _ => mul_comm y x
#align set.centralizer_eq_univ Set.centralizer_eq_univ
#align set.add_centralizer_eq_univ Set.addCentralizer_eq_univ

end Set

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

/-
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
-/
end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
