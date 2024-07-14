/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.GDelta

#align_import topology.instances.irrational from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Topology of irrational numbers

In this file we prove the following theorems:

* `IsGδ.setOf_irrational`, `dense_irrational`, `eventually_residual_irrational`: irrational numbers
  form a dense Gδ set;

* `Irrational.eventually_forall_le_dist_cast_div`,
  `Irrational.eventually_forall_le_dist_cast_div_of_denom_le`;
  `Irrational.eventually_forall_le_dist_cast_rat_of_denom_le`: a sufficiently small neighborhood of
  an irrational number is disjoint with the set of rational numbers with bounded denominator.

We also provide `OrderTopology`, `NoMinOrder`, `NoMaxOrder`, and `DenselyOrdered`
instances for `{x // Irrational x}`.

## Tags

irrational, residual
-/


open Set Filter Metric

open Filter Topology

protected theorem IsGδ.setOf_irrational : IsGδ { x | Irrational x } :=
  (countable_range _).isGδ_compl
set_option linter.uppercaseLean3 false in
#align is_Gδ_irrational IsGδ.setOf_irrational

@[deprecated (since := "2024-02-15")] alias isGδ_irrational := IsGδ.setOf_irrational

theorem dense_irrational : Dense { x : ℝ | Irrational x } := by
  refine Real.isTopologicalBasis_Ioo_rat.dense_iff.2 ?_
  simp only [gt_iff_lt, Rat.cast_lt, not_lt, ge_iff_le, Rat.cast_le, mem_iUnion, mem_singleton_iff,
    exists_prop, forall_exists_index, and_imp]
  rintro _ a b hlt rfl _
  rw [inter_comm]
  exact exists_irrational_btwn (Rat.cast_lt.2 hlt)
#align dense_irrational dense_irrational

theorem eventually_residual_irrational : ∀ᶠ x in residual ℝ, Irrational x :=
  residual_of_dense_Gδ .setOf_irrational dense_irrational
#align eventually_residual_irrational eventually_residual_irrational

namespace Irrational

variable {x : ℝ}

instance : OrderTopology { x // Irrational x } :=
  induced_orderTopology _ Iff.rfl <| @fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩

instance : NoMaxOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x + (1 : ℕ), hx.add_nat 1⟩, by simp⟩⟩

instance : NoMinOrder { x // Irrational x } :=
  ⟨fun ⟨x, hx⟩ => ⟨⟨x - (1 : ℕ), hx.sub_nat 1⟩, by simp⟩⟩

instance : DenselyOrdered { x // Irrational x } :=
  ⟨fun _ _ hlt =>
    let ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn hlt
    ⟨⟨z, hz⟩, hxz, hzy⟩⟩

theorem eventually_forall_le_dist_cast_div (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ m : ℤ, ε ≤ dist x (m / n) := by
  have A : IsClosed (range (fun m => (n : ℝ)⁻¹ * m : ℤ → ℝ)) :=
    ((isClosedMap_smul₀ (n⁻¹ : ℝ)).comp Int.closedEmbedding_coe_real.isClosedMap).isClosed_range
  have B : x ∉ range (fun m => (n : ℝ)⁻¹ * m : ℤ → ℝ) := by
    rintro ⟨m, rfl⟩
    simp at hx
  rcases Metric.mem_nhds_iff.1 (A.isOpen_compl.mem_nhds B) with ⟨ε, ε0, hε⟩
  refine (ge_mem_nhds ε0).mono fun δ hδ m => not_lt.1 fun hlt => ?_
  rw [dist_comm] at hlt
  refine hε (ball_subset_ball hδ hlt) ⟨m, ?_⟩
  simp [div_eq_inv_mul]
#align irrational.eventually_forall_le_dist_cast_div Irrational.eventually_forall_le_dist_cast_div

theorem eventually_forall_le_dist_cast_div_of_denom_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ k ≤ n, ∀ (m : ℤ), ε ≤ dist x (m / k) :=
  (finite_le_nat n).eventually_all.2 fun k _ => hx.eventually_forall_le_dist_cast_div k
#align irrational.eventually_forall_le_dist_cast_div_of_denom_le Irrational.eventually_forall_le_dist_cast_div_of_denom_le

theorem eventually_forall_le_dist_cast_rat_of_den_le (hx : Irrational x) (n : ℕ) :
    ∀ᶠ ε : ℝ in 𝓝 0, ∀ r : ℚ, r.den ≤ n → ε ≤ dist x r :=
  (hx.eventually_forall_le_dist_cast_div_of_denom_le n).mono fun ε H r hr => by
    simpa only [Rat.cast_def] using H r.den hr r.num
#align irrational.eventually_forall_le_dist_cast_rat_of_denom_le Irrational.eventually_forall_le_dist_cast_rat_of_den_le

end Irrational
