/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.NumberField.Ideal

/-!
# Docstring

-/

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology nonZeroDivisors

namespace NumberField

open scoped Real

/-- Docstring. -/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/-- Docstring. -/
def residue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K *  Real.sqrt |discr K|)

theorem residue_pos : 0 < residue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · refine mul_pos ?_ ?_
    · rw [Nat.cast_pos]
      exact PNat.pos (torsionOrder K)
    · exact Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

theorem residue_ne_zero : residue K ≠ 0 := (residue_pos K).ne'

theorem dedekindZeta_residue :
    Tendsto (fun s  : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (residue K)) := by
  classical
  refine LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _ ?_
    (fun _ ↦ Nat.cast_nonneg _)
  have : ∀ n, ∑ k ∈ Finset.Icc 1 n, Nat.card {I : Ideal (𝓞 K) // absNorm I = k} =
      Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm I.1 ≤ n} := by
    intro n
    have : Fintype {I : (Ideal (𝓞 K))⁰ | absNorm I.1 ≤ n} := by
      refine Set.Finite.fintype ?_
      refine Set.Finite.of_finite_image (f := fun I ↦ I.1) ?_ ?_
      · refine Set.Finite.subset (finite_setOf_absNorm_le n) ?_
        simp
      · exact Set.injOn_subtype_val
    have : ∀ k, Fintype {I : Ideal (𝓞 K) | absNorm I = k} := by
      intro k
      exact (finite_setOf_absNorm_eq k).fintype
    have : ∀ I ∈ {I : (Ideal (𝓞 K))⁰ | absNorm I.1 ≤ n}.toFinset,
        absNorm I.1 ∈ Finset.Icc 1 n := by
      intro I hI
      simp at hI
      refine Finset.mem_Icc.mpr ⟨?_, hI⟩
      exact absNorm_pos_iff_mem_nonZeroDivisors.mpr I.prop
    rw [← Set.coe_setOf, Nat.card_eq_card_toFinset, Finset.card_eq_sum_card_fiberwise this]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [← Set.coe_setOf, Nat.card_eq_card_toFinset]
    refine (Finset.card_nbij ?_ ?_ ?_ ?_).symm
    · intro I
      exact I.1
    · intro I
      simp only [Finset.mem_filter, Set.mem_toFinset, Set.mem_setOf_eq, and_imp, imp_self,
        implies_true]
    · exact Set.injOn_subtype_val
    · intro I hI
      refine ⟨⟨I, ?_⟩, ?_, rfl⟩
      · rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors]
        rw [Set.coe_toFinset, Set.mem_setOf] at hI
        rw [hI]
        exact (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1).ne'
      · rw [Set.coe_toFinset, Set.mem_setOf] at hI
        simp_rw [Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq, hI, and_true]
        exact (Finset.mem_Icc.mp hk).2
  simp_rw [← Nat.cast_sum, this]
  have := (Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop
  simp_rw [Function.comp_def, Nat.cast_le] at this
  exact this

end NumberField
