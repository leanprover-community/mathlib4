/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.LSeries.Residue
import Mathlib.NumberTheory.NumberField.Ideal

/-!
# Docstring

-/

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

namespace NumberField

open Filter Ideal NumberField.InfinitePlace NumberField.Units Topology NumberTheory.LSeries

open scoped Real

/-- Docstring. -/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/-- Docstring. -/
def residue : ℝ :=
  (2 ^ NrRealPlaces K * (2 * π) ^ NrComplexPlaces K * regulator K * classNumber K) /
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
  refine tendsto_mul_of_sum_div_tendsto (residue_pos K) ?_
  convert (ideal.tendsto_norm_le_div_atop K).comp tendsto_natCast_atTop_atTop with n
  simp_rw [Function.comp_apply, Nat.cast_le]
  congr
  have : ∀ i, Fintype {I : Ideal (𝓞 K) | absNorm I = i} := by
    intro i
    refine Set.Finite.fintype ?_
    exact finite_setOf_absNorm_eq i
  have : ∀ i, Fintype {I : Ideal (𝓞 K) | absNorm I ≤ i} := by
    intro i
    refine Set.Finite.fintype ?_
    exact finite_setOf_absNorm_le i
  simp_rw (config := {singlePass := true}) [← Set.coe_setOf, Nat.card_eq_card_toFinset]
  rw [← Nat.cast_sum, Finset.card_eq_sum_card_fiberwise (t := Finset.range (n + 1))
    (f := fun I ↦ absNorm I)]
  · congr! with n hn
    ext
    simp only [Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, iff_and_self]
    intro h
    rw [h]
    exact Finset.mem_range_succ_iff.mp hn
  · intro x hx
    simp at hx
    exact Finset.mem_range_succ_iff.mpr hx

end NumberField
