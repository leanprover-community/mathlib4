/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

#align_import number_theory.class_number.admissible_abs from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Admissible absolute value on the integers
This file defines an admissible absolute value `AbsoluteValue.absIsAdmissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

 * `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
-/


namespace AbsoluteValue

open Int

/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
theorem exists_partition_int (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : ℤ} (hb : b ≠ 0) (A : Fin n → ℤ) :
    ∃ t : Fin n → Fin ⌈1 / ε⌉₊,
    ∀ i₀ i₁, t i₀ = t i₁ → ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε := by
  have hb' : (0 : ℝ) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  -- ⊢ ∃ t, ∀ (i₀ i₁ : Fin n), t i₀ = t i₁ → ↑|A i₁ % b - A i₀ % b| < |b| • ε
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : ∀ i, 0 ≤ floor ((A i % b : ℤ) / abs b • ε : ℝ) :=
    fun _ ↦ floor_nonneg.mpr (div_nonneg (cast_nonneg.mpr (emod_nonneg _ hb)) hbε.le)
  refine' ⟨fun i ↦ ⟨natAbs (floor ((A i % b : ℤ) / abs b • ε : ℝ)), _⟩, _⟩
  -- ⊢ natAbs ⌊↑(A i % b) / |b| • ε⌋ < ⌈1 / ε⌉₊
  · rw [← ofNat_lt, natAbs_of_nonneg (hfloor i), floor_lt]
    -- ⊢ ↑(A i % b) / |b| • ε < ↑↑⌈1 / ε⌉₊
    apply lt_of_lt_of_le _ (Nat.le_ceil _)
    -- ⊢ ↑(A i % b) / |b| • ε < 1 / ε
    rw [Algebra.smul_def, eq_intCast, ← div_div, div_lt_div_right hε, div_lt_iff hb', one_mul,
      cast_lt]
    exact Int.emod_lt _ hb
    -- 🎉 no goals
  intro i₀ i₁ hi
  -- ⊢ ↑|A i₁ % b - A i₀ % b| < |b| • ε
  have hi : (⌊↑(A i₀ % b) / abs b • ε⌋.natAbs : ℤ) = ⌊↑(A i₁ % b) / abs b • ε⌋.natAbs :=
    congr_arg ((↑) : ℕ → ℤ) (Fin.mk_eq_mk.mp hi)
  rw [natAbs_of_nonneg (hfloor i₀), natAbs_of_nonneg (hfloor i₁)] at hi
  -- ⊢ ↑|A i₁ % b - A i₀ % b| < |b| • ε
  have hi := abs_sub_lt_one_of_floor_eq_floor hi
  -- ⊢ ↑|A i₁ % b - A i₀ % b| < |b| • ε
  rw [abs_sub_comm, ← sub_div, abs_div, abs_of_nonneg hbε.le, div_lt_iff hbε, one_mul] at hi
  -- ⊢ ↑|A i₁ % b - A i₀ % b| < |b| • ε
  rwa [Int.cast_abs, Int.cast_sub]
  -- 🎉 no goals
#align absolute_value.exists_partition_int AbsoluteValue.exists_partition_int

/-- `abs : ℤ → ℤ` is an admissible absolute value. -/
noncomputable def absIsAdmissible : IsAdmissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_isEuclidean with
    card := fun ε ↦ ⌈1 / ε⌉₊
    exists_partition' := fun n _ hε _ hb ↦ exists_partition_int n hε hb }
#align absolute_value.abs_is_admissible AbsoluteValue.absIsAdmissible

noncomputable instance : Inhabited (IsAdmissible AbsoluteValue.abs) :=
  ⟨absIsAdmissible⟩

end AbsoluteValue
