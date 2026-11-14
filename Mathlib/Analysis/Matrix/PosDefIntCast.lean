/-
Copyright (c) 2026 Ambrose Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ambrose Tang
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Instances.Matrix

/-!
# Positive definite integer matrices over `ℝ`

A positive definite integer matrix is positive definite over `ℝ`
(`Matrix.PosDef.map_intCast_real`). Positivity of `xᵀ A x` for integer `x` gives non-negativity
for rational `x` by clearing denominators, then for real `x` by density, and a positive
semidefinite matrix with non-zero determinant is positive definite.
-/

public section

open Finset

namespace Matrix

variable {ι : Type*}

/-- A positive definite integer matrix is positive definite over `ℝ`.

Clearing denominators gives `xᵀ A x ≥ 0` for rational `x`; density of `ℚⁿ` extends this to real
`x`; and a positive semidefinite matrix with non-zero determinant is positive definite. -/
theorem PosDef.map_intCast_real [Finite ι] {A : Matrix ι ι ℤ} (hA : A.PosDef) :
    (A.map ((↑) : ℤ → ℝ)).PosDef := by
  classical
  have := Fintype.ofFinite ι
  set B := A.map ((↑) : ℤ → ℝ)
  have hrat (x : ι → ℚ) : 0 ≤ (fun i ↦ (x i : ℝ)) ⬝ᵥ (B *ᵥ fun i ↦ (x i : ℝ)) := by
    obtain ⟨⟨b, hb⟩, hbx⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) x
    choose z hz using hbx
    have hz' (i : ι) : (z i : ℝ) = b * x i := by
      simpa using congrArg ((↑) : ℚ → ℝ) (hz i)
    have hb₀ : (b : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
    have hz₀ : (0 : ℝ) ≤ ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℝ) := by
      exact_mod_cast star_trivial z ▸ hA.posSemidef.dotProduct_mulVec_nonneg z
    have : ((z ⬝ᵥ (A *ᵥ z) : ℤ) : ℝ) =
        b ^ 2 * ((fun i ↦ (x i : ℝ)) ⬝ᵥ (B *ᵥ fun i ↦ (x i : ℝ))) := by
      simp only [dotProduct, mulVec, B, map_apply, Int.cast_sum, Int.cast_mul, hz', mul_sum]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    rw [this] at hz₀
    have : (0 : ℝ) < b ^ 2 := by positivity
    exact (mul_nonneg_iff_of_pos_left this).mp hz₀
  have hB : B.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg (hA.isHermitian.map _ fun _ ↦ rfl) fun x ↦ ?_
    rw [star_trivial]
    have hd : DenseRange fun (x : ι → ℚ) i ↦ (x i : ℝ) :=
      DenseRange.piMap fun _ ↦ Rat.denseRange_cast
    refine hd.induction_on (p := fun x : ι → ℝ ↦ 0 ≤ x ⬝ᵥ (B *ᵥ x)) x ?_ hrat
    exact isClosed_le continuous_const
      (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))
  rw [hB.posDef_iff_det_ne_zero, show B = (Int.castRingHom ℝ).mapMatrix A from rfl,
    ← RingHom.map_det]
  simpa using hA.det_pos.ne'

end Matrix
