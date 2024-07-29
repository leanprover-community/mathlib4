import Mathlib.Analysis.Calculus.Rademacher

open Real Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example [FiniteDimensional ℝ E] {x : E} (hx : ‖x‖ = 1) (h : DifferentiableAt ℝ (‖·‖) x)
    (φ : E → ℝ) (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    rw [φ_eq, ← abs_neg]
    nth_rw 1 [← abs_one]
    congr
    ring
    rw [mul_inv_cancel ht]
  have this (t : ℝ) : 1 ≤ ‖x - t • (y - (φ y) • x)‖ := by
    rcases eq_or_ne t 0 with rfl | ht
    · rw [zero_smul, sub_zero, hx]
    · calc
        1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := this t ht
        _ = |t| * |φ y - φ (((φ y) + 1 / t) • x)| := by
          rw [← abs_mul]
          congr
          ring
        _ ≤ |t| * ‖y - (φ y + 1 / t) • x‖ := by
          rw [mul_le_mul_left]
          convert hφ.dist_le_mul y ((φ y + 1 / t) • x) using 1
          · simp [dist_eq_norm]
          · exact abs_pos.2 ht
        _ = ‖x - t • (y - (φ y) • x)‖ := by
          rw [← norm_eq_abs, ← norm_smul, ← norm_neg, smul_sub, smul_smul, mul_add,
            mul_one_div_cancel ht, add_smul, one_smul, mul_smul, smul_sub]
          congr 1
          abel
  have : IsLocalMin (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 := by
    simp [IsLocalMin, IsMinFilter, hx, this]
  have aux := this.deriv_eq_zero
  -- rcases h with ⟨f', hf'⟩
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const]
      simp
      exact differentiableAt_id
    · simpa
    · simp
  rw [aux] at this
