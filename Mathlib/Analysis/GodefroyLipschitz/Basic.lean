import Mathlib.Analysis.Calculus.Rademacher

open Real NNReal Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lol (f : E → ℝ) (x y : E) (h : DifferentiableAt ℝ f x) :
    fderiv ℝ f x y = deriv (fun t : ℝ ↦ f (x + t • y)) 0 := by
  conv_rhs => enter [1]; change f ∘ (fun t ↦ x + t • y)
  rw [fderiv.comp_deriv, zero_smul, add_zero, deriv_const_add, deriv_smul_const, deriv_id'']
  · simp
  · exact differentiableAt_id
  · simpa
  · simp

theorem fderiv_norm {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    fderiv ℝ (‖·‖) x x = ‖x‖ := by
  rw [lol _ _ _ h]
  have this (t : ℝ) (ht : t ≥ -1) : ‖x + t • x‖ = (1 + t) * ‖x‖ := by
    calc
      ‖x + t • x‖ = ‖(1 + t) • x‖ := by
        rw [add_smul, one_smul]
      _ = |1 + t| * ‖x‖ := by
        rw [← norm_eq_abs, norm_smul]
      _ = (1 + t) * ‖x‖ := by
        rw [abs_eq_self.2]
        linarith
  rw [← derivWithin_of_mem_nhds (s := Ici (-1)), derivWithin_congr (f := fun t ↦ (1 + t) * ‖x‖),
    derivWithin_of_mem_nhds]
  · rw [deriv_mul_const, deriv_const_add]
    simp
    apply DifferentiableAt.const_add
    exact differentiableAt_id
  · exact Ici_mem_nhds (by norm_num)
  · intro t ht
    apply this
    simpa
  · simp
  · exact Ici_mem_nhds (by norm_num)

theorem not_differentiableAt_norm_zero (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] :
    ¬DifferentiableAt ℝ (‖·‖) (0 : E) := by
  rcases NormedSpace.exists_lt_norm ℝ E 0 with ⟨x, hx⟩
  intro h
  have : DifferentiableAt ℝ (fun t : ℝ ↦ ‖t • x‖) 0 := by
    apply DifferentiableAt.comp
    · simpa
    · simp
  have : DifferentiableAt ℝ (|·|) (0 : ℝ) := by
    simp_rw [norm_smul, norm_eq_abs] at this
    have mdr : (fun t : ℝ ↦ |t|) = fun t : ℝ ↦ (1 / ‖x‖) * |t| * ‖x‖ := by
      ext t
      rw [mul_assoc, mul_comm, mul_assoc, mul_one_div_cancel, mul_one]
      exact hx.ne.symm
    rw [mdr]
    simp_rw [mul_assoc]
    apply DifferentiableAt.const_mul
    exact this
  exact not_differentiableAt_abs_zero this

theorem norm_fderiv_norm [Nontrivial E] {x : E} (h : DifferentiableAt ℝ (‖·‖) x) :
    ‖fderiv ℝ (‖·‖) x‖ = 1 := by
  have : x ≠ 0 := by
    intro hx
    apply not_differentiableAt_norm_zero E
    convert h
    exact hx.symm
  apply le_antisymm
  · rw [show (1 : ℝ) = ↑(1 : ℝ≥0) by rfl]
    apply norm_fderiv_le_of_lipschitz
    exact lipschitzWith_one_norm
  · apply le_of_mul_le_mul_right (a := ‖x‖)
    rw [one_mul]
    calc
      ‖x‖ = fderiv ℝ (‖·‖) x x := (fderiv_norm h).symm
      _ ≤ ‖fderiv ℝ (‖·‖) x x‖ := le_norm_self _
      _ ≤ ‖fderiv ℝ (‖·‖) x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    exact norm_pos_iff.2 this


example [FiniteDimensional ℝ E] {x : E} (hx : ‖x‖ = 1) (h : DifferentiableAt ℝ (‖·‖) x)
    (φ : E → ℝ) (hφ : LipschitzWith 1 φ) (φ_eq : ∀ t : ℝ, φ (t • x) = t) :
    φ = fderiv ℝ (‖·‖) x := by
  ext y
  have this t (ht : t ≠ 0) : 1 = |t * (φ y) - t * (φ (((φ y) + 1 / t) • x))| := by
    rw [φ_eq, mul_add, ← sub_sub, sub_self, mul_one_div_cancel ht]
    simp
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
  have : deriv (fun t : ℝ ↦ ‖x - t • (y - (φ y) • x)‖) 0 = - fderiv ℝ (‖·‖) x (y - (φ y) • x) := by
    conv_lhs => enter [1]; change ((‖·‖) ∘ (fun t : ℝ ↦ x - t • (y - (φ y) • x)))
    rw [fderiv.comp_deriv]
    · rw [deriv_const_sub, deriv_smul_const]
      simp
      exact differentiableAt_id
    · simpa
    · simp
  rw [aux, map_sub, map_smul, fderiv_norm h, hx] at this
  simp only [smul_eq_mul, mul_one, neg_sub] at this
  exact sub_eq_zero.1 this.symm
