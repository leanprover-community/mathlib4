import Mathlib.Analysis.InnerProductSpace.Projection

open Filter Finset Function
open scoped BigOperators Topology

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

theorem LinearIsometry.tendsto_inv_smul_sum_range_pow_apply_orthogonalProjection
    (f : E →ₗᵢ[𝕜] E) (x : E) :
    Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n) x) atTop
      (𝓝 <| orthogonalProjection (LinearMap.eqLocus f 1) x) := by
  set S := LinearMap.eqLocus f 1
  set P := orthogonalProjection S
  set g := f.toContinuousLinearMap
  set avg := fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, g ^ n
  have havg_norm : ∀ N x, ‖avg N x‖ ≤ ‖x‖ := fun N x ↦
    calc
      ‖avg N x‖ = ‖∑ n in range N, (f^n) x‖ / N := by simp [norm_smul, div_eq_inv_mul]
      _ ≤ (∑ n in range N, ‖(f ^ n) x‖) / N := by gcongr; apply norm_sum_le
      _ = (N / N) * ‖x‖ := by simp only [norm_map]; simp [mul_div_right_comm]
      _ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) (div_self_le_one _)
  suffices : Tendsto (avg · x) atTop (𝓝 (P x))
  · simpa using this
  have havgS : ∀ (y : S) {N : ℕ}, N ≠ 0 → avg N y = y := fun y N hN ↦
    calc
      avg N y = (N : 𝕜)⁻¹ • (N : 𝕜) • y := by simp [iterate_fixed y.2, ← nsmul_eq_smul_cast]
      _ = y := inv_smul_smul₀ (Nat.cast_ne_zero.2 hN) _
  suffices : Tendsto (avg · (x - P x)) atTop (𝓝 0)
  · refine tendsto_sub_nhds_zero_iff.1 (this.congr' <| (eventually_ne_atTop 0).mono fun N hN ↦ ?_)
    simp only [map_sub, havgS _ hN]
  -- TODO: move to a separate lemma; what's the right generality?
  have H₁ : (LinearMap.range (1 - g))ᗮ = S
  · ext x
    suffices : (∀ (a : E), ⟪a, x⟫ = ⟪f a, x⟫) ↔ f x = x
    · simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero]
    refine ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
    · rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := 𝕜), inner_sub_right,
        inner_sub_left, inner_sub_left, f.inner_map_map, ← h, ← inner_conj_symm x (f x), ← h,
        inner_self_conj, sub_self]
    · rw [← f.inner_map_map, h]
  have H₂ : Sᗮ = (LinearMap.range (1 - g)).topologicalClosure
  · rw [← H₁, Submodule.orthogonal_orthogonal_eq_closure]
  have H₃ : x - P x ∈ closure (LinearMap.range (1 - g))
  · rw [← Submodule.topologicalClosure_coe, ← H₂]
    apply sub_orthogonalProjection_mem_orthogonal
  have H₄ : ∀ y, Tendsto (‖avg · (y - f y)‖) atTop (𝓝 0) := fun y ↦ by
    have : ∀ N, avg N (y - f y) = (N : 𝕜) ⁻¹ • ((f ^ (0 : ℕ)) y - (f ^ N) y) := fun N ↦ by
      rw [← sum_range_sub' (fun n : ℕ ↦ (f ^ n) y) N]
      simp [pow_succ', ← smul_sub]
    have : ∀ N : ℕ, ‖avg N (y - f y)‖ ≤ (N : ℝ)⁻¹ * (‖y‖ + ‖y‖)
    · intro N
      rw [this, norm_smul, norm_inv, IsROrC.norm_natCast]
      gcongr
      exact norm_sub_le_of_le (norm_map _ _).le (norm_map _ _).le
    refine squeeze_zero (fun _ ↦ norm_nonneg _) this ?_
    rw [← zero_mul (‖y‖ + ‖y‖)]
    refine Tendsto.mul ?_ tendsto_const_nhds
    exact tendsto_inv_atTop_zero.comp tendsto_nat_cast_atTop_atTop
  refine NormedAddCommGroup.tendsto_nhds_zero.2 fun ε εpos ↦ ?_
  rcases SeminormedAddCommGroup.mem_closure_iff.1 H₃ _ (half_pos εpos) with ⟨_, ⟨y, rfl⟩, hy⟩
  refine ((H₄ y).eventually (gt_mem_nhds <| half_pos εpos)).mono fun N hN ↦ ?_
  calc
    ‖avg N (x - P x)‖ = ‖avg N (x - P x - (y - f y)) + avg N (y - f y)‖ := by
      rw [map_sub _ (x - P x), sub_add_cancel]
    _ ≤ ‖avg N (x - P x - (y - f y))‖ + ‖avg N (y - f y)‖ := norm_add_le _ _
    _ ≤ ‖x - P x - (y - f y)‖ + ‖avg N (y - f y)‖ :=
      add_le_add_right (havg_norm _ _) _
    _ < ε / 2 + ε / 2 := add_lt_add hy hN
    _ = ε := add_halves _
