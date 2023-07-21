import Mathlib.Analysis.InnerProductSpace.Projection

open Filter Finset
open scoped BigOperators Topology

variable {𝕜 E : Type _} [IsROrC 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- TODO: generalize `LinearMap.eqLocus` to `SemilinearMapClass` and use it here
theorem LinearIsometry.tendsto_inv_smul_sum_range_pow_apply_orthogonalProjection
    (f : E →ₗᵢ[𝕜] E) (x : E) :
    Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n) x) atTop
      (𝓝 <| orthogonalProjection (LinearMap.eqLocus f 1) x) := by
  set S := LinearMap.eqLocus f 1
  set P := orthogonalProjection S
  have hfp : ∀ y : S, f y = y := Subtype.prop
  have hfpn : ∀ (y : S) (n : ℕ), (f ^ n) y = y := fun y n ↦ by
    induction n with
    | zero => rfl
    | succ n ihn => rw [pow_succ, coe_mul, Function.comp_apply, ihn, hfp]
  suffices : Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n) (x - P x)) atTop (𝓝 0)
  · refine tendsto_sub_nhds_zero_iff.1 (this.congr' <| (eventually_ne_atTop 0).mono fun N hN ↦ ?_)
    simp only [map_sub, hfpn, sum_sub_distrib, ← nsmul_eq_sum_const, smul_sub]
    rw [nsmul_eq_smul_cast (R := 𝕜), inv_smul_smul₀ (Nat.cast_ne_zero.2 hN)]
  -- TODO: move to a separate lemma; what's the right generality?
  have H₁ : (LinearMap.range (1 - f.toContinuousLinearMap))ᗮ = S
  · ext x
    suffices : (∀ (a : E), ⟪a, x⟫ = ⟪f a, x⟫) ↔ f x = x
    · simpa [Submodule.mem_orthogonal, inner_sub_left, sub_eq_zero]
    refine ⟨fun h ↦ ?_, fun h a ↦ ?_⟩
    · rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := 𝕜), inner_sub_right,
        inner_sub_left, inner_sub_left, f.inner_map_map, ← h, ← inner_conj_symm x (f x), ← h,
        inner_self_conj, sub_self]
    · rw [← f.inner_map_map, h]
  have H₂ : (LinearMap.ker (1 - g))ᗮ = (LinearMap.range (1 - g)).topologicalClosure
  · rw [← H₁, Submodule.orthogonal_orthogonal_eq_closure]
  have H₃ : x - P x ∈ closure (LinearMap.range (1 - g))
  · rw [← Submodule.topologicalClosure_coe, ← H₂]
    apply sub_orthogonalProjection_mem_orthogonal
  have H₄ : ∀ y, Tendsto (fun N : ℕ ↦ ‖(N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n) (y - f y)‖) atTop (𝓝 0)
  · intro y
    have : ∀ N : ℕ, ∑ n in range N, (f ^ n) (y - f y) = (f ^ (0 : ℕ)) y - (f ^ N) y := fun N ↦ by
      rw [← sum_range_sub' (fun n : ℕ ↦ (f ^ n) y) N]
      simp [pow_succ']
    have : ∀ N : ℕ, ‖(N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n) (y - f y)‖ ≤ (N : ℝ)⁻¹ * (‖y‖ + ‖y‖)
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
  
    -- simpa only [zero_mul]
    --   using (tendsto_inv_atTop_zero.comp tendsto_nat_cast_atTop_atTop).mul tendsto_const_nhds
  
      -- calc
      --   ∑ n in range N, (f ^ n) (y - f y) = ∑ n in range N, ((f ^ n) y - (f ^ (n + 1)) y) := by
      --     simp [pow_succ]
      --   _ = (f ^ 0) y - (f ^ N) y := sum_range_sub' (fun n ↦ (f ^ n) y) N
    -- simp only [this, smul_sub]
    
  -- change Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, (g ^ n)) atTop (𝓝 P)
  -- have : ∀ N : ℕ, ∑ n in range N, (g ^ n) = N • P + (1 - g ^ N) := fun N ↦ by
  --   induction N with
  --   | zero => simp [Nat.zero_eq]
  --   | succ N ihN =>
  --     rw [sum_range_succ, ihN, succ_nsmul']
  --     suffices : g ^ (N + 1) = 

-- theorem ContinuousLinearMap.tendsto_inv_smul_sum_range_pow_of_isometry (f : E →L[𝕜] E)
--     (hf : Isometry f) :
--     Tendsto (fun N : ℕ ↦ (N : 𝕜)⁻¹ • ∑ n in range N, (f ^ n)) atTop
--       (𝓝 ((Submodule.subtypeL _) ∘L
--         orthogonalProjection (LinearMap.ker (ContinuousLinearMap.id 𝕜 E - f)))) := by
--   exact _
