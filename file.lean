import Mathlib

/-!
# Banach open mapping theorem

This file contains the Banach open mapping theorem, i.e., the fact that a bijective
bounded linear map between Banach spaces has a bounded inverse.
-/

open Function Metric Set Filter Finset Topology NNReal

open LinearMap (range ker)

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜' F] (f : E →SL[σ] F)
variable {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ']

namespace ContinuousLinearMap

include σ' in
/-- First step of the proof of the Banach open mapping theorem (using completeness of `F`):
by Baire's theorem, there exists a ball in `E` whose image closure has nonempty interior.
Rescaling everything, it follows that any `y ∈ F` is arbitrarily well approached by
images of elements of norm at most `C * ‖y‖`.
For further use, we will only need such an element whose image
is within distance `‖y‖/2` of `y`, to apply an iterative process. -/
theorem exists_approx_preimage_norm_le'
    (h : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n))) :
    ∃ C ≥ 0, ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖ := by
  simp only [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  rcases h with ⟨n, a, ε, ⟨εpos, H⟩⟩
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  refine ⟨(ε / 2)⁻¹ * ‖c‖ * 2 * n, by positivity, fun y => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hc' : 1 < ‖σ c‖ := by simp only [RingHomIsometric.norm_map, hc]
    rcases rescale_to_shell hc' (half_pos εpos) hy with ⟨d, hd, ydlt, -, dinv⟩
    let δ := ‖d‖ * ‖y‖ / 4
    have δpos : 0 < δ := by positivity
    have : a + d • y ∈ ball a ε := by
      simp [dist_eq_norm, lt_of_le_of_lt ydlt.le (half_lt_self εpos)]
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₁, z₁im, h₁⟩
    rcases (mem_image _ _ _).1 z₁im with ⟨x₁, hx₁, xz₁⟩
    rw [← xz₁] at h₁
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₁
    have : a ∈ ball a ε := by
      simp only [mem_ball, dist_self]
      exact εpos
    rcases Metric.mem_closure_iff.1 (H this) _ δpos with ⟨z₂, z₂im, h₂⟩
    rcases (mem_image _ _ _).1 z₂im with ⟨x₂, hx₂, xz₂⟩
    rw [← xz₂] at h₂
    rw [mem_ball, dist_eq_norm, sub_zero] at hx₂
    let x := x₁ - x₂
    have I : ‖f x - d • y‖ ≤ 2 * δ :=
      calc
        ‖f x - d • y‖ = ‖f x₁ - (a + d • y) - (f x₂ - a)‖ := by
          congr 1
          simp only [x, f.map_sub]
          abel
        _ ≤ ‖f x₁ - (a + d • y)‖ + ‖f x₂ - a‖ := norm_sub_le _ _
        _ ≤ δ + δ := by rw [dist_eq_norm'] at h₁ h₂; gcongr
        _ = 2 * δ := (two_mul _).symm
    have J : ‖f (σ' d⁻¹ • x) - y‖ ≤ 1 / 2 * ‖y‖ :=
      calc
        ‖f (σ' d⁻¹ • x) - y‖ = ‖d⁻¹ • f x - (d⁻¹ * d) • y‖ := by
          rwa [f.map_smulₛₗ _, inv_mul_cancel₀, one_smul, map_inv₀, map_inv₀,
            RingHomCompTriple.comp_apply, RingHom.id_apply]
        _ = ‖d⁻¹ • (f x - d • y)‖ := by rw [mul_smul, smul_sub]
        _ = ‖d‖⁻¹ * ‖f x - d • y‖ := by rw [norm_smul, norm_inv]
        _ ≤ ‖d‖⁻¹ * (2 * δ) := by gcongr
        _ = ‖d‖⁻¹ * ‖d‖ * ‖y‖ / 2 := by
          simp only [δ]
          ring
        _ = ‖y‖ / 2 := by
          simp [norm_eq_zero, hd]
        _ = 1 / 2 * ‖y‖ := by ring
    rw [← dist_eq_norm] at J
    have K : ‖σ' d⁻¹ • x‖ ≤ (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ :=
      calc
        ‖σ' d⁻¹ • x‖ = ‖d‖⁻¹ * ‖x₁ - x₂‖ := by rw [norm_smul, RingHomIsometric.norm_map, norm_inv]
        _ ≤ (ε / 2)⁻¹ * ‖c‖ * ‖y‖ * (n + n) := by
          gcongr
          · simpa using dinv
          · exact le_trans (norm_sub_le _ _) (by gcongr)
        _ = (ε / 2)⁻¹ * ‖c‖ * 2 * ↑n * ‖y‖ := by ring
    exact ⟨σ' d⁻¹ • x, J, K⟩

variable [CompleteSpace E]

section
include σ'

/-- The Banach open mapping theorem: if a bounded linear map between Banach spaces is onto, then
any point has a preimage with controlled norm. -/
theorem exists_preimage_norm_le' (h : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n))) :
    ∃ C > 0, ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ C * ‖y‖ := by
  obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le' f h
  /- Second step of the proof: starting from `y`, we want an exact preimage of `y`. Let `g y` be
    the approximate preimage of `y` given by the first step, and `h y = y - f(g y)` the part that
    has no preimage yet. We will iterate this process, taking the approximate preimage of `h y`,
    leaving only `h^2 y` without preimage yet, and so on. Let `u n` be the approximate preimage
    of `h^n y`. Then `u` is a converging series, and by design the sum of the series is a
    preimage of `y`. This uses completeness of `E`. -/
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  refine ⟨2 * C + 1, by linarith, fun y => ?_⟩
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) C0
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have x_ineq : ‖x‖ ≤ (2 * C + 1) * ‖y‖ :=
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
      _ ≤ ∑' n, (1 / 2) ^ n * (C * ‖y‖) :=
        sNu.tsum_le_tsum ule <| Summable.mul_right _ summable_geometric_two
      _ = (∑' n, (1 / 2) ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = 2 * C * ‖y‖ := by rw [tsum_geometric_two, mul_assoc]
      _ ≤ 2 * C * ‖y‖ + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
      _ = (2 * C + 1) * ‖y‖ := by ring
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq, x_ineq⟩

/-- The Banach open mapping theorem: a surjective bounded linear map between Banach spaces is
open. -/
protected theorem isOpenMap' (h : ∃ (n : ℕ) (x : _), x ∈ interior (closure (f '' ball 0 n))) :
    IsOpenMap f := by
  intro s hs
  rcases exists_preimage_norm_le' f h with ⟨C, Cpos, hC⟩
  refine isOpen_iff.2 fun y yfs => ?_
  rcases yfs with ⟨x, xs, fxy⟩
  rcases isOpen_iff.1 hs x xs with ⟨ε, εpos, hε⟩
  refine ⟨ε / C, div_pos εpos Cpos, fun z hz => ?_⟩
  rcases hC (z - y) with ⟨w, wim, wnorm⟩
  have : f (x + w) = z := by rw [f.map_add, wim, fxy, add_sub_cancel]
  rw [← this]
  have : x + w ∈ ball x ε :=
    calc
      dist (x + w) x = ‖w‖ := by
        simp
      _ ≤ C * ‖z - y‖ := wnorm
      _ < C * (ε / C) := by
        apply mul_lt_mul_of_pos_left _ Cpos
        rwa [mem_ball, dist_eq_norm] at hz
      _ = ε := mul_div_cancel₀ _ (ne_of_gt Cpos)
  exact Set.mem_image_of_mem _ (hε this)

end

example {α β : Type*} [NormedAddCommGroup α] [NormedAddCommGroup β] [InnerProductSpace ℝ α]
    [InnerProductSpace ℝ β] [CompleteSpace β] [CompleteSpace α] (T : α →L[ℝ] β) {δ : ℝ} (h0 : δ > 0)
    (h : closure (T '' (Metric.ball (0 : α) 1)) ⊇ Metric.ball (0 : β) δ) :
    T '' (Metric.ball (0 : α) 1) ⊇ Metric.ball (0 : β) δ := by
  have int_t : interior (closure (⇑T '' Metric.ball 0 1)) ⊇ Metric.ball 0 δ :=
    (IsOpen.subset_interior_iff Metric.isOpen_ball).mpr h
  have convex_t : Convex ℝ ((T '' (Metric.ball (0 : α) 1))) :=
    (convex_ball 0 1).is_linear_image T.isBoundedLinearMap.toIsLinearMap
  have : IsOpenMap T := by
    apply ContinuousLinearMap.isOpenMap'
    use 1, 0
    exact mem_interior.mpr ⟨ball 0 δ, by simpa, by simpa⟩
  have : interior (closure (⇑T '' ball 0 1)) = interior (⇑T '' ball 0 1) := by
    apply Convex.interior_closure_eq_interior_of_nonempty_interior convex_t
    use 0
    exact mem_interior.mpr ⟨⇑T '' ball 0 1, by simp, this (ball 0 1) (isOpen_ball), by use 0; simp⟩
  rw [this] at int_t
  exact fun _ a => interior_subset (int_t a)
