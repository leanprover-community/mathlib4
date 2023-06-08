import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology Pointwise Asymptotics Metric

section TVS

variable  (𝕜 : Type _) [NontriviallyNormedField 𝕜] {α E F : Type _}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F]

def IsLittleOTVS (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ c : ℝ, 0 < c →
    ∀ᶠ x in l, ∀ b : 𝕜, b ≠ 0 → g x ∈ b • V → ∃ a : 𝕜, ‖a‖ ≤ c * ‖b‖ ∧ f x ∈ a • U

theorem Filter.HasBasis.isLittleOTVS_iff {ιE ιF : Type _} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ c : ℝ, 0 < c →
      ∀ᶠ x in l, ∀ b : 𝕜, b ≠ 0 → g x ∈ b • sF j → ∃ a : 𝕜, ‖a‖ ≤ c * ‖b‖ ∧ f x ∈ a • sE i := by
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun i _ ↦ (hF.exists_iff ?_)
  · rintro U U' hUU' ⟨V, hV, hU⟩
    refine ⟨V, hV, fun c hc ↦ (hU c hc).mono fun x hx ↦ fun b hb₀ hb ↦ ?_⟩
    rcases hx b hb₀ hb with ⟨a, hab, ha⟩
    exact ⟨a, hab, smul_set_mono hUU' ha⟩
  · refine fun V V' hVV' H c hc ↦ (H c hc).mono fun x hx ↦ fun b hb₀ hb ↦ ?_
    exact hx b hb₀ (smul_set_mono hVV' hb)

end TVS

theorem isLittleOTVS_iff_isLittleO (𝕜 : Type _) [NontriviallyNormedField 𝕜] {α E F : Type _}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ f =o[l] g := by
  rcases NormedField.exists_norm_lt_one 𝕜 with ⟨z, hz₀, hz₁⟩
  have hz₀' : z ≠ 0 := norm_pos_iff.1 hz₀
  have hz₁' : 1 < ‖z⁻¹‖
  · rw [norm_inv]
    exact one_lt_inv hz₀ hz₁
  rw [isLittleO_iff]
  constructor
  · rw [(basis_sets _).isLittleOTVS_iff _ (nhds_basis_closedBall_pow hz₀ hz₁)]
    simp only [true_and, true_implies]
    intro H c hc
    rcases exists_pow_lt_of_lt_one hc hz₁ with ⟨m, hm⟩
    rcases H _ (ball_mem_nhds _ one_pos) with ⟨j, hj⟩; clear H
    refine (hj (‖z‖ ^ (j + 1 + m)) (by positivity)).mono fun x hx ↦ ?_; clear hj
    suffices H : ∀ k : ℤ, ‖g x‖ ≤ ‖z‖ ^ k → ‖f x‖ ≤ ‖z‖ ^ (k + 1 + m)
    · cases' (norm_nonneg (g x)).eq_or_gt with hgx hgx
      · rw [hgx, mul_zero]
        have : Tendsto (fun n ↦ ‖z‖ ^ (n + (1 + m))) atTop (𝓝 0) :=
          (tendsto_pow_atTop_nhds_0_of_lt_1 hz₀.le hz₁).comp (tendsto_add_atTop_nat _)
        refine ge_of_tendsto' this fun n ↦ ?_
        rw [← add_assoc]
        exact_mod_cast H n (by simp [hgx])
      · rcases exists_mem_Ico_zpow hgx hz₁' with ⟨n, hn, hn'⟩
        rw [norm_inv, inv_zpow, ← zpow_neg] at hn hn'
        calc
          ‖f x‖ ≤ ‖z‖ ^ (-(n + 1) + 1 + m) := H _ hn'.le
          _ = ‖z‖ ^ m * ‖z‖ ^ (-n) := by
            rw [← zpow_coe_nat, ← zpow_add₀, neg_add, neg_add_cancel_right, add_comm]
            exact hz₀.ne'
          _ ≤ c * ‖g x‖ := mul_le_mul hm.le hn (zpow_nonneg (norm_nonneg _) _) hc.le
    intro k hk
    have : g x ∈ (z ^ (k - j)) • closedBall (0 : F) (‖z‖ ^ j)
    . refine ⟨z ^ (j - k) • g x, ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, norm_zpow, zpow_sub₀ hz₀.ne', zpow_coe_nat,
          div_mul_comm]
        exact mul_le_of_le_one_left (by positivity)
          (div_le_one_of_le hk <| zpow_nonneg (norm_nonneg _) _)
      · simp [smul_smul, ← zpow_add₀ hz₀']
    rcases hx (z ^ (k - j)) (zpow_ne_zero _ hz₀') this with ⟨a, ha, y, hy, hxy⟩
    rw [id, mem_ball_zero_iff] at hy
    calc
      ‖f x‖ = ‖a‖ * ‖y‖ := by simp only [← hxy, norm_smul]
      _ ≤ ‖z‖ ^ (j + 1 + m) * ‖z ^ (k - j)‖ * 1 := by gcongr
      _ = ‖z‖ ^ (k + 1 + m) := ?_
    rw [norm_zpow, mul_one, ← zpow_coe_nat, ← zpow_add₀ hz₀.ne']
    push_cast; congr 1; abel
  · rw [(nhds_basis_ball_pow hz₀ hz₁).isLittleOTVS_iff _ (nhds_basis_ball_pow hz₀ hz₁)]
    refine fun H i _ ↦ ⟨i, trivial, fun c hc ↦ ?_⟩
    rcases NormedField.exists_norm_lt 𝕜 hc with ⟨u, hu₀, huc⟩
    refine (H hu₀).mono fun x hx b hb₀ hxb ↦ ⟨u * b, ?_, ?_⟩
    · rw [norm_mul]; gcongr
    refine ⟨(u * b)⁻¹ • f x, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, norm_inv, norm_mul, ← div_eq_inv_mul]
      rcases hxb with ⟨y, hy, hyx⟩
      calc
        ‖f x‖ / (‖u‖ * ‖b‖) ≤ (‖u‖ * ‖g x‖) / (‖u‖ * ‖b‖) := by gcongr
        _ = ‖y‖ := by
          rw [← hyx, norm_smul, mul_div_mul_left, mul_div_cancel_left]
          exacts [norm_ne_zero_iff.2 hb₀, hu₀.ne']
        _ < ‖z‖ ^ i := mem_ball_zero_iff.1 hy
    · apply smul_inv_smul₀
      exact mul_ne_zero (norm_pos_iff.1 hu₀) hb₀
