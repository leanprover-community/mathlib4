import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.Seminorm

open Set Filter Asymptotics Metric
open scoped Topology Pointwise ENNReal NNReal

section TVS


variable (𝕜)

def IsLittleOTVS (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ ε ≠ (0 : ℝ≥0),
    ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ ε * egauge 𝕜 V (g x)

variable {𝕜}

theorem Filter.HasBasis.isLittleOTVS_iff {ιE ιF : Type _} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ ε ≠ (0 : ℝ≥0),
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ ε * egauge 𝕜 (sF j) (g x) := by
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun ε hε ↦ (hV ε hε).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h ε hε ↦ (h ε hε).mono fun x hx ↦ hx.trans ?_
    gcongr

lemma IsLittleOTVS.tendsto_inv_smul {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h : IsLittleOTVS 𝕜 g f l) : Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [(basis_sets _).isLittleOTVS_iff nhds_basis_ball] at h
  rw [(nhds_basis_balanced 𝕜 _).tendsto_right_iff]
  rintro U ⟨hU, hUB⟩
  rcases h U hU with ⟨ε, hε₀, hε⟩
  lift ε to ℝ≥0 using hε₀.le; norm_cast at hε₀
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  filter_upwards [hε (ε / 2 / ‖c‖₊) (ne_of_gt <| div_pos (half_pos hε₀) (one_pos.trans hc))]
    with x hx
  refine mem_of_egauge_lt_one hUB ?_
  rw [id, egauge_smul_right (fun _ ↦ mem_of_mem_nhds hU), nnnorm_inv]
  calc
    ↑‖f x‖₊⁻¹ * egauge 𝕜 U (g x)
      ≤ (↑‖f x‖₊)⁻¹ * (↑(ε / 2 / ‖c‖₊) * egauge 𝕜 (ball 0 ε) (f x)) :=
      mul_le_mul' ENNReal.coe_inv_le hx
    _ ≤ (↑‖f x‖₊)⁻¹ * ((ε / 2 / ‖c‖₊) * (‖c‖₊ * ‖f x‖₊ / ε)) := by
      gcongr
      · refine ENNReal.coe_div_le.trans ?_; gcongr; apply ENNReal.coe_div_le
      · exact egauge_ball_le_of_one_lt_norm hc (.inl hε₀.ne')
    _ = (‖f x‖₊ / ‖f x‖₊) * (ε / ε) * (‖c‖₊ / ‖c‖₊) * (1 / 2) := by
      simp only [div_eq_mul_inv, one_mul]; ring
    _ ≤ 1 * 1 * 1 * (1 / 2) := by gcongr <;> apply ENNReal.div_self_le_one
    _ < 1 := by norm_num

lemma isLittleOTVS_iff_tendsto_inv_smul {f : α → 𝕜} {g : α → E} {l : Filter α}
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    IsLittleOTVS 𝕜 g f l ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  refine ⟨IsLittleOTVS.tendsto_inv_smul, fun h U hU ↦ ?_⟩
  refine ⟨ball 0 1, ball_mem_nhds _ one_pos, fun ε hε ↦ ?_⟩
  rcases NormedField.exists_norm_lt 𝕜 hε.bot_lt with ⟨c, hc₀, hcε : ‖c‖₊ < ε⟩
  rw [norm_pos_iff] at hc₀
  filter_upwards [h₀, h <| (set_smul_mem_nhds_zero_iff hc₀).2 hU]
    with x hx₀ (hx : (f x)⁻¹ • g x ∈ c • U)
  rcases eq_or_ne (f x) 0 with hf₀ | hf₀
  · simp [hx₀ hf₀, mem_of_mem_nhds hU]
  · rw [mem_smul_set_iff_inv_smul_mem₀ hc₀, smul_smul] at hx
    refine (egauge_le_of_smul_mem_of_ne hx (by simp [*])).trans ?_
    simp_rw [nnnorm_mul, nnnorm_inv, mul_inv, inv_inv, ENNReal.coe_mul]
    gcongr
    apply le_egauge_ball_one

lemma isLittleOTVS_iff_isLittleO {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ f =o[l] g := by
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc : 1 < ‖c‖₊⟩
  have hc₀ : 0 < ‖c‖₊ := one_pos.trans hc
  simp only [isLittleO_iff, nhds_basis_ball.isLittleOTVS_iff nhds_basis_ball]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ⟨1, one_pos, fun δ hδ ↦ ?_⟩⟩
  · rcases h ε hε with ⟨δ, hδ₀, hδ⟩
    lift ε to ℝ≥0 using hε.le; lift δ to ℝ≥0 using hδ₀.le; norm_cast at hε hδ₀
    filter_upwards [hδ (δ / ‖c‖₊) (div_pos hδ₀ hc₀).ne'] with x hx
    suffices (‖f x‖₊ / ε : ℝ≥0∞) ≤ ‖g x‖₊ by
      rw [← ENNReal.coe_div hε.ne'] at this
      rw [← div_le_iff' (NNReal.coe_pos.2 hε)]
      exact_mod_cast this
    calc
      (‖f x‖₊ / ε : ℝ≥0∞) ≤ egauge 𝕜 (ball 0 ε) (f x) := div_le_egauge_ball 𝕜 _ _
      _ ≤ ↑(δ / ‖c‖₊) * egauge 𝕜 (ball 0 ↑δ) (g x) := hx
      _ ≤ (δ / ‖c‖₊) * (‖c‖₊ * ‖g x‖₊ / δ) := by
        gcongr
        exacts [ENNReal.coe_div_le, egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hδ₀)]
      _ = (δ / δ) * (‖c‖₊ / ‖c‖₊) * ‖g x‖₊ := by simp only [div_eq_mul_inv]; ring
      _ ≤ 1 * 1 * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = ‖g x‖₊ := by simp
  · filter_upwards [@h ↑(ε * δ / ‖c‖₊) (by positivity)] with x (hx : ‖f x‖₊ ≤ ε * δ / ‖c‖₊ * ‖g x‖₊)
    lift ε to ℝ≥0 using hε.le
    calc
      egauge 𝕜 (ball 0 ε) (f x) ≤ ‖c‖₊ * ‖f x‖₊ / ε :=
        egauge_ball_le_of_one_lt_norm hc (.inl <| ne_of_gt hε)
      _ ≤ ‖c‖₊ * (↑(ε * δ / ‖c‖₊) * ‖g x‖₊) / ε := by gcongr; exact_mod_cast hx
      _ = (‖c‖₊ / ‖c‖₊) * (ε / ε) * δ * ‖g x‖₊ := by
        simp only [div_eq_mul_inv, ENNReal.coe_inv hc₀.ne', ENNReal.coe_mul]; ring
      _ ≤ 1 * 1 * δ * ‖g x‖₊ := by gcongr <;> exact ENNReal.div_self_le_one
      _ = δ * ‖g x‖₊ := by simp
      _ ≤ δ * egauge 𝕜 (ball 0 1) (g x) := by gcongr; apply le_egauge_ball_one
