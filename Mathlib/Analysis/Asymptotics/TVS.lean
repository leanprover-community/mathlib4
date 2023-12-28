import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull

open Set Filter Asymptotics Metric
open scoped Topology Pointwise ENNReal NNReal

section TVS

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {α E F : Type*}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F]

noncomputable def egauge (s : Set E) (x : E) : ℝ≥0∞ := ⨅ (c : 𝕜) (_ : x ∈ c • s), ‖c‖₊

@[mono, gcongr]
lemma egauge_anti {s t : Set E} (h : s ⊆ t) (x : E) : egauge 𝕜 t x ≤ egauge 𝕜 s x :=
  iInf_mono fun _c ↦ iInf_mono' fun hc ↦ ⟨smul_set_mono h hc, le_rfl⟩

variable {𝕜}
  
lemma egauge_le_of_mem_smul {c : 𝕜} {s : Set E} {x : E} (h : x ∈ c • s) : egauge 𝕜 s x ≤ ‖c‖₊ :=
  iInf₂_le c h

lemma le_egauge_iff {r : ℝ≥0∞} {s : Set E} {x : E} :
    r ≤ egauge 𝕜 s x ↔ ∀ c : 𝕜, x ∈ c • s → r ≤ ‖c‖₊ :=
  le_iInf₂_iff

lemma egauge_eq_top {s : Set E} {x : E} : egauge 𝕜 s x = ∞ ↔ ∀ c : 𝕜, x ∉ c • s := by
  simp [egauge]

lemma egauge_lt_iff {r : ℝ≥0∞} {s : Set E} {x : E} :
    egauge 𝕜 s x < r ↔ ∃ c : 𝕜, x ∈ c • s ∧ ‖c‖₊ < r := by
  simp [egauge, iInf_lt_iff]

variable (𝕜)

def IsLittleOTVS' (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ c : ℝ, 0 < c →
    ∀ᶠ x in l, ∀ b : 𝕜, b ≠ 0 → g x ∈ b • V → ∃ a : 𝕜, ‖a‖ ≤ c * ‖b‖ ∧ f x ∈ a • U

def IsLittleOTVS (f : α → E) (g : α → F) (l : Filter α) : Prop :=
  ∀ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 (0 : F), ∀ c : ℝ≥0, 0 < c →
    ∀ᶠ x in l, egauge 𝕜 U (f x) ≤ c * egauge 𝕜 V (g x)

variable {𝕜}

theorem Filter.HasBasis.isLittleOTVS_iff {ιE ιF : Type _} {pE : ιE → Prop} {pF : ιF → Prop}
    {sE : ιE → Set E} {sF : ιF → Set F} (hE : HasBasis (𝓝 (0 : E)) pE sE)
    (hF : HasBasis (𝓝 (0 : F)) pF sF) {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS 𝕜 f g l ↔ ∀ i, pE i → ∃ j, pF j ∧ ∀ c : ℝ≥0, 0 < c →
      ∀ᶠ x in l, egauge 𝕜 (sE i) (f x) ≤ c * egauge 𝕜 (sF j) (g x) := by
  refine (hE.forall_iff ?_).trans <| forall₂_congr fun _ _ ↦ hF.exists_iff ?_
  · rintro s t hsub ⟨V, hV₀, hV⟩
    exact ⟨V, hV₀, fun c hc ↦ (hV c hc).mono fun x ↦ le_trans <| egauge_anti _ hsub _⟩
  · refine fun s t hsub h c hc ↦ (h c hc).mono fun x hx ↦ hx.trans ?_
    gcongr

example {f : α → 𝕜} {g : α → E} {l : Filter α} (hf₀ : ∀ᶠ x in l, f x ≠ 0) :
    IsLittleOTVS 𝕜 g f l ↔ Tendsto (fun x ↦ (f x)⁻¹ • g x) l (𝓝 0) := by
  rw [(nhds_basis_balanced 𝕜 _).isLittleOTVS_iff nhds_basis_ball]
  rw [(nhds_basis_balanced 𝕜 _).tendsto_right_iff]
  refine forall₂_congr fun U ⟨hU, hUb⟩ ↦ ⟨?_, ?_⟩
  · rintro ⟨ε, hε₀, hε⟩
    lift ε to ℝ≥0 using hε₀.le
    
  
    
  

example {f : α → E} {g : α → F} {l : Filter α} :
    IsLittleOTVS' 𝕜 f g l ↔ IsLittleOTVS 𝕜 f g l := by
  refine forall₂_congr fun U _ ↦ exists_congr fun V ↦ and_congr_right fun hV ↦
    ⟨fun h c hc ↦ ?_, fun h c hc ↦ ?_⟩
  · filter_upwards [h c hc] with x hx
    simp only [egauge, ENNReal.mul_iInf_of_ne (ENNReal.coe_ne_zero.2 hc.ne') ENNReal.coe_ne_top]
    refine le_iInf₂ fun b hgb ↦ ?_
    rcases eq_or_ne b 0 with rfl | hb₀
    · have hx0 : g x = 0 := zero_smul_set_subset V hgb
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
      rcases NormedField.exists_norm_lt 𝕜 (div_pos hε hc) with ⟨b', hb₀', hb' : ‖b'‖₊ < ε / c⟩
      rw [norm_pos_iff] at hb₀'
      rcases hx b' hb₀' ⟨0, mem_of_mem_nhds hV, by simp [hx0]⟩ with ⟨a, hab, hfa⟩
      refine iInf₂_le_of_le _ hfa ?_
      suffices ‖a‖ ≤ ε by simpa
      exact hab.trans ((le_div_iff' hc).1 hb'.le)
    · rcases hx b hb₀ hgb with ⟨a, hab, hfa⟩
      refine iInf₂_le_of_le a hfa ?_
      assumption_mod_cast
  · lift c to ℝ≥0 using hc.le; norm_cast at hc
    filter_upwards [h _ (half_pos hc)] with x hx b hb hgb
    have hglt : egauge 𝕜 V (g x) < 2 * ‖b‖₊ := by
      refine egauge_lt_iff.2 ⟨_, hgb, ?_⟩
      norm_cast; rw [← NNReal.coe_lt_coe]; push_cast
      linarith [norm_pos_iff.2 hb]
    have hflt : egauge 𝕜 U (f x) < c * ‖b‖₊ :=
      calc
        egauge 𝕜 U (f x) ≤ ↑(c / 2) * egauge 𝕜 V (g x) := hx
        _ < ↑(c / 2) * (2 * ‖b‖₊) := by gcongr; exact ENNReal.coe_ne_top
        _ = c * ‖b‖₊ := by norm_cast; field_simp; ac_rfl
    rcases egauge_lt_iff.1 hflt with ⟨a, hfa, halt⟩
    exact ⟨a, by exact_mod_cast halt.le, hfa⟩

#exit    

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
