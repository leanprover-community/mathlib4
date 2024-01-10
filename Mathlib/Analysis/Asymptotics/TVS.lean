import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.Seminorm

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

@[simp] lemma egauge_empty (x : E) : egauge 𝕜 ∅ x = ∞ := by simp [egauge]

variable {𝕜}

lemma egauge_le_of_mem_smul {c : 𝕜} {s : Set E} {x : E} (h : x ∈ c • s) : egauge 𝕜 s x ≤ ‖c‖₊ :=
  iInf₂_le c h

lemma egauge_le_of_smul_mem_of_ne {c : 𝕜} {s : Set E} {x : E} (h : c • x ∈ s) (hc : c ≠ 0) :
    egauge 𝕜 s x ≤ ‖c‖₊⁻¹ := by
  rw [← nnnorm_inv]
  exact egauge_le_of_mem_smul <| (mem_inv_smul_set_iff₀ hc _ _).2 h

lemma egauge_le_of_smul_mem {c : 𝕜} {s : Set E} {x : E} (h : c • x ∈ s) :
    egauge 𝕜 s x ≤ (↑‖c‖₊)⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le

lemma le_egauge_iff {r : ℝ≥0∞} {s : Set E} {x : E} :
    r ≤ egauge 𝕜 s x ↔ ∀ c : 𝕜, x ∈ c • s → r ≤ ‖c‖₊ :=
  le_iInf₂_iff

lemma egauge_eq_top {s : Set E} {x : E} : egauge 𝕜 s x = ∞ ↔ ∀ c : 𝕜, x ∉ c • s := by
  simp [egauge]

lemma egauge_lt_iff {r : ℝ≥0∞} {s : Set E} {x : E} :
    egauge 𝕜 s x < r ↔ ∃ c : 𝕜, x ∈ c • s ∧ ‖c‖₊ < r := by
  simp [egauge, iInf_lt_iff]

lemma mem_of_egauge_lt_one {x : E} {s : Set E} (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) :
    x ∈ s :=
  let ⟨c, hxc, hc⟩ := egauge_lt_iff.1 hx
  hs c (mod_cast hc.le) hxc
  
variable (𝕜)

@[simp]
lemma egauge_zero_right {s : Set E} (hs : 0 ∈ s) : egauge 𝕜 s 0 = 0 := by
  simpa using egauge_le_of_mem_smul (𝕜 := 𝕜) (zero_mem_smul_set (a := 0) hs)

@[simp] lemma egauge_zero_left_eq_top {x : E} : egauge 𝕜 0 x = ∞ ↔ x ≠ 0 := by simp [egauge]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top

lemma egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0 := by simp

lemma egauge_le_one {x : E} {s : Set E} (h : x ∈ s) : egauge 𝕜 s x ≤ 1 := by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

lemma div_le_egauge_closedBall {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (r : ℝ≥0) (x : E) : ‖x‖₊ / r ≤ egauge 𝕜 (closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff, ← coe_nnnorm, NNReal.coe_le_coe] at hy
  apply ENNReal.div_le_of_le_mul
  simp only [nnnorm_smul, ENNReal.coe_mul]
  gcongr

lemma le_egauge_closedBall_one {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖x‖₊ ≤ egauge 𝕜 (closedBall 0 1) x := by
  simpa using div_le_egauge_closedBall 𝕜 1 x

lemma div_le_egauge_ball {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (r : ℝ≥0) (x : E) : ‖x‖₊ / r ≤ egauge 𝕜 (ball 0 r) x :=
  (div_le_egauge_closedBall 𝕜 r x).trans <| egauge_anti _ ball_subset_closedBall _

lemma le_egauge_ball_one {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖x‖₊ ≤ egauge 𝕜 (ball 0 1) x := by
  simpa using div_le_egauge_ball 𝕜 1 x

variable {𝕜}

lemma le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) :
    egauge 𝕜 s x / ‖c‖₊ ≤ egauge 𝕜 (c • s) x := by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← ENNReal.coe_mul, ← nnnorm_mul]
  exact egauge_le_of_mem_smul <| smul_mem_smul_set hx

lemma egauge_smul_left {c : 𝕜} (hc : c ≠ 0) (s : Set E) (x : E) :
    egauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖₊ := by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  have hc' : (‖c‖₊ : ℝ≥0∞) ≠ 0 := by simpa
  rw [ENNReal.le_div_iff_mul_le (.inl hc') (.inl ENNReal.coe_ne_top)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖₊ = egauge 𝕜 (c • s) x / ‖c⁻¹‖₊ := by
      rw [nnnorm_inv, ENNReal.coe_inv (by simpa), div_eq_mul_inv, inv_inv]
    _ ≤ egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_smul_left _ _ _
    _ = egauge 𝕜 s x := by rw [inv_smul_smul₀ hc]

lemma le_egauge_smul_right (s : Set E) (c : 𝕜) (x : E) :
    ‖c‖₊ * egauge 𝕜 s x ≤ egauge 𝕜 s (c • x) := by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine ENNReal.mul_le_of_le_div' <| le_trans ?_ ENNReal.coe_div_le
    rw [← nnnorm_div]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [div_eq_inv_mul, mul_smul, hxy, inv_smul_smul₀ hc]

lemma egauge_smul_right {s : Set E} {c : 𝕜} (h : c = 0 → 0 ∈ s) (x : E) :
    egauge 𝕜 s (c • x) = ‖c‖₊ * egauge 𝕜 s x := by
  refine le_antisymm ?_ (le_egauge_smul_right s c x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [h rfl]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl ENNReal.coe_ne_top),
      ENNReal.div_eq_inv_mul, ← ENNReal.coe_inv (by simpa), ← nnnorm_inv]
    refine (le_egauge_smul_right _ _ _).trans_eq ?_
    rw [inv_smul_smul₀ hc]

lemma egauge_ball_le_of_one_lt_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ≥0} {x : E} (h₀ : r ≠ 0 ∨ x ≠ 0) :
    egauge 𝕜 (ball 0 r) x ≤ ‖c‖₊ * ‖x‖₊ / r := by
  rcases (zero_le r).eq_or_lt with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa using h₀
  · rcases eq_or_ne x 0 with rfl | hx
    · rw [egauge_zero_right]
      exacts [zero_le _, mem_ball_self hr]
    rcases rescale_to_shell hc hr hx with ⟨a, ha₀, har, -, hainv⟩
    calc
      egauge 𝕜 (ball 0 r) x ≤ ↑(‖a‖₊⁻¹) := egauge_le_of_smul_mem_of_ne (mem_ball_zero_iff.2 har) ha₀
      _ ≤ ↑(‖c‖₊ * ‖x‖₊ / r) := by rwa [ENNReal.coe_le_coe, div_eq_inv_mul, ← mul_assoc]
      _ ≤ ‖c‖₊ * ‖x‖₊ / r := ENNReal.coe_div_le.trans <| by rw [ENNReal.coe_mul]

lemma egauge_ball_one_le_of_one_lt_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {c : 𝕜} (hc : 1 < ‖c‖) (x : E) : egauge 𝕜 (ball 0 1) x ≤ ‖c‖₊ * ‖x‖₊ := by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

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
