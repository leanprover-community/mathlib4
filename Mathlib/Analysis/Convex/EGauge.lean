/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Seminorm
import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# The Minkowski functional, normed field version

In this file we define `(egauge 𝕜 s ·)`
to be the Minkowski functional (gauge) of the set `s`
in a topological vector space `E` over a normed field `𝕜`,
as a function `E → ℝ≥0∞`.

It is defined as the infimum of the norms of `c : 𝕜` such that `x ∈ c • s`.
In particular, for `𝕜 = ℝ≥0` this definition gives an `ℝ≥0∞`-valued version of `gauge`
defined in `Mathlib/Analysis/Convex/Gauge.lean`.

This definition can be used to generalize the notion of Fréchet derivative
to maps between topological vector spaces without norms.

Currently, we can't reuse results about `egauge` for `gauge`,
because we lack a theory of normed semifields.
-/

open Function Set Filter Metric
open scoped Topology Pointwise ENNReal NNReal

section SMul

/-- The Minkowski functional for vector spaces over normed fields.
Given a set `s` in a vector space over a normed field `𝕜`,
`egauge s` is the functional which sends `x : E`
to the infimum of `‖c‖ₑ` over `c` such that `x` belongs to `s` scaled by `c`.

The definition only requires `𝕜` to have a `ENorm` instance
and `(· • ·) : 𝕜 → E → E` to be defined.
This way the definition applies, e.g., to `𝕜 = ℝ≥0`.
For `𝕜 = ℝ≥0`, the function is equal (up to conversion to `ℝ`)
to the usual Minkowski functional defined in `gauge`. -/
noncomputable def egauge (𝕜 : Type*) [ENorm 𝕜] {E : Type*} [SMul 𝕜 E] (s : Set E) (x : E) : ℝ≥0∞ :=
  ⨅ (c : 𝕜) (_ : x ∈ c • s), ‖c‖ₑ

variable (𝕜 : Type*) [NNNorm 𝕜] {E : Type*} [SMul 𝕜 E] {c : 𝕜} {s t : Set E} {x : E} {r : ℝ≥0∞}

lemma Set.MapsTo.egauge_le {E' F : Type*} [SMul 𝕜 E'] [FunLike F E E'] [MulActionHomClass F 𝕜 E E']
    (f : F) {t : Set E'} (h : MapsTo f s t) (x : E) : egauge 𝕜 t (f x) ≤ egauge 𝕜 s x :=
  iInf_mono fun c ↦ iInf_mono' fun hc ↦ ⟨h.smul_set c hc, le_rfl⟩

@[mono, gcongr]
lemma egauge_anti (h : s ⊆ t) (x : E) : egauge 𝕜 t x ≤ egauge 𝕜 s x :=
  MapsTo.egauge_le _ (MulActionHom.id ..) h _

@[simp] lemma egauge_empty (x : E) : egauge 𝕜 ∅ x = ∞ := by simp [egauge]

variable {𝕜}

lemma egauge_le_of_mem_smul (h : x ∈ c • s) : egauge 𝕜 s x ≤ ‖c‖ₑ := iInf₂_le c h

lemma le_egauge_iff : r ≤ egauge 𝕜 s x ↔ ∀ c : 𝕜, x ∈ c • s → r ≤ ‖c‖ₑ := le_iInf₂_iff

lemma egauge_eq_top : egauge 𝕜 s x = ∞ ↔ ∀ c : 𝕜, x ∉ c • s := by simp [egauge]

lemma egauge_lt_iff : egauge 𝕜 s x < r ↔ ∃ c : 𝕜, x ∈ c • s ∧ ‖c‖ₑ < r := by
  simp [egauge, iInf_lt_iff]

lemma egauge_union (s t : Set E) (x : E) : egauge 𝕜 (s ∪ t) x = egauge 𝕜 s x ⊓ egauge 𝕜 t x := by
  unfold egauge
  simp [smul_set_union, iInf_or, iInf_inf_eq]

lemma le_egauge_inter (s t : Set E) (x : E) :
    egauge 𝕜 s x ⊔ egauge 𝕜 t x ≤ egauge 𝕜 (s ∩ t) x :=
  max_le (egauge_anti _ inter_subset_left _) (egauge_anti _ inter_subset_right _)

lemma le_egauge_pi {ι : Type*} {E : ι → Type*} [∀ i, SMul 𝕜 (E i)] {I : Set ι} {i : ι}
    (hi : i ∈ I) (s : ∀ i, Set (E i)) (x : ∀ i, E i) :
    egauge 𝕜 (s i) (x i) ≤ egauge 𝕜 (I.pi s) x :=
  MapsTo.egauge_le _ (Pi.evalMulActionHom i) (fun x hx ↦ by exact hx i hi) _

variable {F : Type*} [SMul 𝕜 F]

lemma le_egauge_prod (s : Set E) (t : Set F) (a : E) (b : F) :
    max (egauge 𝕜 s a) (egauge 𝕜 t b) ≤ egauge 𝕜 (s ×ˢ t) (a, b) :=
  max_le (mapsTo_fst_prod.egauge_le 𝕜 (MulActionHom.fst 𝕜 E F) (a, b))
    (MapsTo.egauge_le 𝕜 (MulActionHom.snd 𝕜 E F) mapsTo_snd_prod (a, b))

end SMul

section SMulZero

variable (𝕜 : Type*) [NNNorm 𝕜] [Nonempty 𝕜] {E : Type*} [Zero E] [SMulZeroClass 𝕜 E] {x : E}

@[simp] lemma egauge_zero_left_eq_top : egauge 𝕜 0 x = ∞ ↔ x ≠ 0 := by
  simp [egauge_eq_top]

@[simp] alias ⟨_, egauge_zero_left⟩ := egauge_zero_left_eq_top

end SMulZero

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    {c : 𝕜} {s : Set E} {x : E}

/-- If `c • x ∈ s` and `c ≠ 0`, then `egauge 𝕜 s x` is at most `(‖c‖₊⁻¹ : ℝ≥0)`.

See also `egauge_le_of_smul_mem`. -/
lemma egauge_le_of_smul_mem_of_ne (h : c • x ∈ s) (hc : c ≠ 0) : egauge 𝕜 s x ≤ (‖c‖₊⁻¹ : ℝ≥0) := by
  rw [← nnnorm_inv]
  exact egauge_le_of_mem_smul <| (mem_inv_smul_set_iff₀ hc _ _).2 h

/-- If `c • x ∈ s`, then `egauge 𝕜 s x` is at most `‖c‖ₑ⁻¹`.

See also `egauge_le_of_smul_mem_of_ne`. -/
lemma egauge_le_of_smul_mem (h : c • x ∈ s) : egauge 𝕜 s x ≤ ‖c‖ₑ⁻¹ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (egauge_le_of_smul_mem_of_ne h hc).trans ENNReal.coe_inv_le

lemma mem_smul_of_egauge_lt (hs : Balanced 𝕜 s) (hc : egauge 𝕜 s x < ‖c‖ₑ) : x ∈ c • s :=
  let ⟨a, hxa, ha⟩ := egauge_lt_iff.1 hc
  hs.smul_mono (by simpa [enorm] using ha.le) hxa

lemma mem_of_egauge_lt_one (hs : Balanced 𝕜 s) (hx : egauge 𝕜 s x < 1) : x ∈ s :=
  one_smul 𝕜 s ▸ mem_smul_of_egauge_lt hs (by simpa)

lemma egauge_eq_zero_iff : egauge 𝕜 s x = 0 ↔ ∃ᶠ c : 𝕜 in 𝓝 0, x ∈ c • s := by
  refine (iInf₂_eq_bot _).trans ?_
  rw [(nhds_basis_uniformity uniformity_basis_edist).frequently_iff]
  simp [and_comm]

@[simp]
lemma egauge_univ [(𝓝[≠] (0 : 𝕜)).NeBot] : egauge 𝕜 univ x = 0 := by
  rw [egauge_eq_zero_iff]
  refine (frequently_iff_neBot.2 ‹_›).mono fun c hc ↦ ?_
  simp_all [smul_set_univ₀]

variable (𝕜)

@[simp]
lemma egauge_zero_right (hs : s.Nonempty) : egauge 𝕜 s 0 = 0 := by
  have : 0 ∈ (0 : 𝕜) • s := by simp [zero_smul_set hs]
  simpa using egauge_le_of_mem_smul this

lemma egauge_zero_zero : egauge 𝕜 (0 : Set E) 0 = 0 := by simp

lemma egauge_le_one (h : x ∈ s) : egauge 𝕜 s x ≤ 1 := by
  rw [← one_smul 𝕜 s] at h
  simpa using egauge_le_of_mem_smul h

variable {𝕜}

lemma le_egauge_smul_left (c : 𝕜) (s : Set E) (x : E) :
    egauge 𝕜 s x / ‖c‖ₑ ≤ egauge 𝕜 (c • s) x := by
  simp_rw [le_egauge_iff, smul_smul]
  rintro a ⟨x, hx, rfl⟩
  apply ENNReal.div_le_of_le_mul
  rw [← enorm_mul]
  exact egauge_le_of_mem_smul <| smul_mem_smul_set hx

lemma egauge_smul_left (hc : c ≠ 0) (s : Set E) (x : E) :
    egauge 𝕜 (c • s) x = egauge 𝕜 s x / ‖c‖ₑ := by
  refine le_antisymm ?_ (le_egauge_smul_left _ _ _)
  rw [ENNReal.le_div_iff_mul_le (by simp [*]) (by simp)]
  calc
    egauge 𝕜 (c • s) x * ‖c‖ₑ = egauge 𝕜 (c • s) x / ‖c⁻¹‖ₑ := by
      rw [enorm_inv (by simpa), div_eq_mul_inv, inv_inv]
    _ ≤ egauge 𝕜 (c⁻¹ • c • s) x := le_egauge_smul_left _ _ _
    _ = egauge 𝕜 s x := by rw [inv_smul_smul₀ hc]

lemma le_egauge_smul_right (c : 𝕜) (s : Set E) (x : E) :
    ‖c‖ₑ * egauge 𝕜 s x ≤ egauge 𝕜 s (c • x) := by
  rw [le_egauge_iff]
  rintro a ⟨y, hy, hxy⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine ENNReal.mul_le_of_le_div' <| le_trans ?_ ENNReal.coe_div_le
    rw [div_eq_inv_mul, ← nnnorm_inv, ← nnnorm_mul]
    refine egauge_le_of_mem_smul ⟨y, hy, ?_⟩
    simp only [mul_smul, hxy, inv_smul_smul₀ hc]

lemma egauge_smul_right (h : c = 0 → s.Nonempty) (x : E) :
    egauge 𝕜 s (c • x) = ‖c‖ₑ * egauge 𝕜 s x := by
  refine le_antisymm ?_ (le_egauge_smul_right c s x)
  rcases eq_or_ne c 0 with rfl | hc
  · simp [egauge_zero_right _ (h rfl)]
  · rw [mul_comm, ← ENNReal.div_le_iff_le_mul (.inl <| by simpa) (.inl enorm_ne_top),
      ENNReal.div_eq_inv_mul, ← enorm_inv (by simpa)]
    refine (le_egauge_smul_right _ _ _).trans_eq ?_
    rw [inv_smul_smul₀ hc]

/-- The extended gauge of a point `(a, b)` with respect to the product of balanced sets `U` and `V`
is equal to the maximum of the extended gauges of `a` with respect to `U`
and `b` with respect to `V`.
-/
theorem egauge_prod_mk {F : Type*} [AddCommGroup F] [Module 𝕜 F] {U : Set E} {V : Set F}
    (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a : E) (b : F) :
    egauge 𝕜 (U ×ˢ V) (a, b) = max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  refine le_antisymm (le_of_forall_gt fun r hr ↦ ?_) (le_egauge_prod _ _ _ _)
  simp only [max_lt_iff, egauge_lt_iff, smul_set_prod, mk_mem_prod] at hr ⊢
  rcases hr with ⟨⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
  cases le_total ‖x‖ ‖y‖ with
  | inl hle => exact ⟨y, ⟨hU.smul_mono hle hx, hy⟩, hyr⟩
  | inr hle => exact ⟨x, ⟨hx, hV.smul_mono hle hy⟩, hxr⟩

theorem egauge_add_add_le {U V : Set E} (hU : Balanced 𝕜 U) (hV : Balanced 𝕜 V) (a b : E) :
    egauge 𝕜 (U + V) (a + b) ≤ max (egauge 𝕜 U a) (egauge 𝕜 V b) := by
  rw [← egauge_prod_mk hU hV a b, ← add_image_prod]
  exact MapsTo.egauge_le 𝕜 (LinearMap.fst 𝕜 E E + LinearMap.snd 𝕜 E E) (mapsTo_image _ _) (a, b)

end NormedDivisionRing

section Pi

variable {𝕜 : Type*} {ι : Type*} {E : ι → Type*}
variable [NormedDivisionRing 𝕜] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]

/-- The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes the following technical condition:
- either `I` is the universal set;
- or one of `x i`, `i ∈ I`, is nonzero;
- or `𝕜` is nontrivially normed.
-/
theorem egauge_pi' {I : Set ι} (hI : I.Finite)
    {U : ∀ i, Set (E i)} (hU : ∀ i ∈ I, Balanced 𝕜 (U i))
    (x : ∀ i, E i) (hI₀ : I = univ ∨ (∃ i ∈ I, x i ≠ 0) ∨ (𝓝[≠] (0 : 𝕜)).NeBot) :
    egauge 𝕜 (I.pi U) x = ⨆ i ∈ I, egauge 𝕜 (U i) (x i) := by
  refine le_antisymm ?_ (iSup₂_le fun i hi ↦ le_egauge_pi hi _ _)
  refine le_of_forall_gt fun r hr ↦ ?_
  have : ∀ i ∈ I, ∃ c : 𝕜, x i ∈ c • U i ∧ ‖c‖ₑ < r := fun i hi ↦
    egauge_lt_iff.mp <| (le_iSup₂ i hi).trans_lt hr
  choose! c hc hcr using this
  obtain ⟨c₀, hc₀, hc₀I, hc₀r⟩ :
      ∃ c₀ : 𝕜, (c₀ ≠ 0 ∨ I = univ) ∧ (∀ i ∈ I, ‖c i‖ ≤ ‖c₀‖) ∧ ‖c₀‖ₑ < r := by
    have hr₀ : 0 < r := hr.bot_lt
    rcases I.eq_empty_or_nonempty with rfl | hIne
    · obtain hι | hbot : IsEmpty ι ∨ (𝓝[≠] (0 : 𝕜)).NeBot := by simpa [@eq_comm _ ∅] using hI₀
      · use 0
        simp [@eq_comm _ ∅, hι, hr₀]
      · rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₀, hc₀, hc₀r⟩
        exact ⟨c₀, .inl hc₀, by simp, hc₀r⟩
    · obtain ⟨i₀, hi₀I, hc_max⟩ : ∃ i₀ ∈ I, IsMaxOn (‖c ·‖ₑ) I i₀ :=
        exists_max_image _ (‖c ·‖ₑ) hI hIne
      by_cases H : c i₀ ≠ 0 ∨ I = univ
      · exact ⟨c i₀, H, fun i hi ↦ by simpa [enorm] using hc_max hi, hcr _ hi₀I⟩
      · push_neg at H
        have hc0 (i : ι) (hi : i ∈ I) : c i = 0 := by simpa [H] using hc_max hi
        have heg0 (i : ι) (hi : i ∈ I) : x i = 0 :=
          zero_smul_set_subset (α := 𝕜) (U i) (hc0 i hi ▸ hc i hi)
        have : (𝓝[≠] (0 : 𝕜)).NeBot := (hI₀.resolve_left H.2).resolve_left (by simpa)
        rcases exists_enorm_lt 𝕜 hr₀.ne' with ⟨c₁, hc₁, hc₁r⟩
        refine ⟨c₁, .inl hc₁, fun i hi ↦ ?_, hc₁r⟩
        simp [hc0 i hi]
  refine egauge_lt_iff.2 ⟨c₀, ?_, hc₀r⟩
  rw [smul_set_pi₀' hc₀]
  intro i hi
  exact (hU i hi).smul_mono (hc₀I i hi) (hc i hi)

/-- The extended gauge of a point `x` in an indexed product with finite index type
with respect to a product of balanced sets `U i`,
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.
-/
theorem egauge_univ_pi [Finite ι] {U : ∀ i, Set (E i)} (hU : ∀ i, Balanced 𝕜 (U i)) (x : ∀ i, E i) :
    egauge 𝕜 (univ.pi U) x = ⨆ i, egauge 𝕜 (U i) (x i) :=
  egauge_pi' finite_univ (fun i _ ↦ hU i) x (.inl rfl) |>.trans <| by simp

/-- The extended gauge of a point `x` in an indexed product
with respect to a product of finitely many balanced sets `U i`, `i ∈ I`,
(and the whole spaces for the other indices)
is the supremum of the extended gauges of the components of `x`
with respect to the corresponding balanced set.

This version assumes that `𝕜` is a nontrivially normed division ring.
See also `egauge_univ_pi` for when `s = univ`,
and `egauge_pi'` for a version with more choices of the technical assumptions.
-/
theorem egauge_pi [(𝓝[≠] (0 : 𝕜)).NeBot] {I : Set ι} {U : ∀ i, Set (E i)}
    (hI : I.Finite) (hU : ∀ i ∈ I, Balanced 𝕜 (U i)) (x : ∀ i, E i) :
    egauge 𝕜 (I.pi U) x = ⨆ i ∈ I, egauge 𝕜 (U i) (x i) :=
  egauge_pi' hI hU x <| .inr <| .inr inferInstance

end Pi

section SeminormedAddCommGroup

variable (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma div_le_egauge_closedBall (r : ℝ≥0) (x : E) : ‖x‖ₑ / r ≤ egauge 𝕜 (closedBall 0 r) x := by
  rw [le_egauge_iff]
  rintro c ⟨y, hy, rfl⟩
  rw [mem_closedBall_zero_iff, ← coe_nnnorm, NNReal.coe_le_coe] at hy
  rw [enorm_smul]
  apply ENNReal.div_le_of_le_mul
  gcongr
  rwa [enorm_le_coe]

lemma le_egauge_closedBall_one (x : E) : ‖x‖ₑ ≤ egauge 𝕜 (closedBall 0 1) x := by
  simpa using div_le_egauge_closedBall 𝕜 1 x

lemma div_le_egauge_ball (r : ℝ≥0) (x : E) : ‖x‖ₑ / r ≤ egauge 𝕜 (ball 0 r) x :=
  (div_le_egauge_closedBall 𝕜 r x).trans <| egauge_anti _ ball_subset_closedBall _

lemma le_egauge_ball_one (x : E) : ‖x‖ₑ ≤ egauge 𝕜 (ball 0 1) x := by
  simpa using div_le_egauge_ball 𝕜 1 x

variable {𝕜}
variable {c : 𝕜} {x : E} {r : ℝ≥0}

lemma egauge_ball_le_of_one_lt_norm (hc : 1 < ‖c‖) (h₀ : r ≠ 0 ∨ ‖x‖ ≠ 0) :
    egauge 𝕜 (ball 0 r) x ≤ ‖c‖ₑ * ‖x‖ₑ / r := by
  letI : NontriviallyNormedField 𝕜 := ⟨c, hc⟩
  rcases (zero_le r).eq_or_lt with rfl | hr
  · rw [ENNReal.coe_zero, ENNReal.div_zero (mul_ne_zero _ _)]
    · apply le_top
    · simpa using one_pos.trans hc
    · simpa [enorm, ← NNReal.coe_eq_zero] using h₀
  · rcases eq_or_ne ‖x‖ 0 with hx | hx
    · have hx' : ‖x‖ₑ = 0 := by simpa [enorm, ← coe_nnnorm, NNReal.coe_eq_zero] using hx
      simp only [hx', mul_zero, ENNReal.zero_div, nonpos_iff_eq_zero, egauge_eq_zero_iff]
      refine (frequently_iff_neBot.2 (inferInstance : NeBot (𝓝[≠] (0 : 𝕜)))).mono fun c hc ↦ ?_
      simp [mem_smul_set_iff_inv_smul_mem₀ hc, norm_smul, hx, hr]
    · rcases rescale_to_shell_semi_normed hc hr hx with ⟨a, ha₀, har, -, hainv⟩
      calc
        egauge 𝕜 (ball 0 r) x ≤ ↑(‖a‖₊⁻¹) :=
          egauge_le_of_smul_mem_of_ne (mem_ball_zero_iff.2 har) ha₀
        _ ≤ ↑(‖c‖₊ * ‖x‖₊ / r) := by rwa [ENNReal.coe_le_coe, div_eq_inv_mul, ← mul_assoc]
        _ ≤ ‖c‖ₑ * ‖x‖ₑ / r := ENNReal.coe_div_le.trans <| by simp [ENNReal.coe_mul, enorm]

lemma egauge_ball_one_le_of_one_lt_norm (hc : 1 < ‖c‖) (x : E) :
    egauge 𝕜 (ball 0 1) x ≤ ‖c‖ₑ * ‖x‖ₑ := by
  simpa using egauge_ball_le_of_one_lt_norm hc (.inl one_ne_zero)

end SeminormedAddCommGroup
