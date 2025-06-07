/-
Copyright (c) 2025 Daniele Bolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Bolla, David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Connected.PathConnected

/-!
# The "topologist's sine curve" is connected but not path-connected

We give an example of a closed subset `T` of `ℝ × ℝ` which is connected but not path-connected: the
closure of the set `{ (x, sin x⁻¹) | x ∈ Ioi 0 }`.

## Main results

* `TopologistsSineCurve.T_is_conn`: the set `T` is connected.
* `TopologistsSineCurve.T_is_not_path_conn`: the set `T` is not path-connected.

This formalization is part of the UniDistance Switzerland bachelor thesis of Daniele Bolla. A
similar result has also been independently formalized by Vlad Tsyrklevich
(https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/golf.20request.3A.20Topologist's.20sine.20curve).
-/

open Topology Filter Set Real

namespace TopologistsSineCurve

/-- The topologist's sine curve, i.e. the graph of `y = sin (x⁻¹)` for `0 < x`. -/
def S : Set (ℝ × ℝ) := (fun x ↦ (x, sin x⁻¹)) '' Ioi 0

/-- The vertical line segment `{ (0, y) | -1 ≤ y ≤ 1 }`, which is the set of limit points of `S`
not contained in `S` itself. -/
def Z : Set (ℝ × ℝ) := (fun y ↦ (0, y)) '' Icc (-1) 1

/-- The union of `S` and `Z` (which we will show is the closure of `S`). -/
def T : Set (ℝ × ℝ) := S ∪ Z

/-- A sequence of `x`-values tending to 0 at which the sine curve has a given `y`-coordinate. -/
noncomputable def x_seq (y : ℝ) (k : ℕ) := 1 / (arcsin y + (k + 1) * (2 * π))

lemma x_seq_pos (y : ℝ) (k : ℕ) : 0 < x_seq y k := by
  rw [x_seq, one_div_pos]
  nlinarith [pi_pos, neg_pi_div_two_le_arcsin y]

lemma x_seq_invsin {y : ℝ} (hy : y ∈ Icc (-1) 1) (k : ℕ) : sin (x_seq y k)⁻¹ = y := by
  simpa [x_seq, -Nat.cast_add, ← Nat.cast_succ] using sin_arcsin' hy

lemma x_seq_tendsto (y : ℝ) : Tendsto (x_seq y) atTop (𝓝 0) := by
  refine .comp (g := fun k : ℝ ↦ 1 / (arcsin y + (k + 1) * (2 * π))) ?_ tendsto_natCast_atTop_atTop
  simp only [div_eq_mul_inv, show 𝓝 0 = 𝓝 (1 * (0 : ℝ)) by simp]
  refine (tendsto_inv_atTop_zero.comp <| tendsto_atTop_add_const_left _ _ ?_).const_mul _
  exact (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_mul_const (by positivity)

/-!
## `T` is closed
-/
/-- The closure of the topologist's sine curve `S` is the set `T`. -/
lemma closure_S : closure S = T := by
  ext ⟨x, y⟩
  -- Use sequential characterization of closure.
  simp only [mem_closure_iff_seq_limit, Prod.tendsto_iff]
  constructor
  · -- Show that if a sequence in `S` has a limit in `ℝ ^ 2`, the limit must be in `T`.
    rintro ⟨f, hf_mem, hf_lim⟩
    have x_nonneg : 0 ≤ x := by
      refine isClosed_Ici.mem_of_tendsto hf_lim.1 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa [← hy.2] using le_of_lt hy.1
    -- Case split on whether limit point `(x, y)` has `x = 0`.
    rcases x_nonneg.eq_or_lt with rfl | h
    · -- If the limit has `x = 0`, show `y`-coord must be in `[-1, 1]` using closedness
      right
      simp only [Z, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
      refine isClosed_Icc.mem_of_tendsto hf_lim.2 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa only [Function.comp_apply, ← hy.2] using sin_mem_Icc ..
    · -- If the limit has `0 < x`, show `y`-coord must be `sin x⁻¹` using continuity
      refine .inl ⟨x, h, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      have : ContinuousAt (fun x ↦ sin x⁻¹) x :=
        continuous_sin.continuousAt.comp <| continuousAt_inv₀ h.ne'
      refine tendsto_nhds_unique ?_ hf_lim.2
      convert this.tendsto.comp hf_lim.1 with n
      obtain ⟨y, hy⟩ := hf_mem n
      simp [← hy.2]
  · -- Show that every `p ∈ T` is the limit of a sequence in `S`.
    rintro (hz | ⟨z, hz⟩)
    · -- Point is in `S`: use constant sequence
      exact ⟨_, fun _ ↦ hz, tendsto_const_nhds, tendsto_const_nhds⟩
    · -- Point is in `Z`: use sequence from `x_seq`
      simp only [Prod.mk.injEq] at hz
      rcases hz with ⟨hz, ⟨rfl, rfl⟩⟩
      refine ⟨fun n ↦ (x_seq z n, z), fun n ↦ ⟨_, x_seq_pos z n, ?_⟩, x_seq_tendsto z,
        tendsto_const_nhds⟩
      simpa using x_seq_invsin hz n

lemma isClosed_T : IsClosed T := by simpa only [← closure_S] using isClosed_closure

/-!
## `T` is connected
-/
/-- `T` is connected, being the closure of the set `S` (which is obviously connected since it
is a continuous image of the positive real line). -/
theorem T_is_conn : IsConnected T := by
  rw [← closure_S]
  refine (isConnected_Ioi.image _ <| continuousOn_id.prodMk ?_).closure
  exact continuous_sin.comp_continuousOn <| continuousOn_inv₀.mono fun _ hx ↦ hx.ne'

/-!
## `T` is not path-connected
-/

lemma zero_mem_T : (0, 0) ∈ T := by
  refine .inr ⟨0, ⟨?_, ?_⟩, rfl⟩ <;>
  linarith

/-- A point in the `body` of the topologist's sine curve. -/
noncomputable def w : ℝ × ℝ := (1, sin 1⁻¹)

lemma w_mem_T : w ∈ T := .inl ⟨1, ⟨zero_lt_one' ℝ, rfl⟩⟩

private lemma norm_ge_abs_snd {a b : ℝ} : |b| ≤ ‖(a, b)‖ := by simp

private lemma exists_unitInterval_gt {t₀ : unitInterval} (ht₀ : t₀ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
  let s₀ := (t₀ : ℝ) -- t₀ is in unitInterval
  let s₁ := min (s₀ + δ/2) 1
  have h_s₀_delta_pos : 0 ≤ s₀ + δ/2 := add_nonneg t₀.2.1 (by positivity)
  have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
  have hs₁': s₁ ≤ 1 := min_le_right ..
  refine ⟨⟨s₁, hs₁, hs₁'⟩, lt_min ((lt_add_iff_pos_right _).mpr (half_pos hδ)) ht₀, ?_⟩
  have h_le : s₁ ≤ s₀ + δ/2 := min_le_left _ _
  have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
  rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-- The set `T` is not path-connected. -/
theorem T_is_not_path_conn : ¬ IsPathConnected T := by
  -- **Step 1**:
  -- Assume for contradiction we have a path from `z = (0, 0)` to `w = (1, sin 1)`.
  -- Let t₀ be the last time the path is on the y-axis. By continuity of the path, we
  -- can find a `δ > 0` such that for all `t ∈ [t₀, t₀ + δ]`, we have `‖p(t) - p(t₀)‖ < 1`.
  intro h_pathConn
  replace h_pathConn := h_pathConn.joinedIn (0, 0) zero_mem_T w w_mem_T
  let p := h_pathConn.somePath
  have xcoord_pathContinuous : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_pathContinuous).sSup_mem ⟨0, by aesop⟩
  obtain ⟨δ , hδ, ht⟩ : ∃ δ, 0 < δ ∧ ∀ t, dist t t₀ < δ → dist (p t) (p t₀) < 1 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_pos
  -- **Step 2**:
  -- Choose a time t₁ in (t₀, t₀ + δ) and let `a = x(p(t₁))`. Using the fact that every
  -- connected subset of `ℝ` is an interval, we have `[0, a] ⊂ x(p([t0, t1]))`.
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
    refine exists_unitInterval_gt (lt_of_le_of_ne (unitInterval.le_one t₀) fun ht₀' ↦ ?_) hδ
    have w_x_path : (p 1).1 = 1 := by simp [w]
    have x_eq_zero : (p 1).1 = 0 := by rwa [ht₀'] at h_pt₀_x
    linarith
  let a := (p t₁).1
  have ha : 0 < a := by
    obtain ⟨x, hxI, hx_eq⟩ : p t₁ ∈ S := by
      refine (h_pathConn.somePath_mem t₁).elim id fun ⟨y, hy⟩ ↦ ?_
      have : (p t₁).1 = 0 := by simp only [p, ← hy.2]
      exact ((show t₁ ≤ t₀ from le_sSup this).not_lt ht₁.1).elim
    simpa only [a, ← hx_eq] using hxI
  have intervalAZeroSubOfT₀T₁Xcoord : Icc 0 a ⊆ (fun t ↦ (p t).1) '' Icc t₀ t₁ :=
    (isPreconnected_Icc.image _ <| xcoord_pathContinuous.continuousOn).Icc_subset
      (show 0 ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₀, ⟨le_rfl, ht₁.1.le⟩, ‹_›⟩)
      (show a ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₁, ⟨ht₁.1.le, le_rfl⟩, rfl⟩)
  -- **Step 3**:
  -- For every `y ∈ [-1, 1]`, there exists a `t` with `p t = y` and `t ∈ [t₀, t₁]`, implying
  -- that `dist t₀ t < δ`.
  -- first find an appropriate `t`-value
  have exists_in_interval {y : ℝ} (hy : y ∈ Icc (-1) 1) : ∃ t ∈ Icc t₀ t₁, (p t).2 = y := by
    obtain ⟨i, hi⟩ :  ∃ i, x_seq y i ∈ Icc 0 a := by
      obtain ⟨N, h_dist⟩ := (Metric.tendsto_nhds.mp (x_seq_tendsto y) (a/2) (by positivity)).exists
      refine ⟨N, (x_seq_pos y N).le, ?_⟩
      rw [dist_eq, sub_zero, abs_of_pos (x_seq_pos _ N)] at h_dist
      linarith
    obtain ⟨t, ht⟩ := intervalAZeroSubOfT₀T₁Xcoord hi
    refine ⟨t, ht.1, ?_⟩
    suffices (p t).2 = sin (x_seq y i)⁻¹ from this ▸ x_seq_invsin hy i
    obtain ⟨xpos_real, hxInpos_real, h_eq_path⟩ : p t ∈ S := by
      cases h_pathConn.somePath_mem t with
      | inl hS => exact hS
      | inr hZ =>
        obtain ⟨y, hy⟩ := hZ
        have h_x_zero : (p t).1 = 0 := by simp [p, ← hy.2]
        have h_x_pos : 0 < (p t).1 := by simpa [ht.2] using x_seq_pos ..
        linarith
    have xIsSeq : xpos_real = x_seq y i := (congrArg Prod.fst h_eq_path).trans ht.2
    rw [← h_eq_path, xIsSeq]
  -- then show it lies within `δ` of `t₀`.
  have exists_close (y : ℝ) (hy : y ∈ Icc (-1) 1) : ∃ t, dist t t₀ < δ ∧ (p t).2 = y := by
    obtain ⟨t, ht, hty⟩ : ∃ t ∈ Icc t₀ t₁, (p t).2 = y := exists_in_interval hy
    refine ⟨t, ?_, hty⟩
    calc
    dist t t₀ ≤ dist t₁ t₀ := by
      simp only [Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_nonneg, abs_of_nonneg]
      · simpa using ht.2
      · linarith [Subtype.coe_lt_coe.mpr ht₁.1]
      · simpa using mod_cast ht.1
    _ = dist t₀ t₁ := by rw [dist_comm]
    _ < δ := ht₁.2
  -- **Step 4**:
  -- Now the final contradiction: there are times within `δ` of `t₀` with `p t = 1`, and with
  -- `p t = -1`; but both must have distance `< 1` from `p t₀`, contradicting the triangle
  -- inequality.
  obtain ⟨x₁, hx₁, h_pathx₁⟩ : ∃ x₁, dist x₁ t₀ < δ ∧ (p x₁).2 = 1 := exists_close _ (by simp)
  obtain ⟨x₂, hx₂, h_pathx₂⟩ : ∃ x₂, dist x₂ t₀ < δ ∧ (p x₂).2 = -1 := exists_close _ (by simp)
  have : dist (p x₁) (p x₂) < 2 := by
    refine (dist_triangle_right _ _ (p t₀)).trans_lt ?_
    exact (add_lt_add (ht _ hx₁) (ht _ hx₂)).trans_eq (by norm_num)
  have := norm_ge_abs_snd.trans_lt this
  rw [h_pathx₁, h_pathx₂, abs_of_nonneg (by norm_num)] at this
  linarith

end TopologistsSineCurve
