/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.LeftRightDeriv


open Set Filter Topology

open scoped ENNReal NNReal

variable {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}

namespace ConvexOn

lemma comp_neg {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}
    (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) := by
  refine ⟨hf.1.neg, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp_rw [neg_add_rev, ← smul_neg, add_comm]
  exact hf.2 hx hy ha hb hab

lemma comp_neg_iff {𝕜 F β : Type*} [LinearOrderedField 𝕜] [AddCommGroup F]
    [OrderedAddCommMonoid β] [Module 𝕜 F] [SMul 𝕜 β] {f : F → β} {s : Set F}  :
    ConvexOn 𝕜 (-s) (fun x ↦ f (-x)) ↔ ConvexOn 𝕜 s f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ConvexOn.comp_neg h⟩
  rw [← neg_neg s, ← Function.comp_id f, ← neg_comp_neg, ← Function.comp_assoc]
  exact h.comp_neg

section Slope

lemma monotoneOn_slope_gt (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | x < y} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne'⟩

lemma monotoneOn_slope_lt (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | y < x} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne⟩

lemma bddBelow_slope_Ioi_of_mem_interior (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ interior s) :
    BddBelow (slope f x '' {y ∈ s | x < y}) := by
  obtain ⟨y, hys, hyx⟩ : ∃ y ∈ s, y < x := by
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs
    obtain ⟨a, b, hxab, habs⟩ := hxs
    rw [mem_Ioo] at hxab
    obtain ⟨a', haa', ha'x⟩ := exists_between hxab.1
    exact ⟨a', habs ⟨haa', ha'x.trans hxab.2⟩, ha'x⟩
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine slope_mono hfc (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · simp [hys, hyx.ne]
  · simp [hz.2.ne', hz.1]

lemma bddAbove_slope_Iio_of_mem_interior (hfc : ConvexOn ℝ s f) {x : ℝ} (hxs : x ∈ interior s) :
    BddAbove (slope f x '' {y ∈ s | y < x}) := by
  obtain ⟨y, hys, hyx⟩ : ∃ y ∈ s, x < y := by
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs
    obtain ⟨a, b, hxab, habs⟩ := hxs
    rw [mem_Ioo] at hxab
    obtain ⟨b', hxb', hb'b⟩ := exists_between hxab.2
    exact ⟨b', habs ⟨hxab.1.trans hxb', hb'b⟩, hxb'⟩
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine slope_mono hfc (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · simp [hz.2.ne, hz.1]
  · simp [hys, hyx.ne']

end Slope

lemma hasDerivWithinAt_Ioi_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (sInf (slope f x '' {y ∈ s | x < y})) (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) {y ∈ s | x < y} :=
    monotoneOn_slope_gt hfc (interior_subset hxs)
  have h_bddBelow : BddBelow (slope f x '' Ioo x b) := by
    refine (bddBelow_slope_Ioi_of_mem_interior hfc hxs).mono ?_
    exact image_subset _ fun z hz ↦ ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[>] x) (𝓝 (sInf (slope f x '' Ioo x b))) := by
    refine MonotoneOn.tendsto_nhdsWithin_Ioo_right ?_ ?_ h_bddBelow
    · simpa using hxab.2
    · exact h_mono.mono fun z hz ↦ ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  suffices sInf (slope f x '' Ioo x b) = sInf (slope f x '' {y ∈ s | x < y}) by rwa [← this]
  apply le_antisymm
  · refine le_csInf ?_ fun z hz ↦ ?_
    · simp only [image_nonempty]
      obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
      exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
    · simp only [mem_image, mem_setOf_eq] at hz
      obtain ⟨y, ⟨hys, hxy⟩, rfl⟩ := hz
      obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxab.2 hxy)
      refine csInf_le_of_le (b := slope f x z) h_bddBelow ?_ ?_
      · exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, rfl⟩
      · refine monotoneOn_slope_gt hfc (interior_subset hxs) ?_ ⟨hys, hxy⟩
          (hzy.le.trans (min_le_right _ _))
        exact ⟨habs ⟨hxab.1.trans hxz, hzy.trans_le (min_le_left _ _)⟩, hxz⟩
  · refine csInf_le_csInf (bddBelow_slope_Ioi_of_mem_interior hfc hxs) ?_ ?_
    · simpa using hxab.2
    · refine image_subset _ fun z hz ↦ ?_
      exact ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩

lemma differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasDerivWithinAt_Ioi_of_mem_interior hxs).differentiableWithinAt

lemma hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (rightDeriv f x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

lemma rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    rightDeriv f x = sInf (slope f x '' {y | y ∈ s ∧ x < y}) :=
  (hfc.hasDerivWithinAt_Ioi_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma rightDeriv_le_slope (hfc : ConvexOn ℝ s f)
    {y : ℝ} (hxs : x ∈ interior s) (hys : y ∈ s) (hxy : x < y) :
    rightDeriv f x ≤ slope f x y :=
  right_deriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

lemma hasDerivWithinAt_Iio_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (sSup (slope f x '' {y ∈ s | y < x})) (Iio x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h_mono : MonotoneOn (slope f x) {y ∈ s | y < x} :=
    monotoneOn_slope_lt hfc (interior_subset hxs)
  have h_bddAbove : BddAbove (slope f x '' Ioo a x) := by
    refine (bddAbove_slope_Iio_of_mem_interior hfc hxs).mono ?_
    exact image_subset _ fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[<] x) (𝓝 (sSup (slope f x '' Ioo a x))) := by
    refine MonotoneOn.tendsto_nhdsWithin_Ioo_left ?_ ?_ h_bddAbove
    · simpa using hxab.1
    · exact h_mono.mono fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  suffices sSup (slope f x '' Ioo a x) = sSup (slope f x '' {y ∈ s | y < x}) by rwa [← this]
  apply le_antisymm
  · refine csSup_le_csSup (bddAbove_slope_Iio_of_mem_interior hfc hxs) ?_ ?_
    · simpa using hxab.1
    · refine image_subset _ fun z hz ↦ ?_
      exact ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  · refine csSup_le ?_ fun z hz ↦ ?_
    · simp only [image_nonempty]
      obtain ⟨z, haz, hzx⟩ := exists_between hxab.1
      exact ⟨z, habs ⟨haz, hzx.trans hxab.2⟩, hzx⟩
    · simp only [mem_image, mem_setOf_eq] at hz
      obtain ⟨y, ⟨hys, hyx⟩, rfl⟩ := hz
      obtain ⟨z, hxz, hzy⟩ := exists_between (max_lt hxab.1 hyx)
      refine le_csSup_of_le (b := slope f x z) h_bddAbove ?_ ?_
      · exact ⟨z, ⟨(le_max_left _ _).trans_lt hxz, hzy⟩, rfl⟩
      · refine monotoneOn_slope_lt hfc (interior_subset hxs) ⟨hys, hyx⟩ ?_
          ((le_max_right _ _).trans hxz.le)
        exact ⟨habs ⟨(le_max_left _ _).trans_lt hxz, hzy.trans hxab.2⟩, hzy⟩

lemma differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  (hfc.hasDerivWithinAt_Iio_of_mem_interior hxs).differentiableWithinAt

lemma hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    HasDerivWithinAt f (leftDeriv f x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

lemma leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    leftDeriv f x = sSup (slope f x '' {y | y ∈ s ∧ y < x}) :=
  (hfc.hasDerivWithinAt_Iio_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

lemma slope_le_leftDeriv (hfc : ConvexOn ℝ s f)
    {y : ℝ} (hxs : x ∈ interior s) (hys : y ∈ s) (hxy : y < x) :
    slope f x y ≤ leftDeriv f x := by
  rw [slope_comm]
  exact slope_le_left_deriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

lemma leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ s f) (hxs : x ∈ interior s) :
    leftDeriv f x ≤ rightDeriv f x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine csSup_le ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, haz, hzx⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨haz, hzx.trans hxab.2⟩, hzx⟩
  rintro _ ⟨z, ⟨hzs, hzx⟩, rfl⟩
  refine le_csInf ?_ ?_
  · rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  rintro _ ⟨y, ⟨hys, hxy⟩, rfl⟩
  exact slope_mono hfc (interior_subset hxs) ⟨hzs, hzx.ne⟩ ⟨hys, hxy.ne'⟩ (hzx.trans hxy).le

lemma rightDeriv_monotoneOn (hfc : ConvexOn ℝ s f) : MonotoneOn (rightDeriv f) (interior s) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_Ioi_of_mem_interior hfc hxs)
    ⟨y, by simp only [mem_setOf_eq, hxy, and_true]; exact interior_subset hys⟩
    (le_csInf ?_ ?_)
  · have hys' := hys
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hys'
    obtain ⟨a, b, hxab, habs⟩ := hys'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.2
    exact ⟨z, habs ⟨hxab.1.trans hxz, hzb⟩, hxz⟩
  · rintro _ ⟨z, ⟨hzs, hyz : y < z⟩, rfl⟩
    rw [slope_comm]
    exact slope_mono hfc (interior_subset hys) ⟨interior_subset hxs, hxy.ne⟩ ⟨hzs, hyz.ne'⟩
      (hxy.trans hyz).le

lemma leftDeriv_monotoneOn (hfc : ConvexOn ℝ s f) : MonotoneOn (leftDeriv f) (interior s) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_Iio_of_mem_interior hfc hys)
    ⟨x, by simp only [slope_comm, mem_setOf_eq, hxy, and_true]; exact interior_subset hxs⟩
    (csSup_le ?_ ?_)
  · have hxs' := hxs
    rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
    obtain ⟨a, b, hxab, habs⟩ := hxs'
    rw [image_nonempty]
    obtain ⟨z, hxz, hzb⟩ := exists_between hxab.1
    exact ⟨z, habs ⟨hxz, hzb.trans hxab.2⟩, hzb⟩
  · rintro _ ⟨z, ⟨hzs, hyz : z < x⟩, rfl⟩
    exact slope_mono hfc (interior_subset hxs) ⟨hzs, hyz.ne⟩ ⟨interior_subset hys, hxy.ne'⟩
      (hyz.trans hxy).le

lemma affine_rightDeriv_le_of_mem_interior (hf : ConvexOn ℝ s f)
    (hx : x ∈ interior s) (hy : y ∈ s) :
    rightDeriv f x * y + (f x - rightDeriv f x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : rightDeriv f x ≤ slope f x y := rightDeriv_le_slope hf hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ rightDeriv f x :=
      (slope_le_leftDeriv hf hx hy hyx).trans (leftDeriv_le_rightDeriv_of_mem_interior hf hx)
    rw [slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma affine_leftDeriv_le_of_mem_interior (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) (hy : y ∈ s) :
    leftDeriv f x * y + (f x - leftDeriv f x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : leftDeriv f x ≤ slope f x y :=
      (leftDeriv_le_rightDeriv_of_mem_interior hf hx).trans (rightDeriv_le_slope hf hx hy hxy)
    rwa [slope_def_field, le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub,
      add_sub, add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ leftDeriv f x := slope_le_leftDeriv hf hx hy hyx
    rwa [slope_def_field, ← neg_div_neg_eq, neg_sub, neg_sub, div_le_iff₀ (by simp [hyx]),
      sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add', sub_sub_eq_add_sub,
      add_sub_right_comm] at this

lemma ge_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn ℝ s f) (hx : x ∈ interior s)
    (hf_ld : leftDeriv f x ≤ 0) (hf_rd : 0 ≤ rightDeriv f x) (hy : y ∈ s) :
    f x ≤ f y := by
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 ≤ slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
    exact hf_rd.trans <| rightDeriv_le_slope hf hx hy hxy
  · simp [h_eq]
  · suffices slope f x y ≤ 0 by
      simp only [slope_def_field, div_nonpos_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hyx, and_false, or_false] at this
      exact this.1
    exact (slope_le_leftDeriv hf hx hy hyx).trans hf_ld

lemma nonneg_of_todo (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_deriv : rightDeriv f 1 = 0) (hx : 0 < x) :
    0 ≤ f x := by
  calc 0
  _ = rightDeriv f 1 * x + (f 1 - rightDeriv f 1 * 1) := by simp [hf_one, hf_deriv]
  _ ≤ f x := hf.affine_rightDeriv_le_of_mem_interior
    ((interior_Ioi (a := (0 : ℝ))).symm ▸ mem_Ioi.mpr zero_lt_one) hx

lemma nonneg_of_todo' (hf : ConvexOn ℝ (Ioi 0) f)
    (hf_one : f 1 = 0) (hf_ld : leftDeriv f 1 ≤ 0) (hf_rd : 0 ≤ rightDeriv f 1) (hx : 0 < x) :
    0 ≤ f x := by
  rw [← hf_one]
  exact ge_of_leftDeriv_nonpos_of_rightDeriv_nonneg hf (by simp) hf_ld hf_rd hx

end ConvexOn
