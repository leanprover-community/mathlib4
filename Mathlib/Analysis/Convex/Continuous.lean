/-
Copyright (c) 2023 Yaël Dillies, Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Convex functions are continuous

This file proves that a convex function from a finite-dimensional real normed space to `ℝ` is
continuous.
-/

public section

open FiniteDimensional Metric Set List Bornology
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E} {f : E → ℝ} {x₀ : E} {ε r r' M : ℝ}

lemma ConvexOn.lipschitzOnWith_of_abs_le (hf : ConvexOn ℝ (ball x₀ r) f) (hε : 0 < ε)
    (hM : ∀ a, dist a x₀ < r → |f a| ≤ M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
  set K := 2 * M / ε with hK
  have oneside {x y : E} (hx : x ∈ ball x₀ (r - ε)) (hy : y ∈ ball x₀ (r - ε)) :
      f x - f y ≤ K * ‖x - y‖ := by
    obtain rfl | hxy := eq_or_ne x y
    · simp
    have hx₀r : ball x₀ (r - ε) ⊆ ball x₀ r := ball_subset_ball <| by linarith
    have hx' : x ∈ ball x₀ r := hx₀r hx
    have hy' : y ∈ ball x₀ r := hx₀r hy
    let z := x + (ε / ‖x - y‖) • (x - y)
    replace hxy : 0 < ‖x - y‖ := by rwa [norm_sub_pos_iff]
    have hz : z ∈ ball x₀ r := mem_ball_iff_norm.2 <| by
      calc
        _ = ‖(x - x₀) + (ε / ‖x - y‖) • (x - y)‖ := by simp only [z, add_sub_right_comm]
        _ ≤ ‖x - x₀‖ + ‖(ε / ‖x - y‖) • (x - y)‖ := norm_add_le ..
        _ < r - ε + ε :=
          add_lt_add_of_lt_of_le (mem_ball_iff_norm.1 hx) <| by
            simp [norm_smul, abs_of_nonneg, hε.le, hxy.ne']
        _ = r := by simp
    let a := ε / (ε + ‖x - y‖)
    let b := ‖x - y‖ / (ε + ‖x - y‖)
    have hab : a + b = 1 := by simp [field, a, b]
    have hxyz : x = a • y + b • z := by
      calc
        x = a • x + b • x := by rw [Convex.combo_self hab]
        _ = a • y + b • z := by simp [z, a, b, smul_smul, hxy.ne', smul_sub]; abel
    rw [hK, mul_comm, ← mul_div_assoc, le_div_iff₀' hε]
    calc
      ε * (f x - f y) ≤ ‖x - y‖ * (f z - f x) := by
        have h := hf.2 hy' hz (by positivity) (by positivity) hab
        simp only [← hxyz, smul_eq_mul, a, b] at h
        field_simp at h
        linear_combination h
      _ ≤ _ := by
        rw [sub_eq_add_neg (f _), two_mul]
        gcongr
        · exact (le_abs_self _).trans <| hM _ hz
        · exact (neg_le_abs _).trans <| hM _ hx'
  refine .of_dist_le' fun x hx y hy ↦ ?_
  simp_rw [dist_eq_norm_sub, Real.norm_eq_abs, abs_sub_le_iff]
  exact ⟨oneside hx hy, norm_sub_rev x _ ▸ oneside hy hx⟩

lemma ConcaveOn.lipschitzOnWith_of_abs_le (hf : ConcaveOn ℝ (ball x₀ r) f) (hε : 0 < ε)
    (hM : ∀ a, dist a x₀ < r → |f a| ≤ M) :
    LipschitzOnWith (2 * M / ε).toNNReal f (ball x₀ (r - ε)) := by
  simpa using hf.neg.lipschitzOnWith_of_abs_le hε <| by simpa using hM

lemma ConvexOn.exists_lipschitzOnWith_of_isBounded (hf : ConvexOn ℝ (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : ∃ K, LipschitzOnWith K f (ball x₀ r') := by
  rw [isBounded_iff_subset_ball 0] at hf'
  simp only [Set.subset_def, mem_image, mem_ball, dist_zero_right, Real.norm_eq_abs,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hf'
  obtain ⟨M, hM⟩ := hf'
  rw [← sub_sub_cancel r r']
  exact ⟨_, hf.lipschitzOnWith_of_abs_le (sub_pos.2 hr) fun a ha ↦ (hM a ha).le⟩

lemma ConcaveOn.exists_lipschitzOnWith_of_isBounded (hf : ConcaveOn ℝ (ball x₀ r) f) (hr : r' < r)
    (hf' : IsBounded (f '' ball x₀ r)) : ∃ K, LipschitzOnWith K f (ball x₀ r') := by
  replace hf' : IsBounded ((-f) '' ball x₀ r) := by convert hf'.neg; ext; simp [neg_eq_iff_eq_neg]
  simpa using hf.neg.exists_lipschitzOnWith_of_isBounded hr hf'

set_option backward.isDefEq.respectTransparency false in
lemma ConvexOn.isBoundedUnder_abs (hf : ConvexOn ℝ C f) {x₀ : E} (hC : C ∈ 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· ≤ ·) f := by
  refine ⟨fun h ↦ h.mono_le <| .of_forall fun x ↦ le_abs_self _, ?_⟩
  rintro ⟨r, hr⟩
  refine ⟨|r| + 2 * |f x₀|, ?_⟩
  have : (𝓝 x₀).Tendsto (fun y => 2 • x₀ - y) (𝓝 x₀) :=
    tendsto_nhds_nhds.2 (⟨·, ·, by simp [two_nsmul, dist_comm]⟩)
  simp only [Filter.eventually_map, Pi.abs_apply, abs_le'] at hr ⊢
  filter_upwards [this.eventually_mem hC, hC, hr, this.eventually hr] with y hx hx' hfr hfr'
  refine ⟨hfr.trans <| (le_abs_self _).trans <| by simp, ?_⟩
  rw [← sub_le_iff_le_add, neg_sub_comm, sub_le_iff_le_add', ← abs_two, ← abs_mul]
  calc
    -|2 * f x₀| ≤ 2 * f x₀ := neg_abs_le _
    _ ≤ f y + f (2 • x₀ - y) := by
      have := hf.2 hx' hx (by positivity) (by positivity) (add_halves _)
      simp only [one_div, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_ofNat, smul_sub, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, inv_smul_smul₀, add_sub_cancel, smul_eq_mul] at this
      cancel_denoms at this
      rwa [← Nat.cast_two, Nat.cast_smul_eq_nsmul] at this
    _ ≤ f y + |r| := by gcongr; exact hfr'.trans (le_abs_self _)

lemma ConcaveOn.isBoundedUnder_abs (hf : ConcaveOn ℝ C f) {x₀ : E} (hC : C ∈ 𝓝 x₀) :
    (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f| ↔ (𝓝 x₀).IsBoundedUnder (· ≥ ·) f := by
  simpa [Pi.neg_def, Pi.abs_def] using hf.neg.isBoundedUnder_abs hC

lemma ConvexOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConvexOn ℝ C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    ∃ x₀ ∈ C, ContinuousAt f x₀,
    ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≤ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f|] := by
  tfae_have 1 → 2 := LocallyLipschitzOn.continuousOn
  tfae_have 2 → 3 := by
    obtain ⟨x₀, hx₀⟩ := hC'
    exact fun h ↦ ⟨x₀, hx₀, h.continuousAt <| hC.mem_nhds hx₀⟩
  tfae_have 3 → 4
  | ⟨x₀, hx₀, h⟩ =>
    ⟨x₀, hx₀, f x₀ + 1, by simpa using h.eventually (eventually_le_nhds (by simp))⟩
  tfae_have 4 → 5
  | ⟨x₀, hx₀, r, hr⟩, x, hx => by
    have : ∀ᶠ δ in 𝓝 (0 : ℝ), (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀ ∈ C := by
      have h : ContinuousAt (fun δ : ℝ ↦ (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀) 0 := by
        fun_prop (disch := norm_num)
      exact h (by simpa using hC.mem_nhds hx)
    obtain ⟨δ, hδ₀, hy, hδ₁⟩ := (this.and <| eventually_lt_nhds zero_lt_one).exists_gt
    set y := (1 - δ)⁻¹ • x - (δ / (1 - δ)) • x₀
    refine ⟨max r (f y), ?_⟩
    simp only [Filter.eventually_map] at hr ⊢
    obtain ⟨ε, hε, hr⟩ := Metric.eventually_nhds_iff.1 <| hr.and (hC.eventually_mem hx₀)
    refine Metric.eventually_nhds_iff.2 ⟨ε * δ, by positivity, fun z hz ↦ ?_⟩
    have hx₀' : δ⁻¹ • (x - y) + y = x₀ := MulAction.injective₀ (sub_ne_zero.2 hδ₁.ne') <| by
      simp [y, smul_sub, smul_smul, hδ₀.ne', div_eq_mul_inv, sub_ne_zero.2 hδ₁.ne', mul_left_comm,
        sub_mul, sub_smul]
    let w := δ⁻¹ • (z - y) + y
    have hwyz : δ • w + (1 - δ) • y = z := by simp [w, hδ₀.ne', sub_smul]
    have hw : dist w x₀ < ε := by
      simpa [w, ← hx₀', dist_smul₀, abs_of_nonneg, hδ₀.le, inv_mul_lt_iff₀', hδ₀]
    calc
      f z ≤ max (f w) (f y) :=
        hf.le_max_of_mem_segment (hr hw).2 hy ⟨_, _, hδ₀.le, sub_nonneg.2 hδ₁.le, by simp, hwyz⟩
      _ ≤ max r (f y) := by gcongr; exact (hr hw).1
  tfae_have 6 ↔ 5 := forall₂_congr fun x₀ hx₀ ↦ hf.isBoundedUnder_abs (hC.mem_nhds hx₀)
  tfae_have 6 → 1
  | h, x, hx => by
    obtain ⟨r, hr⟩ := h hx
    obtain ⟨ε, hε, hεD⟩ := Metric.mem_nhds_iff.1 <| Filter.inter_mem (hC.mem_nhds hx) hr
    simp only [preimage_setOf_eq, Pi.abs_apply, subset_inter_iff, hC.nhdsWithin_eq hx] at hεD ⊢
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_of_isBounded (hf.subset hεD.1 (convex_ball ..))
      (half_lt_self hε) <| isBounded_iff_forall_norm_le.2 ⟨r, by simpa using hεD.2⟩
    exact ⟨K, _, ball_mem_nhds _ (by simpa), hK⟩
  tfae_finish

lemma ConcaveOn.continuousOn_tfae (hC : IsOpen C) (hC' : C.Nonempty) (hf : ConcaveOn ℝ C f) : TFAE [
    LocallyLipschitzOn C f,
    ContinuousOn f C,
    ∃ x₀ ∈ C, ContinuousAt f x₀,
    ∃ x₀ ∈ C, (𝓝 x₀).IsBoundedUnder (· ≥ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≥ ·) f,
    ∀ ⦃x₀⦄, x₀ ∈ C → (𝓝 x₀).IsBoundedUnder (· ≤ ·) |f|] := by
  have := hf.neg.continuousOn_tfae hC hC'
  simp only [locallyLipschitzOn_neg_iff, continuousOn_neg_iff, continuousAt_neg_iff, abs_neg]
    at this
  convert this using 8 <;> exact (Equiv.neg ℝ).exists_congr (by simp)

lemma ConvexOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  obtain rfl | hC' := C.eq_empty_or_nonempty
  · simp
  · exact (hf.continuousOn_tfae hC hC').out 0 1

lemma ConcaveOn.locallyLipschitzOn_iff_continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f ↔ ContinuousOn f C := by
  simpa using hf.neg.locallyLipschitzOn_iff_continuousOn hC

variable [FiniteDimensional ℝ E]

protected lemma ConvexOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn C f := by
  obtain rfl | ⟨x₀, hx₀⟩ := C.eq_empty_or_nonempty
  · simp
  · obtain ⟨b, hx₀b, hbC⟩ := exists_mem_interior_convexHull_affineBasis (hC.mem_nhds hx₀)
    refine ((hf.continuousOn_tfae hC ⟨x₀, hx₀⟩).out 3 0).mp ?_
    refine ⟨x₀, hx₀, BddAbove.isBoundedUnder (IsOpen.mem_nhds isOpen_interior hx₀b) ?_⟩
    exact (hf.bddAbove_convexHull ((subset_convexHull ..).trans hbC)
      ((finite_range _).image _).bddAbove).mono (by gcongr; exact interior_subset)

protected lemma ConcaveOn.locallyLipschitzOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn C f := by simpa using hf.neg.locallyLipschitzOn hC

protected lemma ConvexOn.continuousOn (hC : IsOpen C) (hf : ConvexOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

protected lemma ConcaveOn.continuousOn (hC : IsOpen C) (hf : ConcaveOn ℝ C f) :
    ContinuousOn f C := (hf.locallyLipschitzOn hC).continuousOn

lemma ConvexOn.locallyLipschitzOn_interior (hf : ConvexOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

lemma ConcaveOn.locallyLipschitzOn_interior (hf : ConcaveOn ℝ C f) :
    LocallyLipschitzOn (interior C) f :=
  (hf.subset interior_subset hf.1.interior).locallyLipschitzOn isOpen_interior

lemma ConvexOn.continuousOn_interior (hf : ConvexOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

lemma ConcaveOn.continuousOn_interior (hf : ConcaveOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.locallyLipschitzOn_interior.continuousOn

protected lemma ConvexOn.locallyLipschitz (hf : ConvexOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

protected lemma ConcaveOn.locallyLipschitz (hf : ConcaveOn ℝ univ f) : LocallyLipschitz f := by
  simpa using hf.locallyLipschitzOn_interior

-- Commented out since `intrinsicInterior` is not imported (but should be once these are proved)
-- proof_wanted ConvexOn.locallyLipschitzOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.locallyLipschitzOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConvexOn.continuousOn_intrinsicInterior (hf : ConvexOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)

-- proof_wanted ConcaveOn.continuousOn_intrinsicInterior (hf : ConcaveOn ℝ C f) :
--     ContinuousOn f (intrinsicInterior ℝ C)
