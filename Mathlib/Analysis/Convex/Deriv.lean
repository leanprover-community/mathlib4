/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Slope

/-!
# Convexity of functions and derivatives

Here we relate convexity of functions `ℝ → ℝ` to properties of their derivatives.

## Main results

* `MonotoneOn.convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

-/

open Metric Set Asymptotics ContinuousLinearMap Filter

open scoped Classical Topology NNReal

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem MonotoneOn.convexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn ℝ D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
      have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
        exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y) :=
        exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)
#align monotone_on.convex_on_of_deriv MonotoneOn.convexOn_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)
#align antitone_on.concave_on_of_deriv AntitoneOn.concaveOn_of_deriv

theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine' ⟨b, ⟨hxa.trans hab, hby⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab
#align strict_mono_on.exists_slope_lt_deriv_aux StrictMonoOn.exists_slope_lt_deriv_aux

theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · push_neg at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine' ⟨b, ⟨hxw.trans hwb, hby⟩, _⟩
    simp only [div_lt_iff, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
#align strict_mono_on.exists_slope_lt_deriv StrictMonoOn.exists_slope_lt_deriv

theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine' ⟨b, ⟨hxb, hba.trans hay⟩, _⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba
#align strict_mono_on.exists_deriv_lt_slope_aux StrictMonoOn.exists_deriv_lt_slope_aux

theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · push_neg at h
    rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine' hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine' ⟨a, ⟨hxa, haw.trans hwy⟩, _⟩
    simp only [lt_div_iff, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith
#align strict_mono_on.exists_deriv_lt_slope StrictMonoOn.exists_deriv_lt_slope

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly monotone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
    have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
    -- can be compared to the slopes between `x, y` and `y, z` respectively.
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a :=
      StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y) :=
      StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)
#align strict_mono_on.strict_convex_on_of_deriv StrictMonoOn.strictConvexOn_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg
#align strict_anti_on.strict_concave_on_of_deriv StrictAntiOn.strictConcaveOn_of_deriv

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
#align monotone.convex_on_univ_of_deriv Monotone.convexOn_univ_of_deriv

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn
#align antitone.concave_on_univ_of_deriv Antitone.concaveOn_univ_of_deriv

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn
#align strict_mono.strict_convex_on_univ_of_deriv StrictMono.strictConvexOn_univ_of_deriv

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn
#align strict_anti.strict_concave_on_univ_of_deriv StrictAnti.strictConcaveOn_univ_of_deriv

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'
#align convex_on_of_deriv2_nonneg convexOn_of_deriv2_nonneg

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'
#align concave_on_of_deriv2_nonpos concaveOn_of_deriv2_nonpos

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
lemma convexOn_of_hasDerivWithinAt2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 ≤ f'' x) : ConvexOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx using 1
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this $ by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
lemma concaveOn_of_hasDerivWithinAt2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, f'' x ≤ 0) : ConcaveOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx using 1
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this $ by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, 0 < (deriv^[2] f) x) :
    StrictConvexOn ℝ D f :=
  ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf
#align strict_convex_on_of_deriv2_pos strictConvexOn_of_deriv2_pos

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, deriv^[2] f x < 0) :
    StrictConcaveOn ℝ D f :=
  ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf
#align strict_concave_on_of_deriv2_neg strictConcaveOn_of_deriv2_neg

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)
#align convex_on_of_deriv2_nonneg' convexOn_of_deriv2_nonneg'

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)
#align concave_on_of_deriv2_nonpos' concaveOn_of_deriv2_nonpos'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)
#align strict_convex_on_of_deriv2_pos' strictConvexOn_of_deriv2_pos'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)
#align strict_concave_on_of_deriv2_neg' strictConcaveOn_of_deriv2_neg'

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x
#align convex_on_univ_of_deriv2_nonneg convexOn_univ_of_deriv2_nonneg

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, deriv^[2] f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x
#align concave_on_univ_of_deriv2_nonpos concaveOn_univ_of_deriv2_nonpos

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x
#align strict_convex_on_univ_of_deriv2_pos strictConvexOn_univ_of_deriv2_pos

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, deriv^[2] f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x
#align strict_concave_on_univ_of_deriv2_neg strictConcaveOn_univ_of_deriv2_neg
