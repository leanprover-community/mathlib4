/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Convexity of functions and derivatives

Here we relate convexity of functions `ℝ → ℝ` to properties of their derivatives.

## Main results

* `MonotoneOn.convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.
* `ConvexOn.monotoneOn_deriv`: if a function is convex and differentiable, then its derivative is
  monotone.
-/

public section

open Metric Set Asymptotics ContinuousLinearMap Filter
open scoped Topology NNReal

/-!
## Monotonicity of `f'` implies convexity of `f`
-/

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

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)

theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine ⟨b, ⟨hxa.trans hab, hby⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab

theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
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
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨b, ⟨hxw.trans hwb, hby⟩, ?_⟩
    simp only [div_lt_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine ⟨b, ⟨hxb, hba.trans hay⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba

theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
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
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨a, ⟨hxa, haw.trans hwy⟩, ?_⟩
    simp only [lt_div_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

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

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

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
    exact (hf'' _ hy).congr this <| by rw [this hy]

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
    exact (hf'' _ hy).congr this <| by rw [this hy]

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

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, deriv^[2] f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, deriv^[2] f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

/-!
## Convexity of `f` implies monotonicity of `f'`

In this section we prove inequalities relating derivatives of convex functions to slopes of secant
lines, and deduce that if `f` is convex then its derivative is monotone (and similarly for strict
convexity / strict monotonicity).
-/

section slope

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is monotone on `s \ {x}`. -/
lemma ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) : MonotoneOn (slope f x) (s \ {x}) :=
  (slope_fun_def_field f _).symm ▸ fun _ hy _ hz hz' ↦ hfc.secant_mono hx (mem_of_mem_diff hy)
    (mem_of_mem_diff hz) (notMem_of_mem_diff hy :) (notMem_of_mem_diff hz :) hz'

lemma ConvexOn.monotoneOn_slope_gt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | x < y} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne'⟩

lemma ConvexOn.monotoneOn_slope_lt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    MonotoneOn (slope f x) {y ∈ s | y < x} :=
  (hfc.slope_mono hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne⟩

/-- If `f : 𝕜 → 𝕜` is concave on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is antitone on `s \ {x}`. -/
lemma ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x ∈ s) :
    AntitoneOn (slope f x) (s \ {x}) := by
  rw [← neg_neg f, slope_neg_fun]
  exact (ConvexOn.slope_mono hfc.neg hx).neg

lemma ConcaveOn.antitoneOn_slope_gt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    AntitoneOn (slope f x) {y ∈ s | x < y} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne'⟩

lemma ConcaveOn.antitoneOn_slope_lt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    AntitoneOn (slope f x) {y ∈ s | y < x} :=
  (hfc.slope_anti hxs).mono fun _ ⟨h1, h2⟩ ↦ ⟨h1, h2.ne⟩

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

lemma bddBelow_slope_lt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddBelow (slope f x '' {y ∈ s | x < y}) := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, y < x ∧ y ∈ s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddBelow_iff_subset_Ici.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Ici, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hyx.trans hz.2).le
  · simp [hys, hyx.ne]
  · simp [hz.2.ne', hz.1]

lemma bddAbove_slope_gt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddAbove (slope f x '' {y ∈ s | y < x}) := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, x < y ∧ y ∈ s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine bddAbove_iff_subset_Iic.mpr ⟨slope f x y, fun y' ⟨z, hz, hz'⟩ ↦ ?_⟩
  simp_rw [mem_Iic, ← hz']
  refine hfc.slope_mono (interior_subset hxs) ?_ ?_ (hz.2.trans hyx).le
  · simp [hz.2.ne, hz.1]
  · simp [hys, hyx.ne']

end slope

namespace ConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section Interior

/-!
### Left and right derivative of a convex function in the interior of the set
-/

lemma hasDerivWithinAt_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (sInf (slope f x '' {y ∈ S | x < y})) (Ioi x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Ioi, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h : Ioo x b ⊆ {y | y ∈ S ∧ x < y} := fun z hz ↦ ⟨habs ⟨hxab.1.trans hz.1, hz.2⟩, hz.1⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[>] x) (𝓝 (sInf (slope f x '' Ioo x b))) :=
    ((monotoneOn_slope_gt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_right
      (by simpa using hxab.2) ((bddBelow_slope_lt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sInf (slope f x '' Ioo x b) = sInf (slope f x '' {y ∈ S | x < y}) by rwa [← this]
  apply (monotoneOn_slope_gt hfc (habs hxab)).csInf_eq_of_subset_of_forall_exists_le
    (bddBelow_slope_lt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hxy⟩
  obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxab.2 hxy)
  exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, hzy.le.trans (min_le_right _ _)⟩

lemma hasDerivWithinAt_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (sSup (slope f x '' {y ∈ S | y < x})) (Iio x) x := by
  have hxs' := hxs
  rw [mem_interior_iff_mem_nhds, mem_nhds_iff_exists_Ioo_subset] at hxs'
  obtain ⟨a, b, hxab, habs⟩ := hxs'
  simp_rw [hasDerivWithinAt_iff_tendsto_slope]
  simp only [mem_Iio, lt_self_iff_false, not_false_eq_true, diff_singleton_eq_self]
  have h : Ioo a x ⊆ {y | y ∈ S ∧ y < x} := fun z hz ↦ ⟨habs ⟨hz.1, hz.2.trans hxab.2⟩, hz.2⟩
  have h_Ioo : Tendsto (slope f x) (𝓝[<] x) (𝓝 (sSup (slope f x '' Ioo a x))) :=
    ((monotoneOn_slope_lt hfc (habs hxab)).mono h).tendsto_nhdsWithin_Ioo_left
      (by simpa using hxab.1) ((bddAbove_slope_gt_of_mem_interior hfc hxs).mono (image_mono h))
  suffices sSup (slope f x '' Ioo a x) = sSup (slope f x '' {y ∈ S | y < x}) by rwa [← this]
  apply (monotoneOn_slope_lt hfc (habs hxab)).csSup_eq_of_subset_of_forall_exists_le
    (bddAbove_slope_gt_of_mem_interior hfc hxs) h ?_
  rintro y ⟨hyS, hyx⟩
  obtain ⟨z, hyz, hzx⟩ := exists_between (max_lt hxab.1 hyx)
  exact ⟨z, ⟨(le_max_left _ _).trans_lt hyz, hzx⟩, (le_max_right _ _).trans hyz.le⟩

lemma differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt

lemma differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt

lemma hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

lemma hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

lemma rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Ioi x) x = sInf (slope f x '' {y | y ∈ S ∧ x < y}) :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x = sSup (slope f x '' {y | y ∈ S ∧ y < x}) :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

lemma monotoneOn_rightDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Ioi x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine csInf_le_of_le (b := slope f x y) (bddBelow_slope_lt_of_mem_interior hfc hxs)
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

lemma monotoneOn_leftDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Iio x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine le_csSup_of_le (b := slope f x y) (bddAbove_slope_gt_of_mem_interior hfc hys)
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

lemma leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x := by
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

end Interior

section left
/-!
### Convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and right-differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is bounded below by the right derivative of `f` at `x`. -/
lemma le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' ≤ slope f x y := by
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_def_field]
  filter_upwards [eventually_lt_nhds hxy] with t ht (ht' : x < t)
  refine hfc.secant_mono hx (?_ : t ∈ S) hy ht'.ne' hxy.ne' ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht'.le, ht.le⟩

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` using `derivWithin`. -/
lemma rightDeriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt

lemma rightDeriv_le_slope_of_mem_interior (hfc : ConvexOn ℝ S f)
    {y : ℝ} (hxs : x ∈ interior S) (hys : y ∈ S) (hxy : x < y) :
    derivWithin f (Ioi x) x ≤ slope f x y :=
  rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `x`, then the slope of any
secant line with left endpoint at `x` is bounded below by the derivative of `f` within `S` at `x`.

This is fractionally weaker than `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
lemma le_slope_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S x) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt` using `derivWithin`. -/
lemma derivWithin_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x ≤ slope f x y :=
  le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `x ∈ S`, then the slope of any secant
line with left endpoint at `x` is bounded below by the derivative of `f` at `x`. -/
lemma le_slope_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (ha : HasDerivAt f f' x) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivAt` using `deriv` -/
lemma deriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x ≤ slope f x y :=
  le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and left-differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the left derivative of `f` at `y`. -/
lemma slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y ≤ f' := by
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  simp_rw [eventually_nhdsWithin_iff, slope_comm f x y, slope_def_field]
  filter_upwards [eventually_gt_nhds hxy] with t ht (ht' : t < y)
  refine hfc.secant_mono hy hx (?_ : t ∈ S) hxy.ne ht'.ne ht.le
  exact hfc.1.ordConnected.out hx hy ⟨ht.le, ht'.le⟩

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` using `derivWithin`. -/
lemma slope_le_leftDeriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y ≤ derivWithin f (Iio y) y :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f)
    (hys : x ∈ S) (hxs : y ∈ interior S) (hxy : x < y) :
    slope f x y ≤ derivWithin f (Iio y) y :=
  slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `y`, then the slope of any
secant line with right endpoint at `y` is bounded above by the derivative of `f` within `S` at `y`.

This is fractionally weaker than `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
lemma slope_le_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt` using `derivWithin`. -/
lemma slope_le_derivWithin (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y ≤ derivWithin f S y :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the derivative of `f` at `y`. -/
lemma slope_le_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivAt` using `deriv`. -/
lemma slope_le_deriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y ≤ deriv f y :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Convex functions, monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
lemma monotoneOn_derivWithin (hfc : ConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    MonotoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
theorem monotoneOn_deriv (hfc : ConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))

lemma isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x ≤ 0) (hf_rd : 0 ≤ derivWithin f (Ioi x) x) :
    IsMinOn f S x := by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · suffices 0 ≤ slope f x y by
      simp only [slope_def_field, div_nonneg_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hxy, and_false, or_false] at this
      exact this.1
    exact hf_rd.trans <| rightDeriv_le_slope_of_mem_interior hf hx hy hxy
  · simp [h_eq]
  · suffices slope f x y ≤ 0 by
      simp only [slope_def_field, div_nonpos_iff, sub_nonneg, tsub_le_iff_right, zero_add,
        not_le.mpr hyx, and_false, or_false] at this
      exact this.1
    rw [slope_comm]
    exact (slope_le_leftDeriv_of_mem_interior hf hy hx hyx).trans hf_ld

lemma isMinOn_of_rightDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_rd : derivWithin f (Ioi x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd

lemma isMinOn_of_leftDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

section AffineLowerBound

/-- A convex set of `ℝ` with empty interior is a subsingleton. -/
lemma _root_.Convex.subsingleton_of_interior_eq_empty (hs : Convex ℝ S) (h : interior S = ∅) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra h_ne
  wlog h_lt : x < y
  · exact this hs h hy hx (Ne.symm h_ne) (lt_of_le_of_ne' (not_lt.mp h_lt) h_ne)
  · have h_subset : Set.Icc x y ⊆ S := by
      rw [← segment_eq_Icc h_lt.le]
      exact hs.segment_subset hx hy
    have : Set.Ioo x y ⊆ interior S := by
      rw [← interior_Icc]
      exact interior_mono h_subset
    simp only [h, Set.subset_empty_iff, Set.Ioo_eq_empty_iff] at this
    exact this h_lt

lemma affine_le_of_mem_interior (hf : ConvexOn ℝ S f) {x y : ℝ}
    (hx : x ∈ interior S) (hy : y ∈ S) :
    derivWithin f (Set.Ioi x) x * y + (f x - derivWithin f (Set.Ioi x) x * x) ≤ f y := by
  rw [add_comm]
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · have : derivWithin f (Set.Ioi x) x ≤ slope f x y :=
      hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at this
    rwa [le_div_iff₀ (by simp [hxy]), le_sub_iff_add_le, add_comm, mul_sub, add_sub,
      add_sub_right_comm] at this
  · simp [h_eq]
  · have : slope f x y ≤ derivWithin f (Set.Ioi x) x := by
      have := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
        (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
      rwa [slope_comm]
    rw [slope_def_field] at this
    rw [← neg_div_neg_eq, neg_sub, neg_sub] at this
    rwa [div_le_iff₀ (by simp [hyx]), sub_le_iff_le_add, mul_sub, ← sub_le_iff_le_add',
      sub_sub_eq_add_sub, add_sub_right_comm] at this

lemma exists_affine_le (hf : ConvexOn ℝ S f) (hs : Convex ℝ S) :
    ∃ c c', ∀ x ∈ S, c * x + c' ≤ f x := by
  cases Set.eq_empty_or_nonempty (interior S) with
  | inl h => -- there is at most one point in `S`
    have hs_sub : S.Subsingleton := hs.subsingleton_of_interior_eq_empty h
    cases Set.eq_empty_or_nonempty S with
    | inl h' => simp [h']
    | inr h' => -- there is exactly one point in `S`
      obtain ⟨x, hxs⟩ := h'
      refine ⟨0, f x, fun y hys ↦ ?_⟩
      simp [hs_sub hxs hys]
  | inr h => -- there is a point in the interior of `S`
    obtain ⟨x, hx⟩ := h
    refine ⟨derivWithin f (Set.Ioi x) x, f x - derivWithin f (Set.Ioi x) x * x, fun y hy ↦ ?_⟩
    exact hf.affine_le_of_mem_interior hx hy

end AffineLowerBound

end ConvexOn

namespace StrictConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section left
/-!
### Strict convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and right-differentiable at `x ∈ S`, then the slope of
any secant line with left endpoint at `x` is strictly greater than the right derivative of `f` at
`x`. -/
lemma lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' < slope f x y := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy
  simp only [← slope_def_field] at this
  exact (hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf').trans_lt this

lemma rightDeriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `x ∈ S`, then the
slope of any secant line with left endpoint at `x` is strictly greater than the derivative of `f`
within `S` at `x`.

This is fractionally weaker than `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy

lemma derivWithin_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is strictly greater than the derivative of `f` at `x`. -/
lemma lt_slope_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' x) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

lemma deriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the left derivative at `y`. -/
lemma slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y < f' := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.1.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have := hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu
  simp_rw [← slope_def_field, slope_comm _ y] at this
  exact this.trans_le <| hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu hy huy hf'

lemma slope_lt_leftDeriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y < derivWithin f (Iio y) y :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `y ∈ S`, then the
slope of any secant line with right endpoint at `y` is strictly less than the derivative of `f`
within `S` at `y`.

This is fractionally weaker than `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy

lemma slope_lt_derivWithin (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y < derivWithin f S y :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the derivative of `f` at `y`. -/
lemma slope_lt_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma slope_lt_deriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y < deriv f y :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/-!
### Strict convex functions, strict monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
lemma strictMonoOn_derivWithin (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictMonoOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
lemma strictMonoOn_deriv (hfc : StrictConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

end StrictConvexOn

section MirrorImage

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

namespace ConcaveOn

section left
/-!
### Concave functions, derivative at left endpoint of secant
-/

lemma slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y ≤ f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

lemma slope_le_rightDeriv (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y ≤ derivWithin f (Ioi x) x :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivWithinAt f f' S x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hfd.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsGT hx hy hxy

lemma slope_le_derivWithin (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y ≤ derivWithin f S x :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

lemma slope_le_deriv (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : DifferentiableAt ℝ f x) :
    slope f x y ≤ deriv f x :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Concave functions, derivative at right endpoint of secant
-/

lemma le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' ≤ slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

lemma leftDeriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma le_slope_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.1.ordConnected.mem_nhdsLT hx hy hxy

lemma derivWithin_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma le_slope_of_hasDerivAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' ≤ slope f x y :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma deriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y ≤ slope f x y :=
  hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Concave functions, anti-monotonicity of derivative
-/

lemma antitoneOn_derivWithin (hfc : ConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    AntitoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

/-- If `f` is concave on `S` and differentiable at all points of `S`, then its derivative is
antitone (monotone decreasing) on `S`. -/
theorem antitoneOn_deriv (hfc : ConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    AntitoneOn (deriv f) S := by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end ConcaveOn

namespace StrictConcaveOn

section left
/-!
### Strict concave functions, derivative at left endpoint of secant
-/

lemma slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

lemma slope_lt_rightDeriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y < derivWithin f (Ioi x) x :=
  hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)

lemma slope_lt_derivWithin (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y < derivWithin f S x :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma slope_lt_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivAt f f' x) :
    slope f x y < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)

lemma slope_lt_deriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    slope f x y < deriv f x :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict concave functions, derivative at right endpoint of secant
-/

lemma lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' < slope f x y := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

lemma leftDeriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    f' < slope f x y := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)

lemma derivWithin_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma lt_slope_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' < slope f x y :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma deriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y < slope f x y :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Strict concave functions, anti-monotonicity of derivative
-/

lemma strictAntiOn_derivWithin (hfc : StrictConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictAntiOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))

theorem strictAntiOn_deriv (hfc : StrictConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictAntiOn (deriv f) S := by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end StrictConcaveOn

end MirrorImage
