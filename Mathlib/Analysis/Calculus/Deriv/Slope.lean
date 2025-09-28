/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.LinearAlgebra.AffineSpace.Slope
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Derivative as the limit of the slope

In this file we relate the derivative of a function with its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `𝓝[≠] x`.
Since we are talking about functions taking values in a normed space instead of the base field, we
use `slope f x y = (y - x)⁻¹ • (f y - f x)` instead of division.

We also prove some estimates on the upper/lower limits of the slope in terms of the derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, slope
-/

universe u v

open scoped Topology

open Filter TopologicalSpace Set

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. In this version we have to take the limit along the subset `{x}ᶜ`,
because for `y=x` the slope equals zero due to the convention `0⁻¹=0`. -/
theorem hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' x L ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') :=
  calc HasDerivAtFilter f f' x L
    ↔ Tendsto (fun y ↦ slope f x y - (y - x)⁻¹ • (y - x) • f') L (𝓝 0) := by
        simp only [hasDerivAtFilter_iff_tendsto, ← norm_inv, ← norm_smul,
          ← tendsto_zero_iff_norm_tendsto_zero, slope_def_module, smul_sub]
  _ ↔ Tendsto (fun y ↦ slope f x y - (y - x)⁻¹ • (y - x) • f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) :=
        .symm <| tendsto_inf_principal_nhds_iff_of_forall_eq <| by simp
  _ ↔ Tendsto (fun y ↦ slope f x y - f') (L ⊓ 𝓟 {x}ᶜ) (𝓝 0) := tendsto_congr' <| by
        refine (EqOn.eventuallyEq fun y hy ↦ ?_).filter_mono inf_le_right
        rw [inv_smul_smul₀ (sub_ne_zero.2 hy) f']
  _ ↔ Tendsto (slope f x) (L ⊓ 𝓟 {x}ᶜ) (𝓝 f') := by
        rw [← nhds_translation_sub f', tendsto_comap_iff]; rfl

theorem hasDerivWithinAt_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s \ {x}] x) (𝓝 f') := by
  simp only [HasDerivWithinAt, nhdsWithin, diff_eq, ← inf_assoc, inf_principal.symm]
  exact hasDerivAtFilter_iff_tendsto_slope

theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔ Tendsto (slope f x) (𝓝[s] x) (𝓝 f') := by
  rw [hasDerivWithinAt_iff_tendsto_slope, diff_singleton_eq_self hs]

theorem hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope

theorem hasDerivAt_iff_tendsto_slope_zero :
    HasDerivAt f f' x ↔ Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f') := by
  have : 𝓝[≠] x = Filter.map (fun t ↦ x + t) (𝓝[≠] 0) := by
    simp [nhdsWithin, map_add_left_nhds_zero x, Filter.map_inf, add_right_injective x]
  simp [hasDerivAt_iff_tendsto_slope, this, slope, Function.comp_def]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero

theorem HasDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[>] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)

theorem HasDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[<] 0) (𝓝 f') :=
  h.tendsto_slope_zero.mono_left (nhdsLT_le_nhdsNE 0)

/-- Given a set `t` such that `s ∩ t` is dense in `s`, then the range of `derivWithin f s` is
contained in the closure of the submodule spanned by the image of `t`. -/
theorem range_derivWithin_subset_closure_span_image
    (f : 𝕜 → F) {s t : Set 𝕜} (h : s ⊆ closure (s ∩ t)) :
    range (derivWithin f s) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rintro - ⟨x, rfl⟩
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (zero_mem _)
  have I : (𝓝[(s ∩ t) \ {x}] x).NeBot := by
    rw [← accPt_principal_iff_nhdsWithin, ← uniqueDiffWithinAt_iff_accPt]
    exact H.mono_closure h
  have : Tendsto (slope f x) (𝓝[(s ∩ t) \ {x}] x) (𝓝 (derivWithin f s x)) := by
    apply Tendsto.mono_left (hasDerivWithinAt_iff_tendsto_slope.1 H'.hasDerivWithinAt)
    rw [inter_comm, inter_diff_assoc]
    exact nhdsWithin_mono _ inter_subset_right
  rw [← closure_closure, ← Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope, vsub_eq_sub, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact mem_image_of_mem _ hy.1.2
  · apply Submodule.closure_subset_topologicalClosure_span
    suffices A : f x ∈ closure (f '' (s ∩ t)) from
      closure_mono (image_mono inter_subset_right) A
    apply ContinuousWithinAt.mem_closure_image
    · apply H'.continuousWithinAt.mono inter_subset_left
    rw [mem_closure_iff_nhdsWithin_neBot]
    exact I.mono (nhdsWithin_mono _ diff_subset)

/-- Given a dense set `t`, then the range of `deriv f` is contained in the closure of the submodule
spanned by the image of `t`. -/
theorem range_deriv_subset_closure_span_image
    (f : 𝕜 → F) {t : Set 𝕜} (h : Dense t) :
    range (deriv f) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]

theorem isSeparable_range_derivWithin [SeparableSpace 𝕜] (f : 𝕜 → F) (s : Set 𝕜) :
    IsSeparable (range (derivWithin f s)) := by
  obtain ⟨t, ts, t_count, ht⟩ : ∃ t, t ⊆ s ∧ Set.Countable t ∧ s ⊆ closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s ⊆ closure (s ∩ t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin_subset_closure_span_image f this)
  exact (Countable.image t_count f).isSeparable.span.closure

theorem isSeparable_range_deriv [SeparableSpace 𝕜] (f : 𝕜 → F) :
    IsSeparable (range (deriv f)) := by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _

lemma HasDerivAt.continuousAt_div [DecidableEq 𝕜] {f : 𝕜 → 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c) :
    ContinuousAt (Function.update (fun x ↦ (f x - f c) / (x - c)) c a) c := by
  rw [← slope_fun_def_field]
  exact continuousAt_update_same.mpr <| hasDerivAt_iff_tendsto_slope.mp hf

section Order

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {g : 𝕜 → 𝕜} {g' : 𝕜}

/-- If a monotone function has a derivative within a set at a non-isolated point, then this
derivative is nonnegative. -/
lemma HasDerivWithinAt.nonneg_of_monotoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s) : 0 ≤ g' := by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  have : Tendsto (slope g x) (𝓝[s \ {x}] x) (𝓝 g') := hasDerivWithinAt_iff_tendsto_slope.mp hd
  apply ge_of_tendsto this
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [mem_diff, mem_singleton_iff] at hy
  rcases lt_or_gt_of_ne hy.2 with h'y | h'y
  · simp only [slope, vsub_eq_sub, smul_eq_mul]
    apply mul_nonneg_of_nonpos_of_nonpos
    · simpa using h'y.le
    · simpa using h'g (by simp [hy]) (by simp) h'y.le
  · simp only [slope, vsub_eq_sub, smul_eq_mul]
    apply mul_nonneg
    · simpa using h'y.le
    · simpa [sub_nonneg] using h'g (by simp) (by simp [hy]) h'y.le

/-- The derivative within a set of a monotone function is nonnegative. -/
lemma MonotoneOn.derivWithin_nonneg (hg : MonotoneOn g s) :
    0 ≤ derivWithin g s x := by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

/-- If a monotone function has a derivative, then this derivative is nonnegative. -/
lemma HasDerivAt.nonneg_of_monotone (hd : HasDerivAt g g' x) (hg : Monotone g) : 0 ≤ g' := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of a monotone function is nonnegative. -/
lemma Monotone.deriv_nonneg (hg : Monotone g) : 0 ≤ deriv g x := by
  rw [← derivWithin_univ]
  exact (hg.monotoneOn univ).derivWithin_nonneg

/-- If an antitone function has a derivative within a set at a non-isolated point, then this
derivative is nonpositive. -/
lemma HasDerivWithinAt.nonpos_of_antitoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : AntitoneOn g s) : g' ≤ 0 := by
  have : MonotoneOn (-g) s := fun x hx y hy hxy ↦ by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

/-- The derivative within a set of an antitone function is nonpositive. -/
lemma AntitoneOn.derivWithin_nonpos (hg : AntitoneOn g s) :
    derivWithin g s x ≤ 0 := by
  simpa [derivWithin.fun_neg] using hg.neg.derivWithin_nonneg

/-- If an antitone function has a derivative, then this derivative is nonpositive. -/
lemma HasDerivAt.nonpos_of_antitone (hd : HasDerivAt g g' x) (hg : Antitone g) : g' ≤ 0 := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of an antitone function is nonpositive. -/
lemma Antitone.deriv_nonpos (hg : Antitone g) : deriv g x ≤ 0 := by
  rw [← derivWithin_univ]
  exact (hg.antitoneOn univ).derivWithin_nonpos

end Order

end NormedField

/-! ### Upper estimates on liminf and limsup -/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ z in 𝓝[s \ {x}] x, slope f x z < r :=
  hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)

theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) : ∀ᶠ z in 𝓝[s] x, slope f x z < r :=
  (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)

theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : ∃ᶠ z in 𝓝[>] x, slope f x z < r :=
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end Real

section RealSpace

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r := by
  have hr₀ : 0 < r := lt_of_le_of_lt (norm_nonneg f') hr
  have A : ∀ᶠ z in 𝓝[s \ {x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    (hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)
  have B : ∀ᶠ z in 𝓝[{x}] x, ‖(z - x)⁻¹ • (f z - f x)‖ ∈ Iio r :=
    mem_of_superset self_mem_nhdsWithin (singleton_subset_iff.2 <| by simp [hr₀])
  have C := mem_sup.2 ⟨A, B⟩
  rw [← nhdsWithin_union, diff_union_self, nhdsWithin_union, mem_sup] at C
  filter_upwards [C.1]
  simp only [norm_smul, mem_Iio, norm_inv]
  exact fun _ => id

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` in some neighborhood of `x` within `s`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `HasDerivWithinAt.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ z in 𝓝[s] x, ‖z - x‖⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  apply (hf.limsup_norm_slope_le hr).mono
  intro z hz
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) ?_) hz
  exact inv_nonneg.2 (norm_nonneg _)

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `HasDerivWithinAt.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, ‖z - x‖⁻¹ * ‖f z - f x‖ < r :=
  (hf.Ioi_of_Ici.limsup_norm_slope_le hr).frequently

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `HasDerivWithinAt.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `HasDerivWithinAt.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f xp‖` instead of `‖f z‖ - ‖f x‖`. -/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) : ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖ - ‖f x‖) < r := by
  have := (hf.Ioi_of_Ici.limsup_slope_norm_le hr).frequently
  refine this.mp (Eventually.mono self_mem_nhdsWithin fun z hxz hz ↦ ?_)
  rwa [Real.norm_eq_abs, abs_of_pos (sub_pos_of_lt hxz)] at hz

end RealSpace
