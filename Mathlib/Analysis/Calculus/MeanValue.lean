/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The mean value inequality and equalities

In this file we prove the following facts:

* `Convex.norm_image_sub_le_of_norm_deriv_le` : if `f` is differentiable on a convex set `s`
  and the norm of its derivative is bounded by `C`, then `f` is Lipschitz continuous on `s` with
  constant `C`; also a variant in which what is bounded by `C` is the norm of the difference of the
  derivative from a fixed linear map. This lemma and its versions are formulated using `RCLike`,
  so they work both for real and complex derivatives.

* `image_le_of*`, `image_norm_le_of_*` : several similar lemmas deducing `f x ≤ B x` or
  `‖f x‖ ≤ B x` from upper estimates on `f'` or `‖f'‖`, respectively. These lemmas differ by
  their assumptions:

  * `of_liminf_*` lemmas assume that limit inferior of some ratio is less than `B' x`;
  * `of_deriv_right_*`, `of_norm_deriv_right_*` lemmas assume that the right derivative
    or its norm is less than `B' x`;
  * `of_*_lt_*` lemmas assume a strict inequality whenever `f x = B x` or `‖f x‖ = B x`;
  * `of_*_le_*` lemmas assume a non-strict inequality everywhere on `[a, b)`;
  * name of a lemma ends with `'` if (1) it assumes that `B` is continuous on `[a, b]`
    and has a right derivative at every point of `[a, b)`, and (2) the lemma has
    a counterpart assuming that `B` is differentiable everywhere on `ℝ`

* `norm_image_sub_le_*_segment` : if derivative of `f` on `[a, b]` is bounded above
  by a constant `C`, then `‖f x - f a‖ ≤ C * ‖x - a‖`; several versions deal with
  right derivative and derivative within `[a, b]` (`HasDerivWithinAt` or `derivWithin`).

* `Convex.is_const_of_fderivWithin_eq_zero` : if a function has derivative `0` on a convex set `s`,
  then it is a constant on `s`.

* `hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt` : a C^1 function over the reals is
  strictly differentiable. (This is a corollary of the mean value inequality.)
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

open Metric Set Asymptotics ContinuousLinearMap Filter

open scoped Topology NNReal

/-! ### One-dimensional fencing inequalities -/


/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  change Icc a b ⊆ { x | f x ≤ B x }
  set s := { x | f x ≤ B x } ∩ Icc a b
  have A : ContinuousOn (fun x => (f x, B x)) (Icc a b) := hf.prodMk hB
  have : IsClosed s := by
    simp only [s, inter_comm]
    exact A.preimage_isClosed_of_isClosed isClosed_Icc OrderClosedTopology.isClosed_le'
  apply this.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxB : f x ≤ B x, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · -- If `f x < B x`, then all we need is continuity of both sides
    refine nonempty_of_mem (inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : ∀ᶠ x in 𝓝[Icc a b] x, f x < B x :=
      A x (Ico_subset_Icc_self xab) (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd) hxB)
    have : ∀ᶠ x in 𝓝[>] x, f x < B x := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · rcases exists_between (bound x xab hxB) with ⟨r, hfr, hrB⟩
    specialize hf' x xab r hfr
    have HB : ∀ᶠ z in 𝓝[>] x, r < slope B x z :=
      (hasDerivWithinAt_iff_tendsto_slope' <| lt_irrefl x).1 (hB' x xab).Ioi_of_Ici
        (Ioi_mem_nhds hrB)
    obtain ⟨z, hfz, hzB, hz⟩ : ∃ z, slope f x z < r ∧ r < slope B x z ∧ z ∈ Ioc x y :=
      hf'.and_eventually (HB.and (Ioc_mem_nhdsGT hy)) |>.exists
    refine ⟨z, ?_, hz⟩
    have := (hfz.trans hzB).le
    rwa [slope_def_field, slope_def_field, div_le_div_iff_of_pos_right (sub_pos.2 hz.1), hxB,
      sub_le_sub_iff_right] at this

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (f z - f x) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(f z - f x) / (z - x)`
  is bounded above by `B'`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_liminf_slope_right_le_deriv_boundary {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    -- `bound` actually says `liminf (f z - f x) / (z - x) ≤ B' x`
    (bound : ∀ x ∈ Ico a b, ∀ r, B' x < r → ∃ᶠ z in 𝓝[>] x, slope f x z < r) :
    ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x := by
  have Hr : ∀ x ∈ Icc a b, ∀ r > 0, f x ≤ B x + r * (x - a) := fun x hx r hr => by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf bound
    · rwa [sub_self, mul_zero, add_zero]
    · exact hB.add (ContinuousOn.const.mul (continuousOn_id.sub ContinuousOn.const))
    · intro x hx
      exact (hB' x hx).add (((hasDerivWithinAt_id x (Ici x)).sub_const a).const_mul r)
    · intro x _ _
      rw [mul_one]
      exact (lt_add_iff_pos_right _).2 hr
    exact hx
  intro x hx
  have : ContinuousWithinAt (fun r => B x + r * (x - a)) (Ioi 0) 0 :=
    continuousWithinAt_const.add (continuousWithinAt_id.mul continuousWithinAt_const)
  convert continuousWithinAt_const.closure_le _ this (Hr x hx) using 1 <;> simp

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary' {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has derivative `B'` everywhere on `ℝ`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x < B' x` whenever `f x = B x`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_lt_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, f x = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `f a ≤ B a`;
* `B` has right derivative `B'` at every point of `[a, b)`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* we have `f' x ≤ B' x` on `[a, b)`.

Then `f x ≤ B x` everywhere on `[a, b]`. -/
theorem image_le_of_deriv_right_le_deriv_boundary {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : f a ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, f' x ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → f x ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary hf ha hB hB' fun x hx _ hr =>
    (hf' x hx).liminf_right_slope_le (lt_of_le_of_lt (bound x hx) hr)

/-! ### Vector-valued functions `f : ℝ → E` -/


section

variable {f : ℝ → E} {a b : ℝ}

/-- General fencing theorem for continuous functions with an estimate on the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `B` has right derivative at every point of `[a, b)`;
* for each `x ∈ [a, b)` the right-side limit inferior of `(‖f z‖ - ‖f x‖) / (z - x)`
  is bounded above by a function `f'`;
* we have `f' x < B' x` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. -/
theorem image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {f' : ℝ → ℝ} (hf : ContinuousOn f (Icc a b))
    -- `hf'` actually says `liminf (‖f z‖ - ‖f x‖) / (z - x) ≤ f' x`
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, slope (norm ∘ f) x z < r)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → f' x < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_lt_deriv_boundary' (continuous_norm.comp_continuousOn hf) hf' ha hB
    hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_liminf_right_slope_norm_lt_deriv_boundary hf
    (fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le hr) ha hB hB' bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* the norm of `f'` is strictly less than `B'` whenever `‖f x‖ = B x`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_lt_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f x‖ = B x → ‖f' x‖ < B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` and `B` have right derivatives `f'` and `B'` respectively at every point of `[a, b)`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary' {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ x ∈ Ico a b, HasDerivWithinAt B (B' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_le_of_liminf_slope_right_le_deriv_boundary (continuous_norm.comp_continuousOn hf) ha hB hB'
    fun x hx _ hr => (hf' x hx).liminf_right_slope_norm_le ((bound x hx).trans_lt hr)

/-- General fencing theorem for continuous functions with an estimate on the norm of the derivative.
Let `f` and `B` be continuous functions on `[a, b]` such that

* `‖f a‖ ≤ B a`;
* `f` has right derivative `f'` at every point of `[a, b)`;
* `B` has derivative `B'` everywhere on `ℝ`;
* we have `‖f' x‖ ≤ B x` everywhere on `[a, b)`.

Then `‖f x‖ ≤ B x` everywhere on `[a, b]`. We use one-sided derivatives in the assumptions
to make this theorem work for piecewise differentiable functions.
-/
theorem image_norm_le_of_norm_deriv_right_le_deriv_boundary {f' : ℝ → E}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    {B B' : ℝ → ℝ} (ha : ‖f a‖ ≤ B a) (hB : ∀ x, HasDerivAt B (B' x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ B' x) : ∀ ⦃x⦄, x ∈ Icc a b → ‖f x‖ ≤ B x :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary' hf hf' ha
    (fun x _ => (hB x).continuousAt.continuousWithinAt) (fun x _ => (hB x).hasDerivWithinAt) bound

/-- A function on `[a, b]` with the norm of the right derivative bounded by `C`
satisfies `‖f x - f a‖ ≤ C * (x - a)`. -/
theorem norm_image_sub_le_of_norm_deriv_right_le_segment {f' : ℝ → E} {C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  let g x := f x - f a
  have hg : ContinuousOn g (Icc a b) := hf.sub ContinuousOn.const
  have hg' : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x := by
    intro x hx
    simp [g, hf' x hx]
  let B x := C * (x - a)
  have hB : ∀ x, HasDerivAt B C x := by
    intro x
    simpa using (hasDerivAt_const x C).mul ((hasDerivAt_id x).sub (hasDerivAt_const x a))
  convert image_norm_le_of_norm_deriv_right_le_deriv_boundary hg hg' _ hB bound
  simp only [g, B]; rw [sub_self, norm_zero, sub_self, mul_zero]

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `HasDerivWithinAt`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x)
    (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ C) : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine
    norm_image_sub_le_of_norm_deriv_right_le_segment (fun x hx => (hf x hx).continuousWithinAt)
      (fun x hx => ?_) bound
  exact (hf x <| Ico_subset_Icc_self hx).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hx)

/-- A function on `[a, b]` with the norm of the derivative within `[a, b]`
bounded by `C` satisfies `‖f x - f a‖ ≤ C * (x - a)`, `derivWithin`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment {C : ℝ} (hf : DifferentiableOn ℝ f (Icc a b))
    (bound : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' ?_ bound
  exact fun x hx => (hf x hx).hasDerivWithinAt

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `HasDerivWithinAt`
version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01' {f' : ℝ → E} {C : ℝ}
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Icc (0 : ℝ) 1) x)
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖f' x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment' hf bound 1 (right_mem_Icc.2 zero_le_one)

/-- A function on `[0, 1]` with the norm of the derivative within `[0, 1]`
bounded by `C` satisfies `‖f 1 - f 0‖ ≤ C`, `derivWithin` version. -/
theorem norm_image_sub_le_of_norm_deriv_le_segment_01 {C : ℝ}
    (hf : DifferentiableOn ℝ f (Icc (0 : ℝ) 1))
    (bound : ∀ x ∈ Ico (0 : ℝ) 1, ‖derivWithin f (Icc (0 : ℝ) 1) x‖ ≤ C) : ‖f 1 - f 0‖ ≤ C := by
  simpa only [sub_zero, mul_one] using
    norm_image_sub_le_of_norm_deriv_le_segment hf bound 1 (right_mem_Icc.2 zero_le_one)

theorem constant_of_has_deriv_right_zero (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt f 0 (Ici x) x) : ∀ x ∈ Icc a b, f x = f a := by
  have : ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ 0 * (x - a) := fun x hx =>
    norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv (fun _ _ => norm_zero.le) x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using this

theorem constant_of_derivWithin_zero (hdiff : DifferentiableOn ℝ f (Icc a b))
    (hderiv : ∀ x ∈ Ico a b, derivWithin f (Icc a b) x = 0) : ∀ x ∈ Icc a b, f x = f a := by
  have H : ∀ x ∈ Ico a b, ‖derivWithin f (Icc a b) x‖ ≤ 0 := by
    simpa only [norm_le_zero_iff] using fun x hx => hderiv x hx
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using fun x hx =>
    norm_image_sub_le_of_norm_deriv_le_segment hdiff H x hx

variable {f' g : ℝ → E}

/-- If two continuous functions on `[a, b]` have the same right derivative and are equal at `a`,
  then they are equal everywhere on `[a, b]`. -/
theorem eq_of_has_deriv_right_eq (derivf : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (derivg : ∀ x ∈ Ico a b, HasDerivWithinAt g (f' x) (Ici x) x) (fcont : ContinuousOn f (Icc a b))
    (gcont : ContinuousOn g (Icc a b)) (hi : f a = g a) : ∀ y ∈ Icc a b, f y = g y := by
  simp only [← @sub_eq_zero _ _ (f _)] at hi ⊢
  exact hi ▸ constant_of_has_deriv_right_zero (fcont.sub gcont) fun y hy => by
    simpa only [sub_self] using (derivf y hy).sub (derivg y hy)

/-- If two differentiable functions on `[a, b]` have the same derivative within `[a, b]` everywhere
  on `[a, b)` and are equal at `a`, then they are equal everywhere on `[a, b]`. -/
theorem eq_of_derivWithin_eq (fdiff : DifferentiableOn ℝ f (Icc a b))
    (gdiff : DifferentiableOn ℝ g (Icc a b))
    (hderiv : EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)) (hi : f a = g a) :
    ∀ y ∈ Icc a b, f y = g y := by
  have A : ∀ y ∈ Ico a b, HasDerivWithinAt f (derivWithin f (Icc a b) y) (Ici y) y := fun y hy =>
    (fdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  have B : ∀ y ∈ Ico a b, HasDerivWithinAt g (derivWithin g (Icc a b) y) (Ici y) y := fun y hy =>
    (gdiff y (mem_Icc_of_Ico hy)).hasDerivWithinAt.mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem hy)
  exact eq_of_has_deriv_right_eq A (fun y hy => (hderiv hy).symm ▸ B y hy) fdiff.continuousOn
    gdiff.continuousOn hi

end

/-!
### Vector-valued functions `f : E → G`

Theorems in this section work both for real and complex differentiable functions. We use assumptions
`[NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]` to
achieve this result. For the domain `E` we also assume `[NormedSpace ℝ E]` to have a notion
of a `Convex` set. -/

section

namespace Convex

variable {𝕜 G : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f g : E → G} {C : ℝ} {s : Set E} {x y : E} {f' g' : E → E →L[𝕜] G} {φ : E →L[𝕜] G}

instance (priority := 100) : PathConnectedSpace 𝕜 := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  infer_instance

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`, then
the function is `C`-Lipschitz. Version with `HasFDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  /- By composition with `AffineMap.lineMap x y`, we reduce to a statement for functions defined
    on `[0,1]`, for which it is proved in `norm_image_sub_le_of_norm_deriv_le_segment`.
    We just have to check the differentiability of the composition and bounds on its derivative,
    which is straightforward but tedious for lack of automation. -/
  set g := (AffineMap.lineMap x y : ℝ → E)
  have segm : MapsTo g (Icc 0 1 : Set ℝ) s := hs.mapsTo_lineMap xs ys
  have hD : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) (Icc 0 1) t := fun t ht => by
    simpa using ((hf (g t) (segm ht)).restrictScalars ℝ).comp_hasDerivWithinAt _
      AffineMap.hasDerivWithinAt_lineMap segm
  have bound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' (g t) (y - x)‖ ≤ C * ‖y - x‖ := fun t ht =>
    le_of_opNorm_le _ (bound _ <| segm <| Ico_subset_Icc_self ht) _
  simpa [g] using norm_image_sub_le_of_norm_deriv_le_segment_01' hD bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `HasFDerivWithinAt` and
`LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_hasFDerivWithin_le {C : ℝ≥0}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C)
    (hs : Convex ℝ s) : LipschitzOnWith C f s := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro x x_in y y_in
  exact hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf bound y_in x_in

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is
`K`-Lipschitz on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt` for a version that claims
existence of `K` instead of an explicit estimate. -/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt (hs : Convex ℝ s)
    {f : E → G} (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y)
    (hcont : ContinuousWithinAt f' s x) (K : ℝ≥0) (hK : ‖f' x‖₊ < K) :
    ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t := by
  obtain ⟨ε, ε0, hε⟩ : ∃ ε > 0,
      ball x ε ∩ s ⊆ { y | HasFDerivWithinAt f (f' y) s y ∧ ‖f' y‖₊ < K } :=
    mem_nhdsWithin_iff.1 (hder.and <| hcont.nnnorm.eventually (gt_mem_nhds hK))
  rw [inter_comm] at hε
  refine ⟨s ∩ ball x ε, inter_mem_nhdsWithin _ (ball_mem_nhds _ ε0), ?_⟩
  exact
    (hs.inter (convex_ball _ _)).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun y hy => (hε hy).1.mono inter_subset_left) fun y hy => (hε hy).2.le

/-- Let `s` be a convex set in a real normed vector space `E`, let `f : E → G` be a function
differentiable within `s` in a neighborhood of `x : E` with derivative `f'`. Suppose that `f'` is
continuous within `s` at `x`. Then for any number `K : ℝ≥0` larger than `‖f' x‖₊`, `f` is Lipschitz
on some neighborhood of `x` within `s`. See also
`Convex.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt` for a version
with an explicit estimate on the Lipschitz constant. -/
theorem exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt (hs : Convex ℝ s) {f : E → G}
    (hder : ∀ᶠ y in 𝓝[s] x, HasFDerivWithinAt f (f' y) s y) (hcont : ContinuousWithinAt f' s x) :
    ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t :=
  (exists_gt _).imp <|
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt hder hcont

/-- The mean value theorem on a convex set: if the derivative of a function within this set is
bounded by `C`, then the function is `C`-Lipschitz. Version with `fderivWithin`. -/
theorem norm_image_sub_le_of_norm_fderivWithin_le (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderivWithin` and
`LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_fderivWithin_le {C : ℝ≥0} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt) bound

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set: if the derivative of a function is bounded by `C` on
`s`, then the function is `C`-Lipschitz on `s`. Version with `fderiv` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_fderiv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound

/-- The mean value theorem: if the derivative of a function is bounded by `C`, then the function is
`C`-Lipschitz. Version with `fderiv` and `LipschitzWith`. -/
theorem _root_.lipschitzWith_of_nnnorm_fderiv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖fderiv 𝕜 f x‖₊ ≤ C) : LipschitzWith C f := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ ↦ hf x) (fun x _ ↦ bound x) convex_univ

/-- Variant of the mean value inequality on a convex set, using a bound on the difference between
the derivative and a fixed linear map, rather than a bound on the derivative itself. Version with
`HasFDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x - φ‖ ≤ C)
    (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ := by
  /- We subtract `φ` to define a new function `g` for which `g' = 0`, for which the previous theorem
    applies, `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`. Then, we just need to glue
    together the pieces, expressing back `f` in terms of `g`. -/
  let g y := f y - φ y
  have hg : ∀ x ∈ s, HasFDerivWithinAt g (f' x - φ) s x := fun x xs =>
    (hf x xs).sub φ.hasFDerivWithinAt
  calc
    ‖f y - f x - φ (y - x)‖ = ‖f y - f x - (φ y - φ x)‖ := by simp
    _ = ‖f y - φ y - (f x - φ x)‖ := by congr 1; abel
    _ = ‖g y - g x‖ := by simp [g]
    _ ≤ C * ‖y - x‖ := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg bound hs xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderivWithin`. -/
theorem norm_image_sub_le_of_norm_fderivWithin_le' (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' (fun x hx => (hf x hx).hasFDerivWithinAt) bound
    xs ys

/-- Variant of the mean value inequality on a convex set. Version with `fderiv`. -/
theorem norm_image_sub_le_of_norm_fderiv_le' (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖fderiv 𝕜 f x - φ‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x - φ (y - x)‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys

/-- If a function has zero Fréchet derivative at every point of a convex set,
then it is a constant on this set. -/
theorem is_const_of_fderivWithin_eq_zero (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : ∀ x ∈ s, fderivWithin 𝕜 f s x = 0) (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  have bound : ∀ x ∈ s, ‖fderivWithin 𝕜 f s x‖ ≤ 0 := fun x hx => by
    simp only [hf' x hx, norm_zero, le_rfl]
  simpa only [(dist_eq_norm _ _).symm, zero_mul, dist_le_zero, eq_comm] using
    hs.norm_image_sub_le_of_norm_fderivWithin_le hf bound hx hy

theorem _root_.is_const_of_fderiv_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f : E → G}
    (hf : Differentiable 𝕜 f) (hf' : ∀ x, fderiv 𝕜 f x = 0)
    (x y : E) : f x = f y := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  exact convex_univ.is_const_of_fderivWithin_eq_zero hf.differentiableOn
    (fun x _ => by rw [fderivWithin_univ]; exact hf' x) trivial trivial

/-- If two functions have equal Fréchet derivatives at every point of a convex set, and are equal at
one point in that set, then they are equal on that set. -/
theorem eqOn_of_fderivWithin_eq (hs : Convex ℝ s) (hf : DifferentiableOn 𝕜 f s)
    (hg : DifferentiableOn 𝕜 g s) (hs' : UniqueDiffOn 𝕜 s)
    (hf' : s.EqOn (fderivWithin 𝕜 f s) (fderivWithin 𝕜 g s)) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := fun y hy => by
  suffices f x - g x = f y - g y by rwa [hfgx, sub_self, eq_comm, sub_eq_zero] at this
  refine hs.is_const_of_fderivWithin_eq_zero (hf.sub hg) (fun z hz => ?_) hx hy
  rw [fderivWithin_sub (hs' _ hz) (hf _ hz) (hg _ hz), sub_eq_zero, hf' hz]

/-- If `f` has zero derivative on an open set, then `f` is locally constant on `s`. -/
-- TODO: change the spelling once we have `IsLocallyConstantOn`.
theorem _root_.IsOpen.isOpen_inter_preimage_of_fderiv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) (t : Set G) : IsOpen (s ∩ f ⁻¹' t) := by
  refine Metric.isOpen_iff.mpr fun y ⟨hy, hy'⟩ ↦ ?_
  obtain ⟨r, hr, h⟩ := Metric.isOpen_iff.mp hs y hy
  refine ⟨r, hr, Set.subset_inter h fun x hx ↦ ?_⟩
  have := (convex_ball y r).is_const_of_fderivWithin_eq_zero (hf.mono h) ?_ hx (mem_ball_self hr)
  · simpa [this]
  · intro z hz
    simpa only [fderivWithin_of_isOpen Metric.isOpen_ball hz] using hf' (h hz)

theorem _root_.isLocallyConstant_of_fderiv_eq_zero (h₁ : Differentiable 𝕜 f)
    (h₂ : ∀ x, fderiv 𝕜 f x = 0) : IsLocallyConstant f := by
  simpa using isOpen_univ.isOpen_inter_preimage_of_fderiv_eq_zero h₁.differentiableOn fun _ _ ↦ h₂ _

/-- If `f` has zero derivative on a connected open set, then `f` is constant on `s`. -/
theorem _root_.IsOpen.exists_is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) : ∃ a, ∀ x ∈ s, f x = a := by
  obtain (rfl | ⟨y, hy⟩) := s.eq_empty_or_nonempty
  · exact ⟨0, by simp⟩
  · refine ⟨f y, fun x hx ↦ ?_⟩
    have h₁ := hs.isOpen_inter_preimage_of_fderiv_eq_zero hf hf' {f y}
    have h₂ := hf.continuousOn.comp_continuous continuous_subtype_val (fun x ↦ x.2)
    by_contra h₃
    obtain ⟨t, ht, ht'⟩ := (isClosed_singleton (x := f y)).preimage h₂
    have ht'' : ∀ a ∈ s, a ∈ t ↔ f a ≠ f y := by simpa [Set.ext_iff] using ht'
    obtain ⟨z, H₁, H₂, H₃⟩ := hs' _ _ h₁ ht (fun x h ↦ by simp [h, ht'', eq_or_ne]) ⟨y, by simpa⟩
      ⟨x, by simp [ht'' _ hx, hx, h₃]⟩
    exact (ht'' _ H₁).mp H₃ H₂.2

theorem _root_.IsOpen.is_const_of_fderiv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (fderiv 𝕜 f) 0) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  obtain ⟨a, ha⟩ := hs.exists_is_const_of_fderiv_eq_zero hs' hf hf'
  rw [ha x hx, ha y hy]

theorem _root_.IsOpen.exists_eq_add_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (fderiv 𝕜 f) (fderiv 𝕜 g)) : ∃ a, s.EqOn f (g · + a) := by
  simp_rw [Set.EqOn, ← sub_eq_iff_eq_add']
  refine hs.exists_is_const_of_fderiv_eq_zero hs' (hf.sub hg) fun x hx ↦ ?_
  rw [fderiv_fun_sub (hf.differentiableAt (hs.mem_nhds hx)) (hg.differentiableAt (hs.mem_nhds hx)),
    hf' hx, sub_self, Pi.zero_apply]

/-- If two functions have equal Fréchet derivatives at every point of a connected open set,
and are equal at one point in that set, then they are equal on that set. -/
theorem _root_.IsOpen.eqOn_of_fderiv_eq (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : ∀ x ∈ s, fderiv 𝕜 f x = fderiv 𝕜 g x) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g := by
  obtain ⟨a, ha⟩ := hs.exists_eq_add_of_fderiv_eq hs' hf hg hf'
  obtain rfl := left_eq_add.mp (hfgx.symm.trans (ha hx))
  simpa using ha

theorem _root_.eq_of_fderiv_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E → G}
    (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g)
    (hf' : ∀ x, fderiv 𝕜 f x = fderiv 𝕜 g x) (x : E) (hfgx : f x = g x) : f = g := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let A : NormedSpace ℝ E := RestrictScalars.normedSpace ℝ 𝕜 E
  suffices Set.univ.EqOn f g from funext fun x => this <| mem_univ x
  exact convex_univ.eqOn_of_fderivWithin_eq hf.differentiableOn hg.differentiableOn
    uniqueDiffOn_univ (fun x _ => by simpa using hf' _) (mem_univ _) hfgx

lemma isLittleO_pow_succ {x₀ : E} {n : ℕ} (hs : Convex ℝ s) (hx₀s : x₀ ∈ s)
    (hff' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x ↦ ‖x - x₀‖ ^ n) :
    (fun x ↦ f x - f x₀) =o[𝓝[s] x₀] fun x ↦ ‖x - x₀‖ ^ (n + 1) := by
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  simp_rw [norm_pow, pow_succ, ← mul_assoc, norm_norm]
  simp_rw [norm_pow, norm_norm] at hf'
  have : ∀ᶠ x in 𝓝[s] x₀, segment ℝ x₀ x ⊆ s ∧ ∀ y ∈ segment ℝ x₀ x, ‖f' y‖ ≤ c * ‖x - x₀‖ ^ n := by
    have h1 : ∀ᶠ x in 𝓝[s] x₀, x ∈ s := eventually_mem_nhdsWithin
    filter_upwards [h1, hs.eventually_nhdsWithin_segment hx₀s (hf' hc)] with x hxs h
    refine ⟨hs.segment_subset hx₀s hxs, fun y hy ↦ (h y hy).trans ?_⟩
    gcongr
    exact norm_sub_le_of_mem_segment hy
  filter_upwards [this] with x ⟨h_segment, h⟩
  convert (convex_segment x₀ x).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x ↦ f x - f x₀) (y := x) (x := x₀) (s := segment ℝ x₀ x) ?_ h
    (left_mem_segment ℝ x₀ x) (right_mem_segment ℝ x₀ x) using 1
  · simp
  · simp only [hasFDerivWithinAt_sub_const_iff]
    exact fun x hx ↦ (hff' x (h_segment hx)).mono h_segment

theorem isLittleO_pow_succ_real {f f' : ℝ → E} {x₀ : ℝ} {n : ℕ} {s : Set ℝ}
    (hs : Convex ℝ s) (hx₀s : x₀ ∈ s)
    (hff' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (hf' : f' =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ n) :
    (fun x ↦ f x - f x₀) =o[𝓝[s] x₀] fun x ↦ (x - x₀) ^ (n + 1) := by
  have h := hs.isLittleO_pow_succ hx₀s hff' ?_ (n := n)
  · rw [Asymptotics.isLittleO_iff] at h ⊢
    simpa using h
  · rw [Asymptotics.isLittleO_iff] at hf' ⊢
    convert hf' using 4 with c hc x
    simp

end Convex

namespace Convex

variable {𝕜 G : Type*} [RCLike 𝕜] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {f f' : 𝕜 → G} {s : Set 𝕜} {x y : 𝕜}

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `HasDerivWithinAt`. -/
theorem norm_image_sub_le_of_norm_hasDerivWithin_le {C : ℝ}
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖ ≤ C) (hs : Convex ℝ s)
    (xs : x ∈ s) (ys : y ∈ s) : ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `HasDerivWithinAt` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_hasDerivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) (bound : ∀ x ∈ s, ‖f' x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivWithinAt)
    (fun x hx => le_trans (by simp) (bound x hx)) hs

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function within
this set is bounded by `C`, then the function is `C`-Lipschitz. Version with `derivWithin` -/
theorem norm_image_sub_le_of_norm_derivWithin_le {C : ℝ} (hf : DifferentiableOn 𝕜 f s)
    (bound : ∀ x ∈ s, ‖derivWithin f s x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound xs
    ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `derivWithin` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_derivWithin_le {C : ℝ≥0} (hs : Convex ℝ s)
    (hf : DifferentiableOn 𝕜 f s) (bound : ∀ x ∈ s, ‖derivWithin f s x‖₊ ≤ C) :
    LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun x hx => (hf x hx).hasDerivWithinAt) bound

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C`, then the function is `C`-Lipschitz. Version with `deriv`. -/
theorem norm_image_sub_le_of_norm_deriv_le {C : ℝ} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖ ≤ C) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ‖f y - f x‖ ≤ C * ‖y - x‖ :=
  hs.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound xs ys

/-- The mean value theorem on a convex set in dimension 1: if the derivative of a function is
bounded by `C` on `s`, then the function is `C`-Lipschitz on `s`.
Version with `deriv` and `LipschitzOnWith`. -/
theorem lipschitzOnWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x)
    (bound : ∀ x ∈ s, ‖deriv f x‖₊ ≤ C) (hs : Convex ℝ s) : LipschitzOnWith C f s :=
  hs.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt) bound

/-- The mean value theorem set in dimension 1: if the derivative of a function is bounded by `C`,
then the function is `C`-Lipschitz. Version with `deriv` and `LipschitzWith`. -/
theorem _root_.lipschitzWith_of_nnnorm_deriv_le {C : ℝ≥0} (hf : Differentiable 𝕜 f)
    (bound : ∀ x, ‖deriv f x‖₊ ≤ C) : LipschitzWith C f :=
  lipschitzOnWith_univ.1 <|
    convex_univ.lipschitzOnWith_of_nnnorm_deriv_le (fun x _ => hf x) fun x _ => bound x

/-- If `f : 𝕜 → G`, `𝕜 = R` or `𝕜 = ℂ`, is differentiable everywhere and its derivative equal zero,
then it is a constant function. -/
theorem _root_.is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0)
    (x y : 𝕜) : f x = f y :=
  is_const_of_fderiv_eq_zero hf (fun z => by ext; simp [← deriv_fderiv, hf']) _ _

theorem _root_.IsOpen.isOpen_inter_preimage_of_deriv_eq_zero
    (hs : IsOpen s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) (t : Set G) : IsOpen (s ∩ f ⁻¹' t) :=
  hs.isOpen_inter_preimage_of_fderiv_eq_zero hf
    (fun x hx ↦ by ext; simp [← deriv_fderiv, hf' hx]) t

theorem _root_.IsOpen.exists_is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) : ∃ a, ∀ x ∈ s, f x = a :=
  hs.exists_is_const_of_fderiv_eq_zero hs' hf (fun {x} hx ↦ by ext; simp [← deriv_fderiv, hf' hx])

theorem _root_.IsOpen.is_const_of_deriv_eq_zero
    (hs : IsOpen s) (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s)
    (hf' : s.EqOn (deriv f) 0) {x y : 𝕜} (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hs.is_const_of_fderiv_eq_zero hs' hf (fun a ha ↦ by ext; simp [← deriv_fderiv, hf' ha]) hx hy

theorem _root_.IsOpen.exists_eq_add_of_deriv_eq {f g : 𝕜 → G} (hs : IsOpen s)
    (hs' : IsPreconnected s)
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) : ∃ a, s.EqOn f (g · + a) :=
  hs.exists_eq_add_of_fderiv_eq hs' hf hg (fun x hx ↦ by simp [← deriv_fderiv, hf' hx])

theorem _root_.IsOpen.eqOn_of_deriv_eq {f g : 𝕜 → G} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hf' : s.EqOn (deriv f) (deriv g)) (hx : x ∈ s) (hfgx : f x = g x) :
    s.EqOn f g :=
  hs.eqOn_of_fderiv_eq hs' hf hg (fun _ hx ↦ ContinuousLinearMap.ext_ring (hf' hx)) hx hfgx

end Convex

end

section RCLike

/-!
### Vector-valued functions `f : E → F`. Strict differentiability.

A `C^1` function is strictly differentiable, when the field is `ℝ` or `ℂ`. This follows from the
mean value inequality on balls, which is a particular case of the above results after restricting
the scalars to `ℝ`. Note that it does not make sense to talk of a convex set over `ℂ`, but balls
make sense and are enough. Many formulations of the mean value inequality could be generalized to
balls over `ℝ` or `ℂ`. For now, we only include the ones that we need.
-/

variable {𝕜 : Type*} [RCLike 𝕜] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] {f : G → H} {f' : G → G →L[𝕜] H} {x : G}

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (hder : ∀ᶠ y in 𝓝 x, HasFDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictFDerivAt f (f' x) x := by
  -- turn little-o definition of strict_fderiv into an epsilon-delta statement
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  refine fun c hc => Metric.eventually_nhds_iff_ball.mpr ?_
  -- the correct ε is the modulus of continuity of f'
  rcases Metric.mem_nhds_iff.mp (inter_mem hder (hcont <| ball_mem_nhds _ hc)) with ⟨ε, ε0, hε⟩
  refine ⟨ε, ε0, ?_⟩
  -- simplify formulas involving the product E × E
  rintro ⟨a, b⟩ h
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at h
  -- exploit the choice of ε as the modulus of continuity of f'
  have hf' : ∀ x' ∈ ball x ε, ‖f' x' - f' x‖ ≤ c := fun x' H' => by
    rw [← dist_eq_norm]
    exact le_of_lt (hε H').2
  -- apply mean value theorem
  letI : NormedSpace ℝ G := RestrictScalars.normedSpace ℝ 𝕜 G
  refine (convex_ball _ _).norm_image_sub_le_of_norm_hasFDerivWithin_le' ?_ hf' h.2 h.1
  exact fun y hy => (hε hy).1.hasFDerivWithinAt

/-- Over the reals or the complexes, a continuously differentiable function is strictly
differentiable. -/
theorem hasStrictDerivAt_of_hasDerivAt_of_continuousAt {f f' : 𝕜 → G} {x : 𝕜}
    (hder : ∀ᶠ y in 𝓝 x, HasDerivAt f (f' y) y) (hcont : ContinuousAt f' x) :
    HasStrictDerivAt f (f' x) x :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hder.mono fun _ hy => hy.hasFDerivAt) <|
    (smulRightL 𝕜 𝕜 G 1).continuous.continuousAt.comp hcont

end RCLike
