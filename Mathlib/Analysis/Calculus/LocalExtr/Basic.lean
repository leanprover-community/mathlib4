/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Add

#align_import analysis.calculus.local_extr from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Local extrema of differentiable functions

## Main definitions

In a real normed space `E` we define `posTangentConeAt (s : Set E) (x : E)`.
This would be the same as `tangentConeAt ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable),
and `fderiv`/`deriv` instead of `HasFDerivAt`/`HasDerivAt`.

* `IsLocalMaxOn.hasFDerivWithinAt_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `IsLocalMaxOn.hasFDerivWithinAt_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `IsLocalMax.hasFDerivAt_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `HasFDeriv*`/`HasDeriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, tangent cone, Fermat's Theorem
-/


universe u v

open Filter Set

open scoped Topology Classical Convex

section Module

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {f' : E →L[ℝ] ℝ} {s : Set E} {a x y : E}

/-!
### Positive tangent cone
-/

/-- "Positive" tangent cone to `s` at `x`; the only difference from `tangentConeAt`
is that we require `c n → ∞` instead of `‖c n‖ → ∞`. One can think about `posTangentConeAt`
as `tangentConeAt NNReal` but we have no theory of normed semifields yet. -/
def posTangentConeAt (s : Set E) (x : E) : Set E :=
  { y : E | ∃ (c : ℕ → ℝ) (d : ℕ → E), (∀ᶠ n in atTop, x + d n ∈ s) ∧
    Tendsto c atTop atTop ∧ Tendsto (fun n => c n • d n) atTop (𝓝 y) }
#align pos_tangent_cone_at posTangentConeAt

theorem posTangentConeAt_mono : Monotone fun s => posTangentConeAt s a := by
  rintro s t hst y ⟨c, d, hd, hc, hcd⟩
  exact ⟨c, d, mem_of_superset hd fun h hn => hst hn, hc, hcd⟩
#align pos_tangent_cone_at_mono posTangentConeAt_mono

theorem mem_posTangentConeAt_of_frequently_mem (h : ∃ᶠ t : ℝ in 𝓝[>] 0, x + t • y ∈ s) :
    y ∈ posTangentConeAt s x := by
  obtain ⟨a, ha, has⟩ := Filter.exists_seq_forall_of_frequently h
  refine ⟨a⁻¹, (a · • y), eventually_of_forall has, tendsto_inv_zero_atTop.comp ha, ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_nhdsWithin_iff.1 ha).2] with n (hn : 0 < a n)
  simp [ne_of_gt hn]

/-- If `[x -[ℝ] x + y] ⊆ s`, then `y` belongs to the positive tangnet cone of `s`.

Before 2024-07-13, this lemma used to be callsed `mem_posTangentConeAt_of_segment_subset`.
See also `sub_mem_posTangentConeAt_of_segment_subset`
for the lemma that used to be called `mem_posTangentConeAt_of_segment_subset`. -/
theorem mem_posTangentConeAt_of_segment_subset (h : [x -[ℝ] x + y] ⊆ s) :
    y ∈ posTangentConeAt s x := by
  refine mem_posTangentConeAt_of_frequently_mem (Eventually.frequently ?_)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [ge_mem_nhds one_pos] with t ht₁ ht₀
  apply h
  rw [segment_eq_image', add_sub_cancel_left]
  exact mem_image_of_mem _ ⟨le_of_lt ht₀, ht₁⟩
#align mem_pos_tangent_cone_at_of_segment_subset' mem_posTangentConeAt_of_segment_subset

@[deprecated (since := "2024-07-13")] -- cleanup docstrings when we drop this alias
alias mem_posTangentConeAt_of_segment_subset' := mem_posTangentConeAt_of_segment_subset

theorem sub_mem_posTangentConeAt_of_segment_subset (h : segment ℝ x y ⊆ s) :
    y - x ∈ posTangentConeAt s x :=
  mem_posTangentConeAt_of_segment_subset <| by rwa [add_sub_cancel]
#align mem_pos_tangent_cone_at_of_segment_subset mem_posTangentConeAt_of_segment_subset

@[simp]
theorem posTangentConeAt_univ : posTangentConeAt univ a = univ :=
  eq_univ_of_forall fun _ => mem_posTangentConeAt_of_segment_subset (subset_univ _)
#align pos_tangent_cone_at_univ posTangentConeAt_univ

/-!
### Fermat's Theorem (vector space)
-/

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : f' y ≤ 0 := by
  rcases hy with ⟨c, d, hd, hc, hcd⟩
  have hc' : Tendsto (‖c ·‖) atTop atTop := tendsto_abs_atTop_atTop.comp hc
  suffices ∀ᶠ n in atTop, c n • (f (a + d n) - f a) ≤ 0 from
    le_of_tendsto (hf.lim atTop hd hc' hcd) this
  replace hd : Tendsto (fun n => a + d n) atTop (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add (tangentConeAt.lim_zero _ hc' hcd), hd⟩
  rw [add_zero] at hd
  filter_upwards [hd.eventually h, hc.eventually_ge_atTop 0] with n hfn hcn
  exact mul_nonpos_of_nonneg_of_nonpos hcn (sub_nonpos.2 hfn)
#align is_local_max_on.has_fderiv_within_at_nonpos IsLocalMaxOn.hasFDerivWithinAt_nonpos

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y ≤ 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_max_on.fderiv_within_nonpos IsLocalMaxOn.fderivWithin_nonpos

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 :=
  le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) <| by simpa using h.hasFDerivWithinAt_nonpos hf hy'
#align is_local_max_on.has_fderiv_within_at_eq_zero IsLocalMaxOn.hasFDerivWithinAt_eq_zero

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_max_on.fderiv_within_eq_zero IsLocalMaxOn.fderivWithin_eq_zero

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : 0 ≤ f' y := by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy
#align is_local_min_on.has_fderiv_within_at_nonneg IsLocalMinOn.hasFDerivWithinAt_nonneg

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (0 : ℝ) ≤ (fderivWithin ℝ f s a : E → ℝ) y :=
  if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_min_on.fderiv_within_nonneg IsLocalMinOn.fderivWithin_nonneg

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'
#align is_local_min_on.has_fderiv_within_at_eq_zero IsLocalMinOn.hasFDerivWithinAt_eq_zero

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_min_on.fderiv_within_eq_zero IsLocalMinOn.fderivWithin_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasFDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasFDerivAt f f' a) : f' = 0 := by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ
#align is_local_min.has_fderiv_at_eq_zero IsLocalMin.hasFDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv ℝ f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf
#align is_local_min.fderiv_eq_zero IsLocalMin.fderiv_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.hasFDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasFDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasFDerivAt_eq_zero hf.neg
#align is_local_max.has_fderiv_at_eq_zero IsLocalMax.hasFDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv ℝ f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf
#align is_local_max.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.hasFDerivAt_eq_zero (h : IsLocalExtr f a) : HasFDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero
#align is_local_extr.has_fderiv_at_eq_zero IsLocalExtr.hasFDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 :=
  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero
#align is_local_extr.fderiv_eq_zero IsLocalExtr.fderiv_eq_zero

end Module

/-!
### Fermat's Theorem
-/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {a b : ℝ}

lemma one_mem_posTangentConeAt_iff_mem_closure :
    1 ∈ posTangentConeAt s a ↔ a ∈ closure (Ioi a ∩ s) := by
  constructor
  · rintro ⟨c, d, hs, hc, hcd⟩
    have : Tendsto (a + d ·) atTop (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add
        (tangentConeAt.lim_zero _ (tendsto_abs_atTop_atTop.comp hc) hcd)
    apply mem_closure_of_tendsto this
    filter_upwards [hc.eventually_gt_atTop 0, hcd.eventually (lt_mem_nhds one_pos), hs]
      with n hcn hcdn hdn
    simp_all
  · intro h
    apply mem_posTangentConeAt_of_frequently_mem
    rw [mem_closure_iff_frequently, ← map_add_left_nhds_zero, frequently_map] at h
    simpa [nhdsWithin, frequently_inf_principal] using h

lemma one_mem_posTangentConeAt_iff_frequently :
    1 ∈ posTangentConeAt s a ↔ ∃ᶠ x in 𝓝[>] a, x ∈ s := by
  rw [one_mem_posTangentConeAt_iff_mem_closure, mem_closure_iff_frequently,
    frequently_nhdsWithin_iff, inter_comm]
  rfl

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1
#align is_local_min.has_deriv_at_eq_zero IsLocalMin.hasDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf
#align is_local_min.deriv_eq_zero IsLocalMin.deriv_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasDerivAt_eq_zero hf.neg
#align is_local_max.has_deriv_at_eq_zero IsLocalMax.hasDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0 :=
  if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf
#align is_local_max.deriv_eq_zero IsLocalMax.deriv_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero
#align is_local_extr.has_deriv_at_eq_zero IsLocalExtr.hasDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 :=
  h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero
#align is_local_extr.deriv_eq_zero IsLocalExtr.deriv_eq_zero

end Real
