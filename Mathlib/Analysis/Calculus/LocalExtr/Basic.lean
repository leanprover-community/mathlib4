/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add

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

@[expose] public section


universe u v

open Filter Set

open scoped Topology Convex NNReal

section Module

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → ℝ} {f' : StrongDual ℝ E} {s : Set E} {a x y : E}

/-!
### Positive tangent cone
-/

theorem posTangentConeAt_mono : Monotone fun s => posTangentConeAt s a := by
  intro s t hst
  exact tangentConeAt_mono hst

theorem mem_posTangentConeAt_of_frequently_mem (h : ∃ᶠ t : ℝ in 𝓝[>] 0, x + t • y ∈ s) :
    y ∈ posTangentConeAt s x := by
  rw [← NNReal.coe_zero, ← NNReal.map_coe_nhdsGT, frequently_map, frequently_iff_neBot] at h
  apply mem_tangentConeAt_of_add_smul_mem (l := 𝓝[>] (0 : ℝ≥0) ⊓ 𝓟 {t | x + (t : ℝ) • y ∈ s})
  · exact tendsto_id'.mpr <| inf_le_left.trans <| nhdsGT_le_nhdsNE _
  · simp [eventually_inf_principal, NNReal.smul_def]

theorem sub_mem_posTangentConeAt_of_segment_subset (h : segment ℝ x y ⊆ s) :
    y - x ∈ posTangentConeAt s x :=
  sub_mem_posTangentConeAt_of_openSegment_subset <| (openSegment_subset_segment ..).trans h

/-- If `[x -[ℝ] x + y] ⊆ s`, then `y` belongs to the positive tangent cone of `s`. -/
theorem mem_posTangentConeAt_of_segment_subset (h : [x -[ℝ] x + y] ⊆ s) :
    y ∈ posTangentConeAt s x := by
  simpa using sub_mem_posTangentConeAt_of_segment_subset h

theorem posTangentConeAt_univ : posTangentConeAt univ a = univ := tangentConeAt_univ

/-!
### Fermat's Theorem (vector space)
-/

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : f' y ≤ 0 := by
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
  suffices ∀ᶠ n in l, c n • (f (a + d n) - f a) ≤ 0 from
    le_of_tendsto (hf.lim hd₀ hd hcd) this
  replace hd : Tendsto (fun n => a + d n) l (𝓝[s] (a + 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add hd₀, hd⟩
  rw [add_zero] at hd
  refine hd.eventually h |>.mono fun n hn ↦ ?_
  exact mul_nonpos_of_nonneg_of_nonpos (c n).coe_nonneg (sub_nonpos.2 hn)

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.fderivWithin_nonpos (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y ≤ 0 := by
  classical
  exact
    if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 :=
  le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) <| by simpa using h.hasFDerivWithinAt_nonpos hf hy'

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMaxOn.fderivWithin_eq_zero (h : IsLocalMaxOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a) : 0 ≤ f' y := by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.fderivWithin_nonneg (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) : (0 : ℝ) ≤ (fderivWithin ℝ f s a : E → ℝ) y := by
  classical
  exact
    if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
    else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMinOn.fderivWithin_eq_zero (h : IsLocalMinOn f s a)
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 := by
  classical
  exact if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasFDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasFDerivAt f f' a) : f' = 0 := by
  ext y
  apply (h.on univ).hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt <;>
      rw [posTangentConeAt_univ] <;>
    apply mem_univ

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.fderiv_eq_zero (h : IsLocalMin f a) : fderiv ℝ f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.hasFDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasFDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasFDerivAt_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.fderiv_eq_zero (h : IsLocalMax f a) : fderiv ℝ f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasFDerivAt_eq_zero hf.hasFDerivAt
  else fderiv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.hasFDerivAt_eq_zero (h : IsLocalExtr f a) : HasFDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasFDerivAt_eq_zero IsLocalMax.hasFDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.fderiv_eq_zero (h : IsLocalExtr f a) : fderiv ℝ f a = 0 :=
  h.elim IsLocalMin.fderiv_eq_zero IsLocalMax.fderiv_eq_zero

end Module

/-!
### Fermat's Theorem
-/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {a b : ℝ}

lemma one_mem_posTangentConeAt_iff_mem_closure :
    1 ∈ posTangentConeAt s a ↔ a ∈ closure (Ioi a ∩ s) := by
  constructor
  · intro h
    rcases exists_fun_of_mem_tangentConeAt h with ⟨ι, l, hl, c, d, hd₀, hd, hcd⟩
    have : Tendsto (a + d ·) l (𝓝 a) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd₀
    apply mem_closure_of_tendsto this
    filter_upwards [hcd.eventually_const_lt one_pos, hd] with n hcdn hdn
    refine ⟨?_, hdn⟩
    simpa using pos_of_mul_pos_right hcdn
  · intro h
    apply mem_posTangentConeAt_of_frequently_mem
    rw [mem_closure_iff_frequently, ← map_add_left_nhds_zero, frequently_map] at h
    simpa [nhdsWithin, frequently_inf_principal] using h

lemma one_mem_posTangentConeAt_iff_frequently :
    1 ∈ posTangentConeAt s a ↔ ∃ᶠ x in 𝓝[>] a, x ∈ s := by
  rw [one_mem_posTangentConeAt_iff_mem_closure, mem_closure_iff_frequently,
    frequently_nhdsWithin_iff, inter_comm]
  simp_rw [mem_inter_iff]

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using DFunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.deriv_eq_zero (h : IsLocalMin f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.hasDerivAt_eq_zero (h : IsLocalMax f a) (hf : HasDerivAt f f' a) : f' = 0 :=
  neg_eq_zero.1 <| h.neg.hasDerivAt_eq_zero hf.neg

/-- **Fermat's Theorem**: the derivative of a function at a local maximum equals zero. -/
theorem IsLocalMax.deriv_eq_zero (h : IsLocalMax f a) : deriv f a = 0 := by
  classical
  exact if hf : DifferentiableAt ℝ f a then h.hasDerivAt_eq_zero hf.hasDerivAt
  else deriv_zero_of_not_differentiableAt hf

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.hasDerivAt_eq_zero (h : IsLocalExtr f a) : HasDerivAt f f' a → f' = 0 :=
  h.elim IsLocalMin.hasDerivAt_eq_zero IsLocalMax.hasDerivAt_eq_zero

/-- **Fermat's Theorem**: the derivative of a function at a local extremum equals zero. -/
theorem IsLocalExtr.deriv_eq_zero (h : IsLocalExtr f a) : deriv f a = 0 :=
  h.elim IsLocalMin.deriv_eq_zero IsLocalMax.deriv_eq_zero

end Real
