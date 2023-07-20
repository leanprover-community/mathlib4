/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Order.ExtendFrom
import Mathlib.Topology.Algebra.Polynomial

#align_import analysis.calculus.local_extr from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Local extrema of smooth functions

## Main definitions

In a real normed space `E` we define `posTangentConeAt (s : Set E) (x : E)`.
This would be the same as `tangentConeAt ℝ≥0 s x` if we had a theory of normed semifields.
This set is used in the proof of Fermat's Theorem (see below), and can be used to formalize
[Lagrange multipliers](https://en.wikipedia.org/wiki/Lagrange_multiplier) and/or
[Karush–Kuhn–Tucker conditions](https://en.wikipedia.org/wiki/Karush–Kuhn–Tucker_conditions).

## Main statements

For each theorem name listed below,
we also prove similar theorems for `min`, `extr` (if applicable),
and `(f)deriv` instead of `has_fderiv`.

* `IsLocalMaxOn.hasFDerivWithinAt_nonpos` : `f' y ≤ 0` whenever `a` is a local maximum
  of `f` on `s`, `f` has derivative `f'` at `a` within `s`, and `y` belongs to the positive tangent
  cone of `s` at `a`.

* `IsLocalMaxOn.hasFDerivWithinAt_eq_zero` : In the settings of the previous theorem, if both
  `y` and `-y` belong to the positive tangent cone, then `f' y = 0`.

* `IsLocalMax.hasFDerivAt_eq_zero` :
  [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points)),
  the derivative of a differentiable function at a local extremum point equals zero.

* `exists_hasDerivAt_eq_zero` :
  [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem): given a function `f` continuous
  on `[a, b]` and differentiable on `(a, b)`, there exists `c ∈ (a, b)` such that `f' c = 0`.

## Implementation notes

For each mathematical fact we prove several versions of its formalization:

* for maxima and minima;
* using `HasFDeriv*`/`HasDeriv*` or `fderiv*`/`deriv*`.

For the `fderiv*`/`deriv*` versions we omit the differentiability condition whenever it is possible
due to the fact that `fderiv` and `deriv` are defined to be zero for non-differentiable functions.

## References

* [Fermat's Theorem](https://en.wikipedia.org/wiki/Fermat's_theorem_(stationary_points));
* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);
* [Tangent cone](https://en.wikipedia.org/wiki/Tangent_cone);

## Tags

local extremum, Fermat's Theorem, Rolle's Theorem
-/


universe u v

open Filter Set

open scoped Topology Classical Polynomial

section Module

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {a : E} {f' : E →L[ℝ] ℝ}

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

theorem mem_posTangentConeAt_of_segment_subset {s : Set E} {x y : E} (h : segment ℝ x y ⊆ s) :
    y - x ∈ posTangentConeAt s x := by
  let c := fun n : ℕ => (2 : ℝ) ^ n
  let d := fun n : ℕ => (c n)⁻¹ • (y - x)
  refine' ⟨c, d, Filter.univ_mem' fun n => h _, tendsto_pow_atTop_atTop_of_one_lt one_lt_two, _⟩
  show x + d n ∈ segment ℝ x y
  · rw [segment_eq_image']
    refine' ⟨(c n)⁻¹, ⟨_, _⟩, rfl⟩
    exacts [inv_nonneg.2 (pow_nonneg zero_le_two _), inv_le_one (one_le_pow_of_one_le one_le_two _)]
  show Tendsto (fun n => c n • d n) atTop (𝓝 (y - x))
  · exact tendsto_const_nhds.congr fun n ↦ (smul_inv_smul₀ (pow_ne_zero _ two_ne_zero) _).symm
#align mem_pos_tangent_cone_at_of_segment_subset mem_posTangentConeAt_of_segment_subset

theorem mem_posTangentConeAt_of_segment_subset' {s : Set E} {x y : E}
    (h : segment ℝ x (x + y) ⊆ s) : y ∈ posTangentConeAt s x := by
  simpa only [add_sub_cancel'] using mem_posTangentConeAt_of_segment_subset h
#align mem_pos_tangent_cone_at_of_segment_subset' mem_posTangentConeAt_of_segment_subset'

theorem posTangentConeAt_univ : posTangentConeAt univ a = univ :=
  eq_univ_of_forall fun _ => mem_posTangentConeAt_of_segment_subset' (subset_univ _)
#align pos_tangent_cone_at_univ posTangentConeAt_univ

/-- If `f` has a local max on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_nonpos {s : Set E} (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) {y} (hy : y ∈ posTangentConeAt s a) : f' y ≤ 0 := by
  rcases hy with ⟨c, d, hd, hc, hcd⟩
  have hc' : Tendsto (‖c ·‖) atTop atTop := tendsto_abs_atTop_atTop.comp hc
  suffices : ∀ᶠ n in atTop, c n • (f (a + d n) - f a) ≤ 0
  · exact le_of_tendsto (hf.lim atTop hd hc' hcd) this
  replace hd : Tendsto (fun n => a + d n) atTop (𝓝[s] (a + 0))
  · exact tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.add (tangentConeAt.lim_zero _ hc' hcd), hd⟩
  rw [add_zero] at hd
  filter_upwards [hd.eventually h, hc.eventually_ge_atTop 0] with n hfn hcn
  exact mul_nonpos_of_nonneg_of_nonpos hcn (sub_nonpos.2 hfn)
#align is_local_max_on.has_fderiv_within_at_nonpos IsLocalMaxOn.hasFDerivWithinAt_nonpos

/-- If `f` has a local max on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.fderivWithin_nonpos {s : Set E} (h : IsLocalMaxOn f s a) {y}
    (hy : y ∈ posTangentConeAt s a) : (fderivWithin ℝ f s a : E → ℝ) y ≤ 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonpos hf.hasFDerivWithinAt hy
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_max_on.fderiv_within_nonpos IsLocalMaxOn.fderivWithin_nonpos

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMaxOn.hasFDerivWithinAt_eq_zero {s : Set E} (h : IsLocalMaxOn f s a)
    (hf : HasFDerivWithinAt f f' s a) {y} (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 :=
  le_antisymm (h.hasFDerivWithinAt_nonpos hf hy) <| by simpa using h.hasFDerivWithinAt_nonpos hf hy'
#align is_local_max_on.has_fderiv_within_at_eq_zero IsLocalMaxOn.hasFDerivWithinAt_eq_zero

/-- If `f` has a local max on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMaxOn.fderivWithin_eq_zero {s : Set E} (h : IsLocalMaxOn f s a) {y}
    (hy : y ∈ posTangentConeAt s a) (hy' : -y ∈ posTangentConeAt s a) :
    (fderivWithin ℝ f s a : E → ℝ) y = 0 :=
  if hf : DifferentiableWithinAt ℝ f s a then
    h.hasFDerivWithinAt_eq_zero hf.hasFDerivWithinAt hy hy'
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_max_on.fderiv_within_eq_zero IsLocalMaxOn.fderivWithin_eq_zero

/-- If `f` has a local min on `s` at `a`, `f'` is the derivative of `f` at `a` within `s`, and
`y` belongs to the positive tangent cone of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_nonneg {s : Set E} (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) {y} (hy : y ∈ posTangentConeAt s a) : 0 ≤ f' y := by
  simpa using h.neg.hasFDerivWithinAt_nonpos hf.neg hy
#align is_local_min_on.has_fderiv_within_at_nonneg IsLocalMinOn.hasFDerivWithinAt_nonneg

/-- If `f` has a local min on `s` at `a` and `y` belongs to the positive tangent cone
of `s` at `a`, then `0 ≤ f' y`. -/
theorem IsLocalMinOn.fderivWithin_nonneg {s : Set E} (h : IsLocalMinOn f s a) {y}
    (hy : y ∈ posTangentConeAt s a) : (0 : ℝ) ≤ (fderivWithin ℝ f s a : E → ℝ) y :=
  if hf : DifferentiableWithinAt ℝ f s a then h.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hy
  else by rw [fderivWithin_zero_of_not_differentiableWithinAt hf]; rfl
#align is_local_min_on.fderiv_within_nonneg IsLocalMinOn.fderivWithin_nonneg

/-- If `f` has a local max on `s` at `a`, `f'` is a derivative of `f` at `a` within `s`, and
both `y` and `-y` belong to the positive tangent cone of `s` at `a`, then `f' y ≤ 0`. -/
theorem IsLocalMinOn.hasFDerivWithinAt_eq_zero {s : Set E} (h : IsLocalMinOn f s a)
    (hf : HasFDerivWithinAt f f' s a) {y} (hy : y ∈ posTangentConeAt s a)
    (hy' : -y ∈ posTangentConeAt s a) : f' y = 0 := by
  simpa using h.neg.hasFDerivWithinAt_eq_zero hf.neg hy hy'
#align is_local_min_on.has_fderiv_within_at_eq_zero IsLocalMinOn.hasFDerivWithinAt_eq_zero

/-- If `f` has a local min on `s` at `a` and both `y` and `-y` belong to the positive tangent cone
of `s` at `a`, then `f' y = 0`. -/
theorem IsLocalMinOn.fderivWithin_eq_zero {s : Set E} (h : IsLocalMinOn f s a) {y}
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

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {a b : ℝ}

/-- **Fermat's Theorem**: the derivative of a function at a local minimum equals zero. -/
theorem IsLocalMin.hasDerivAt_eq_zero (h : IsLocalMin f a) (hf : HasDerivAt f f' a) : f' = 0 := by
  simpa using FunLike.congr_fun (h.hasFDerivAt_eq_zero (hasDerivAt_iff_hasFDerivAt.1 hf)) 1
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

section Rolle

variable (f f' : ℝ → ℝ) {a b : ℝ}

/-- A continuous function on a closed interval with `f a = f b` takes either its maximum
or its minimum value at a point in the interior of the interval. -/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x :=
    isCompact_Icc.exists_forall_le ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C :=
    isCompact_Icc.exists_forall_ge ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp only [mem_setOf_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
    · refine' ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt _ hC, lt_of_le_of_ne Cmem.2 <| mt _ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
  · refine' ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt _ hc, lt_of_le_of_ne cmem.2 <| mt _ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
#align exists_Ioo_extr_on_Icc exists_Ioo_extr_on_Icc

/-- A continuous function on a closed interval with `f a = f b` has a local extremum at some
point of the corresponding open interval. -/
theorem exists_local_extr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc f hab hfc hfI
  ⟨c, cmem, hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩
#align exists_local_extr_Ioo exists_local_extr_Ioo

/-- **Rolle's Theorem** `HasDerivAt` version -/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) : ∃ c ∈ Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI
  ⟨c, cmem, hc.hasDerivAt_eq_zero <| hff' c cmem⟩
#align exists_has_deriv_at_eq_zero exists_hasDerivAt_eq_zero

/-- **Rolle's Theorem** `deriv` version -/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_local_extr_Ioo f hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩
#align exists_deriv_eq_zero exists_deriv_eq_zero

variable {f f'} {l : ℝ}

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has derivative `f'`
on `(a, b)` and has the same limit `l` at `𝓝[>] a` and `𝓝[<] b`, then `f' c = 0`
for some `c ∈ (a, b)`.  -/
theorem exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Ioo a b, f' c = 0 := by
  have : ContinuousOn f (Ioo a b) := fun x hx => (hff' x hx).continuousAt.continuousWithinAt
  have hcont := continuousOn_Icc_extendFrom_Ioo hab.ne this hfa hfb
  obtain ⟨c, hc, hcextr⟩ : ∃ c ∈ Ioo a b, IsLocalExtr (extendFrom (Ioo a b) f) c := by
    apply exists_local_extr_Ioo _ hab hcont
    rw [eq_lim_at_right_extendFrom_Ioo hab hfb]
    exact eq_lim_at_left_extendFrom_Ioo hab hfa
  use c, hc
  apply (hcextr.congr _).hasDerivAt_eq_zero (hff' c hc)
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨Ioo a b, Ioo_mem_nhds hc.1 hc.2, extendFrom_extends this⟩
#align exists_has_deriv_at_eq_zero' exists_hasDerivAt_eq_zero'

/-- **Rolle's Theorem**, a version for a function on an open interval: if `f` has the same limit
`l` at `𝓝[>] a` and `𝓝[<] b`, then `deriv f c = 0` for some `c ∈ (a, b)`. This version
does not require differentiability of `f` because we define `deriv f c = 0` whenever `f` is not
differentiable at `c`. -/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : ∃ c ∈ Ioo a b, deriv f c = 0 :=
  by_cases
    (fun h : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x =>
      show ∃ c ∈ Ioo a b, deriv f c = 0 from
        exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt)
    fun h : ¬∀ x ∈ Ioo a b, DifferentiableAt ℝ f x =>
    have h : ∃ x, x ∈ Ioo a b ∧ ¬DifferentiableAt ℝ f x := by push_neg at h; exact h
    let ⟨c, hc, hcdiff⟩ := h
    ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩
#align exists_deriv_eq_zero' exists_deriv_eq_zero'

end Rolle

namespace Polynomial

open scoped BigOperators

/-- The number of roots of a real polynomial `p` is at most the number of roots of its derivative
that are not roots of `p` plus one. -/
theorem card_roots_toFinset_le_card_roots_derivative_diff_roots_succ (p : ℝ[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  cases' eq_or_ne (derivative p) 0 with hp' hp'
  · rw [eq_C_of_derivative_eq_zero hp', roots_C, Multiset.toFinset_zero, Finset.card_empty]
    exact zero_le _
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine' Finset.card_le_diff_of_interleaved fun x hx y hy hxy hxy' => _
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ :=
    exists_deriv_eq_zero (fun x : ℝ => eval x p) hxy p.continuousOn (hx.trans hy.symm)
  refine' ⟨z, _, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]
#align polynomial.card_roots_to_finset_le_card_roots_derivative_diff_roots_succ Polynomial.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ

/-- The number of roots of a real polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_roots_toFinset_le_derivative (p : ℝ[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ.trans <|
    add_le_add_right (Finset.card_mono <| Finset.sdiff_subset _ _) _
#align polynomial.card_roots_to_finset_le_derivative Polynomial.card_roots_toFinset_le_derivative

/-- The number of roots of a real polynomial (counted with multiplicities) is at most the number of
roots of its derivative (counted with multiplicities) plus one. -/
theorem card_roots_le_derivative (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1 :=
  calc
    Multiset.card p.roots = ∑ x in p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x in p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x in p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x in p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun x _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ)
    _ ≤ (∑ x in p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x in p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots]
      refine' add_le_add_left (add_le_add_right ((Finset.card_eq_sum_ones _).trans_le _) _) _
      refine' Finset.sum_le_sum fun x hx => Nat.succ_le_iff.2 <| _
      rw [Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union, ←
        Multiset.toFinset_sum_count_eq, ← Finset.sum_subset (Finset.subset_union_right _ _)]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂
#align polynomial.card_roots_le_derivative Polynomial.card_roots_le_derivative

/-- The number of real roots of a polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_rootSet_le_derivative {F : Type _} [CommRing F] [Algebra F ℝ] (p : F[X]) :
    Fintype.card (p.rootSet ℝ) ≤ Fintype.card (p.derivative.rootSet ℝ) + 1 := by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F ℝ))
#align polynomial.card_root_set_le_derivative Polynomial.card_rootSet_le_derivative

end Polynomial
