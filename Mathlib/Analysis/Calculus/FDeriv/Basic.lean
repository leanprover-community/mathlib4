/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Analysis.NormedSpace.OperatorNorm.Asymptotics

#align_import analysis.calculus.fderiv.basic from "leanprover-community/mathlib"@"41bef4ae1254365bc190aee63b947674d2977f01"

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `HasFDerivWithinAt f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasFDerivAt f f' x := HasFDerivWithinAt f f' x univ`

Finally,

  `HasStrictFDerivAt f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`IsBoundedBilinearMap.hasFDerivAt` twice: first for `HasFDerivAt`, then for
`HasStrictFDerivAt`.

## Main results

In addition to the definition and basic properties of the derivative,
the folder `Analysis/Calculus/FDeriv/` contains the usual formulas
(and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps (`Linear.lean`)
* bounded bilinear maps (`Bilinear.lean`)
* sum of two functions (`Add.lean`)
* sum of finitely many functions (`Add.lean`)
* multiplication of a function by a scalar constant (`Add.lean`)
* negative of a function (`Add.lean`)
* subtraction of two functions (`Add.lean`)
* multiplication of a function by a scalar function (`Mul.lean`)
* multiplication of two scalar functions (`Mul.lean`)
* composition of functions (the chain rule) (`Comp.lean`)
* inverse function (`Mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../Inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `Deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : Differentiable ℝ (fun x ↦ sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : DifferentiableAt ℝ (fun x ↦ exp x / (1 + sin x)) x := by
  simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `Analysis.SpecialFunctions.Trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `Deriv.lean`.

## Implementation details

The derivative is defined in terms of the `isLittleO` relation, but also
characterized in terms of the `Tendsto` relation.

We also introduce predicates `DifferentiableWithinAt 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `DifferentiableAt 𝕜 f x`,
`DifferentiableOn 𝕜 f s` and `Differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderivWithin 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `UniqueDiffWithinAt s x` and
`UniqueDiffOn s`, defined in `TangentCone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(fun x ↦ exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`Tests/Differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

-/

open Filter Asymptotics ContinuousLinearMap Set Metric

open scoped Classical
open Topology NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `HasFDerivAt`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `HasFDerivWithinAt`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
@[mk_iff hasFDerivAtFilter_iff_isLittleO]
structure HasFDerivAtFilter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : Filter E) : Prop where
  of_isLittleO :: isLittleO : (fun x' => f x' - f x - f' (x' - x)) =o[L] fun x' => x' - x
#align has_fderiv_at_filter HasFDerivAtFilter

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
@[fun_prop]
def HasFDerivWithinAt (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) :=
  HasFDerivAtFilter f f' x (𝓝[s] x)
#align has_fderiv_within_at HasFDerivWithinAt

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
@[fun_prop]
def HasFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFDerivAtFilter f f' x (𝓝 x)
#align has_fderiv_at HasFDerivAt

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
@[fun_prop]
def HasStrictFDerivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2
#align has_strict_fderiv_at HasStrictFDerivAt

variable (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
@[fun_prop]
def DifferentiableWithinAt (f : E → F) (s : Set E) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x
#align differentiable_within_at DifferentiableWithinAt

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
@[fun_prop]
def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFDerivAt f f' x
#align differentiable_at DifferentiableAt

/-- If `f` has a derivative at `x` within `s`, then `fderivWithin 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. If `x` is isolated in `s`, we take the derivative within `s` to
be zero for convenience. -/
irreducible_def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if 𝓝[s \ {x}] x = ⊥ then 0 else
  if h : ∃ f', HasFDerivWithinAt f f' s x then Classical.choose h else 0
#align fderiv_within fderivWithin

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
irreducible_def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFDerivAt f f' x then Classical.choose h else 0
#align fderiv fderiv

/-- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
@[fun_prop]
def DifferentiableOn (f : E → F) (s : Set E) :=
  ∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x
#align differentiable_on DifferentiableOn

/-- `Differentiable 𝕜 f` means that `f` is differentiable at any point. -/
@[fun_prop]
def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x
#align differentiable Differentiable

variable {𝕜}
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter E}

theorem fderivWithin_zero_of_isolated (h : 𝓝[s \ {x}] x = ⊥) : fderivWithin 𝕜 f s x = 0 := by
  rw [fderivWithin, if_pos h]

theorem fderivWithin_zero_of_nmem_closure (h : x ∉ closure s) : fderivWithin 𝕜 f s x = 0 := by
  apply fderivWithin_zero_of_isolated
  simp only [mem_closure_iff_nhdsWithin_neBot, neBot_iff, Ne, Classical.not_not] at h
  rw [eq_bot_iff, ← h]
  exact nhdsWithin_mono _ diff_subset

theorem fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 f s x = 0 := by
  have : ¬∃ f', HasFDerivWithinAt f f' s x := h
  simp [fderivWithin, this]
#align fderiv_within_zero_of_not_differentiable_within_at fderivWithin_zero_of_not_differentiableWithinAt

theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 := by
  have : ¬∃ f', HasFDerivAt f f' x := h
  simp [fderiv, this]
#align fderiv_zero_of_not_differentiable_at fderiv_zero_of_not_differentiableAt

section DerivativeUniqueness

/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `UniqueDiffWithinAt` and `UniqueDiffOn` indeed imply the
uniqueness of the derivative. -/
/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} (l : Filter α)
    {c : α → 𝕜} {d : α → E} {v : E} (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (clim : Tendsto (fun n => ‖c n‖) l atTop) (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) := by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    conv in 𝓝[s] x => rw [← add_zero x]
    rw [nhdsWithin, tendsto_inf]
    constructor
    · apply tendsto_const_nhds.add (tangentConeAt.lim_zero l clim cdlim)
    · rwa [tendsto_principal]
  have : (fun y => f y - f x - f' (y - x)) =o[𝓝[s] x] fun y => y - x := h.isLittleO
  have : (fun n => f (x + d n) - f x - f' (x + d n - x)) =o[l] fun n => x + d n - x :=
    this.comp_tendsto tendsto_arg
  have : (fun n => f (x + d n) - f x - f' (d n)) =o[l] d := by simpa only [add_sub_cancel_left]
  have : (fun n => c n • (f (x + d n) - f x - f' (d n))) =o[l] fun n => c n • d n :=
    (isBigO_refl c l).smul_isLittleO this
  have : (fun n => c n • (f (x + d n) - f x - f' (d n))) =o[l] fun _ => (1 : ℝ) :=
    this.trans_isBigO (cdlim.isBigO_one ℝ)
  have L1 : Tendsto (fun n => c n • (f (x + d n) - f x - f' (d n))) l (𝓝 0) :=
    (isLittleO_one_iff ℝ).1 this
  have L2 : Tendsto (fun n => f' (c n • d n)) l (𝓝 (f' v)) :=
    Tendsto.comp f'.cont.continuousAt cdlim
  have L3 :
    Tendsto (fun n => c n • (f (x + d n) - f x - f' (d n)) + f' (c n • d n)) l (𝓝 (0 + f' v)) :=
    L1.add L2
  have :
    (fun n => c n • (f (x + d n) - f x - f' (d n)) + f' (c n • d n)) = fun n =>
      c n • (f (x + d n) - f x) := by
    ext n
    simp [smul_add, smul_sub]
  rwa [this, zero_add] at L3
#align has_fderiv_within_at.lim HasFDerivWithinAt.lim

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) :=
  fun _ ⟨_, _, dtop, clim, cdlim⟩ =>
  tendsto_nhds_unique (hf.lim atTop dtop clim cdlim) (hg.lim atTop dtop clim cdlim)
#align has_fderiv_within_at.unique_on HasFDerivWithinAt.unique_on

/-- `UniqueDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)
#align unique_diff_within_at.eq UniqueDiffWithinAt.eq

theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFDerivWithinAt f f' s x)
    (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).eq h h₁
#align unique_diff_on.eq UniqueDiffOn.eq

end DerivativeUniqueness

section FDerivProperties

/-! ### Basic properties of the derivative -/


theorem hasFDerivAtFilter_iff_tendsto :
    HasFDerivAtFilter f f' x L ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) := by
  have h : ∀ x', ‖x' - x‖ = 0 → ‖f x' - f x - f' (x' - x)‖ = 0 := fun x' hx' => by
    rw [sub_eq_zero.1 (norm_eq_zero.1 hx')]
    simp
  rw [hasFDerivAtFilter_iff_isLittleO, ← isLittleO_norm_left, ← isLittleO_norm_right,
    isLittleO_iff_tendsto h]
  exact tendsto_congr fun _ => div_eq_inv_mul _ _
#align has_fderiv_at_filter_iff_tendsto hasFDerivAtFilter_iff_tendsto

theorem hasFDerivWithinAt_iff_tendsto :
    HasFDerivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_fderiv_within_at_iff_tendsto hasFDerivWithinAt_iff_tendsto

theorem hasFDerivAt_iff_tendsto :
    HasFDerivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto
#align has_fderiv_at_iff_tendsto hasFDerivAt_iff_tendsto

theorem hasFDerivAt_iff_isLittleO_nhds_zero :
    HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h := by
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, ← map_add_left_nhds_zero x, isLittleO_map]
  simp [(· ∘ ·)]
#align has_fderiv_at_iff_is_o_nhds_zero hasFDerivAt_iff_isLittleO_nhds_zero

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem HasFDerivAt.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] at hyC
  calc
    ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ := norm_le_insert _ _
    _ ≤ C * ‖y‖ + ε * ‖y‖ := add_le_add hyC hy
    _ = (C + ε) * ‖y‖ := (add_mul _ _ _).symm

#align has_fderiv_at.le_of_lip' HasFDerivAt.le_of_lip'

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFDerivAt.le_of_lipschitzOn
    {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)
#align has_fderiv_at.le_of_lip HasFDerivAt.le_of_lipschitzOn

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFDerivAt.le_of_lipschitz {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOn_univ.2 hlip)

nonrec theorem HasFDerivAtFilter.mono (h : HasFDerivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasFDerivAtFilter f f' x L₁ :=
  .of_isLittleO <| h.isLittleO.mono hst
#align has_fderiv_at_filter.mono HasFDerivAtFilter.mono

theorem HasFDerivWithinAt.mono_of_mem (h : HasFDerivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| nhdsWithin_le_iff.mpr hst
#align has_fderiv_within_at.mono_of_mem HasFDerivWithinAt.mono_of_mem
#align has_fderiv_within_at.nhds_within HasFDerivWithinAt.mono_of_mem

nonrec theorem HasFDerivWithinAt.mono (h : HasFDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| nhdsWithin_mono _ hst
#align has_fderiv_within_at.mono HasFDerivWithinAt.mono

theorem HasFDerivAt.hasFDerivAtFilter (h : HasFDerivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasFDerivAtFilter f f' x L :=
  h.mono hL
#align has_fderiv_at.has_fderiv_at_filter HasFDerivAt.hasFDerivAtFilter

@[fun_prop]
theorem HasFDerivAt.hasFDerivWithinAt (h : HasFDerivAt f f' x) : HasFDerivWithinAt f f' s x :=
  h.hasFDerivAtFilter inf_le_left
#align has_fderiv_at.has_fderiv_within_at HasFDerivAt.hasFDerivWithinAt

@[fun_prop]
theorem HasFDerivWithinAt.differentiableWithinAt (h : HasFDerivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨f', h⟩
#align has_fderiv_within_at.differentiable_within_at HasFDerivWithinAt.differentiableWithinAt

@[fun_prop]
theorem HasFDerivAt.differentiableAt (h : HasFDerivAt f f' x) : DifferentiableAt 𝕜 f x :=
  ⟨f', h⟩
#align has_fderiv_at.differentiable_at HasFDerivAt.differentiableAt

@[simp]
theorem hasFDerivWithinAt_univ : HasFDerivWithinAt f f' univ x ↔ HasFDerivAt f f' x := by
  simp only [HasFDerivWithinAt, nhdsWithin_univ]
  rfl
#align has_fderiv_within_at_univ hasFDerivWithinAt_univ

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ
#align has_fderiv_within_at.has_fderiv_at_of_univ HasFDerivWithinAt.hasFDerivAt_of_univ

theorem hasFDerivWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  rw [HasFDerivAt, HasFDerivWithinAt, nhdsWithin_eq_nhds.mpr h]

lemma hasFDerivWithinAt_of_isOpen (h : IsOpen s) (hx : x ∈ s) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x :=
  hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

theorem hasFDerivWithinAt_insert {y : E} :
    HasFDerivWithinAt f f' (insert y s) x ↔ HasFDerivWithinAt f f' s x := by
  rcases eq_or_ne x y with (rfl | h)
  · simp_rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO]
    apply Asymptotics.isLittleO_insert
    simp only [sub_self, map_zero]
  refine ⟨fun h => h.mono <| subset_insert y s, fun hf => hf.mono_of_mem ?_⟩
  simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]
#align has_fderiv_within_at_insert hasFDerivWithinAt_insert

alias ⟨HasFDerivWithinAt.of_insert, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert
#align has_fderiv_within_at.of_insert HasFDerivWithinAt.of_insert
#align has_fderiv_within_at.insert' HasFDerivWithinAt.insert'

protected theorem HasFDerivWithinAt.insert (h : HasFDerivWithinAt g g' s x) :
    HasFDerivWithinAt g g' (insert x s) x :=
  h.insert'
#align has_fderiv_within_at.insert HasFDerivWithinAt.insert

theorem hasFDerivWithinAt_diff_singleton (y : E) :
    HasFDerivWithinAt f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert, insert_diff_singleton, hasFDerivWithinAt_insert]
#align has_fderiv_within_at_diff_singleton hasFDerivWithinAt_diff_singleton

theorem HasStrictFDerivAt.isBigO_sub (hf : HasStrictFDerivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  hf.isBigO.congr_of_sub.2 (f'.isBigO_comp _ _)
set_option linter.uppercaseLean3 false in
#align has_strict_fderiv_at.is_O_sub HasStrictFDerivAt.isBigO_sub

theorem HasFDerivAtFilter.isBigO_sub (h : HasFDerivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  h.isLittleO.isBigO.congr_of_sub.2 (f'.isBigO_sub _ _)
set_option linter.uppercaseLean3 false in
#align has_fderiv_at_filter.is_O_sub HasFDerivAtFilter.isBigO_sub

@[fun_prop]
protected theorem HasStrictFDerivAt.hasFDerivAt (hf : HasStrictFDerivAt f f' x) :
    HasFDerivAt f f' x := by
  rw [HasFDerivAt, hasFDerivAtFilter_iff_isLittleO, isLittleO_iff]
  exact fun c hc => tendsto_id.prod_mk_nhds tendsto_const_nhds (isLittleO_iff.1 hf hc)
#align has_strict_fderiv_at.has_fderiv_at HasStrictFDerivAt.hasFDerivAt

protected theorem HasStrictFDerivAt.differentiableAt (hf : HasStrictFDerivAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  hf.hasFDerivAt.differentiableAt
#align has_strict_fderiv_at.differentiable_at HasStrictFDerivAt.differentiableAt

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
theorem HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x)
    (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  have := hf.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩
#align has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt` for a
more precise statement. -/
theorem HasStrictFDerivAt.exists_lipschitzOnWith (hf : HasStrictFDerivAt f f' x) :
    ∃ K, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s :=
  (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt
#align has_strict_fderiv_at.exists_lipschitz_on_with HasStrictFDerivAt.exists_lipschitzOnWith

/-- Directional derivative agrees with `HasFDeriv`. -/
theorem HasFDerivAt.lim (hf : HasFDerivAt f f' x) (v : E) {α : Type*} {c : α → 𝕜} {l : Filter α}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    Tendsto (fun n => c n • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) := by
  refine (hasFDerivWithinAt_univ.2 hf).lim _ univ_mem hc ?_
  intro U hU
  refine (eventually_ne_of_tendsto_norm_atTop hc (0 : 𝕜)).mono fun y hy => ?_
  convert mem_of_mem_nhds hU
  dsimp only
  rw [← mul_smul, mul_inv_cancel hy, one_smul]
#align has_fderiv_at.lim HasFDerivAt.lim

theorem HasFDerivAt.unique (h₀ : HasFDerivAt f f₀' x) (h₁ : HasFDerivAt f f₁' x) : f₀' = f₁' := by
  rw [← hasFDerivWithinAt_univ] at h₀ h₁
  exact uniqueDiffWithinAt_univ.eq h₀ h₁
#align has_fderiv_at.unique HasFDerivAt.unique

theorem hasFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]
#align has_fderiv_within_at_inter' hasFDerivWithinAt_inter'

theorem hasFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]
#align has_fderiv_within_at_inter hasFDerivWithinAt_inter

theorem HasFDerivWithinAt.union (hs : HasFDerivWithinAt f f' s x)
    (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s ∪ t) x := by
  simp only [HasFDerivWithinAt, nhdsWithin_union]
  exact .of_isLittleO <| hs.isLittleO.sup ht.isLittleO
#align has_fderiv_within_at.union HasFDerivWithinAt.union

theorem HasFDerivWithinAt.hasFDerivAt (h : HasFDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f f' x := by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h
#align has_fderiv_within_at.has_fderiv_at HasFDerivWithinAt.hasFDerivAt

theorem DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.imp fun _ hf' => hf'.hasFDerivAt hs
#align differentiable_within_at.differentiable_at DifferentiableWithinAt.differentiableAt

/-- If `x` is isolated in `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem HasFDerivWithinAt.of_nhdsWithin_eq_bot (h : 𝓝[s\{x}] x = ⊥) :
    HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_diff_singleton x, HasFDerivWithinAt, h, hasFDerivAtFilter_iff_isLittleO]
  apply isLittleO_bot

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem hasFDerivWithinAt_of_nmem_closure (h : x ∉ closure s) : HasFDerivWithinAt f f' s x :=
  .of_nhdsWithin_eq_bot <| eq_bot_mono (nhdsWithin_mono _ diff_subset) <| by
    rwa [mem_closure_iff_nhdsWithin_neBot, not_neBot] at h
#align has_fderiv_within_at_of_not_mem_closure hasFDerivWithinAt_of_nmem_closure

theorem DifferentiableWithinAt.hasFDerivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasFDerivWithinAt f (fderivWithin 𝕜 f s x) s x := by
  by_cases H : 𝓝[s \ {x}] x = ⊥
  · exact .of_nhdsWithin_eq_bot H
  · unfold DifferentiableWithinAt at h
    rw [fderivWithin, if_neg H, dif_pos h]
    exact Classical.choose_spec h
#align differentiable_within_at.has_fderiv_within_at DifferentiableWithinAt.hasFDerivWithinAt

theorem DifferentiableAt.hasFDerivAt (h : DifferentiableAt 𝕜 f x) :
    HasFDerivAt f (fderiv 𝕜 f x) x := by
  dsimp only [DifferentiableAt] at h
  rw [fderiv, dif_pos h]
  exact Classical.choose_spec h
#align differentiable_at.has_fderiv_at DifferentiableAt.hasFDerivAt

theorem DifferentiableOn.hasFDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt
#align differentiable_on.has_fderiv_at DifferentiableOn.hasFDerivAt

theorem DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hs).differentiableAt
#align differentiable_on.differentiable_at DifferentiableOn.differentiableAt

theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt
#align differentiable_on.eventually_differentiable_at DifferentiableOn.eventually_differentiableAt

protected theorem HasFDerivAt.fderiv (h : HasFDerivAt f f' x) : fderiv 𝕜 f x = f' := by
  ext
  rw [h.unique h.differentiableAt.hasFDerivAt]
#align has_fderiv_at.fderiv HasFDerivAt.fderiv

theorem fderiv_eq {f' : E → E →L[𝕜] F} (h : ∀ x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv
#align fderiv_eq fderiv_eq

variable (𝕜)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem norm_fderiv_le_of_lip' {f : E → F} {x₀ : E}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖fderiv 𝕜 f x₀‖ ≤ C := by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
-- Porting note: renamed so that dot-notation makes sense
theorem norm_fderiv_le_of_lipschitzOn {f : E → F} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C := by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)
#align fderiv_at.le_of_lip norm_fderiv_le_of_lipschitzOn

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem norm_fderiv_le_of_lipschitz {f : E → F} {x₀ : E}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
  norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOn_univ.2 hlip)

variable {𝕜}

protected theorem HasFDerivWithinAt.fderivWithin (h : HasFDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = f' :=
  (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm
#align has_fderiv_within_at.fderiv_within HasFDerivWithinAt.fderivWithin

theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
    DifferentiableWithinAt 𝕜 f s x := by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩
#align differentiable_within_at.mono DifferentiableWithinAt.mono

theorem DifferentiableWithinAt.mono_of_mem (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
    (hst : s ∈ 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x :=
  (h.hasFDerivWithinAt.mono_of_mem hst).differentiableWithinAt
#align differentiable_within_at.mono_of_mem DifferentiableWithinAt.mono_of_mem

theorem differentiableWithinAt_univ :
    DifferentiableWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]
#align differentiable_within_at_univ differentiableWithinAt_univ

theorem differentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]
#align differentiable_within_at_inter differentiableWithinAt_inter

theorem differentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]
#align differentiable_within_at_inter' differentiableWithinAt_inter'

theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)
#align differentiable_at.differentiable_within_at DifferentiableAt.differentiableWithinAt

@[fun_prop]
theorem Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x
#align differentiable.differentiable_at Differentiable.differentiableAt

protected theorem DifferentiableAt.fderivWithin (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs
#align differentiable_at.fderiv_within DifferentiableAt.fderivWithin

theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st
#align differentiable_on.mono DifferentiableOn.mono

theorem differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f := by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]
#align differentiable_on_univ differentiableOn_univ

@[fun_prop]
theorem Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)
#align differentiable.differentiable_on Differentiable.differentiableOn

theorem differentiableOn_of_locally_differentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ DifferentiableOn 𝕜 f (s ∩ u)) :
    DifferentiableOn 𝕜 f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
#align differentiable_on_of_locally_differentiable_on differentiableOn_of_locally_differentiableOn

theorem fderivWithin_of_mem (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem st).fderivWithin ht
#align fderiv_within_of_mem fderivWithin_of_mem

theorem fderivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h
#align fderiv_within_subset fderivWithin_subset

theorem fderivWithin_inter (ht : t ∈ 𝓝 x) : fderivWithin 𝕜 f (s ∩ t) x = fderivWithin 𝕜 f s x := by
  have A : 𝓝[(s ∩ t) \ {x}] x = 𝓝[s \ {x}] x := by
    have : (s ∩ t) \ {x} = (s \ {x}) ∩ t := by rw [inter_comm, inter_diff_assoc, inter_comm]
    rw [this, ← nhdsWithin_restrict' _ ht]
  simp [fderivWithin, A, hasFDerivWithinAt_inter ht]
#align fderiv_within_inter fderivWithin_inter

@[simp]
theorem fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f := by
  ext1 x
  nontriviality E
  have H : 𝓝[univ \ {x}] x ≠ ⊥ := by
    rw [← compl_eq_univ_diff, ← neBot_iff]
    exact Module.punctured_nhds_neBot 𝕜 E x
  simp [fderivWithin, fderiv, H]
#align fderiv_within_univ fderivWithin_univ

theorem fderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ, ← univ_inter s, fderivWithin_inter h]
#align fderiv_within_of_mem_nhds fderivWithin_of_mem_nhds

theorem fderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderivWithin_of_mem_nhds (hs.mem_nhds hx)
#align fderiv_within_of_open fderivWithin_of_isOpen

theorem fderivWithin_eq_fderiv (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt
#align fderiv_within_eq_fderiv fderivWithin_eq_fderiv

theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} : fderiv 𝕜 f x ∈ s ↔
    DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]
#align fderiv_mem_iff fderiv_mem_iff

theorem fderivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
    fderivWithin 𝕜 f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜 f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]
#align fderiv_within_mem_iff fderivWithin_mem_iff

theorem Asymptotics.IsBigO.hasFDerivWithinAt {s : Set E} {x₀ : E} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x₀ := by
  simp_rw [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleO,
    h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero,
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]
set_option linter.uppercaseLean3 false in
#align asymptotics.is_O.has_fderiv_within_at Asymptotics.IsBigO.hasFDerivWithinAt

theorem Asymptotics.IsBigO.hasFDerivAt {x₀ : E} {n : ℕ} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasFDerivAt f (0 : E →L[𝕜] F) x₀ := by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ
set_option linter.uppercaseLean3 false in
#align asymptotics.is_O.has_fderiv_at Asymptotics.IsBigO.hasFDerivAt

nonrec theorem HasFDerivWithinAt.isBigO_sub {f : E → F} {s : Set E} {x₀ : E} {f' : E →L[𝕜] F}
    (h : HasFDerivWithinAt f f' s x₀) : (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.isBigO_sub
set_option linter.uppercaseLean3 false in
#align has_fderiv_within_at.is_O HasFDerivWithinAt.isBigO_sub

lemma DifferentiableWithinAt.isBigO_sub {f : E → F} {s : Set E} {x₀ : E}
    (h : DifferentiableWithinAt 𝕜 f s x₀) : (f · - f x₀) =O[𝓝[s] x₀] (· - x₀) :=
  h.hasFDerivWithinAt.isBigO_sub

nonrec theorem HasFDerivAt.isBigO_sub {f : E → F} {x₀ : E} {f' : E →L[𝕜] F}
    (h : HasFDerivAt f f' x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.isBigO_sub
set_option linter.uppercaseLean3 false in
#align has_fderiv_at.is_O HasFDerivAt.isBigO_sub

nonrec theorem DifferentiableAt.isBigO_sub {f : E → F} {x₀ : E} (h : DifferentiableAt 𝕜 f x₀) :
    (f · - f x₀) =O[𝓝 x₀] (· - x₀) :=
  h.hasFDerivAt.isBigO_sub

end FDerivProperties

section Continuous

/-! ### Deducing continuity from differentiability -/


theorem HasFDerivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasFDerivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) := by
  have : Tendsto (fun x' => f x' - f x) L (𝓝 0) := by
    refine h.isBigO_sub.trans_tendsto (Tendsto.mono_left ?_ hL)
    rw [← sub_self x]
    exact tendsto_id.sub tendsto_const_nhds
  have := this.add (tendsto_const_nhds (x := f x))
  rw [zero_add (f x)] at this
  exact this.congr (by simp only [sub_add_cancel, eq_self_iff_true, forall_const])
#align has_fderiv_at_filter.tendsto_nhds HasFDerivAtFilter.tendsto_nhds

theorem HasFDerivWithinAt.continuousWithinAt (h : HasFDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasFDerivAtFilter.tendsto_nhds inf_le_left h
#align has_fderiv_within_at.continuous_within_at HasFDerivWithinAt.continuousWithinAt

theorem HasFDerivAt.continuousAt (h : HasFDerivAt f f' x) : ContinuousAt f x :=
  HasFDerivAtFilter.tendsto_nhds le_rfl h
#align has_fderiv_at.continuous_at HasFDerivAt.continuousAt

@[fun_prop]
theorem DifferentiableWithinAt.continuousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt
#align differentiable_within_at.continuous_within_at DifferentiableWithinAt.continuousWithinAt

@[fun_prop]
theorem DifferentiableAt.continuousAt (h : DifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousAt
#align differentiable_at.continuous_at DifferentiableAt.continuousAt

@[fun_prop]
theorem DifferentiableOn.continuousOn (h : DifferentiableOn 𝕜 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt
#align differentiable_on.continuous_on DifferentiableOn.continuousOn

@[fun_prop]
theorem Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt
#align differentiable.continuous Differentiable.continuous

protected theorem HasStrictFDerivAt.continuousAt (hf : HasStrictFDerivAt f f' x) :
    ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt
#align has_strict_fderiv_at.continuous_at HasStrictFDerivAt.continuousAt

theorem HasStrictFDerivAt.isBigO_sub_rev {f' : E ≃L[𝕜] F}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) x) :
    (fun p : E × E => p.1 - p.2) =O[𝓝 (x, x)] fun p : E × E => f p.1 - f p.2 :=
  ((f'.isBigO_comp_rev _ _).trans (hf.trans_isBigO (f'.isBigO_comp_rev _ _)).right_isBigO_add).congr
    (fun _ => rfl) fun _ => sub_add_cancel _ _
set_option linter.uppercaseLean3 false in
#align has_strict_fderiv_at.is_O_sub_rev HasStrictFDerivAt.isBigO_sub_rev

theorem HasFDerivAtFilter.isBigO_sub_rev (hf : HasFDerivAtFilter f f' x L) {C}
    (hf' : AntilipschitzWith C f') : (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  have : (fun x' => x' - x) =O[L] fun x' => f' (x' - x) :=
    isBigO_iff.2 ⟨C, eventually_of_forall fun _ => ZeroHomClass.bound_of_antilipschitz f' hf' _⟩
  (this.trans (hf.isLittleO.trans_isBigO this).right_isBigO_add).congr (fun _ => rfl) fun _ =>
    sub_add_cancel _ _
set_option linter.uppercaseLean3 false in
#align has_fderiv_at_filter.is_O_sub_rev HasFDerivAtFilter.isBigO_sub_rev

end Continuous

section congr

/-! ### congr properties of the derivative -/
theorem hasFDerivWithinAt_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {y}) x :=
      (hasFDerivWithinAt_diff_singleton _).symm
    _ ↔ HasFDerivWithinAt f f' (t \ {y}) x := by
      suffices 𝓝[s \ {y}] x = 𝓝[t \ {y}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', diff_eq,
        inter_comm] using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_diff_singleton _
#align has_fderiv_within_at_congr_set' hasFDerivWithinAt_congr_set'

theorem hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' x <| h.filter_mono inf_le_left
#align has_fderiv_within_at_congr_set hasFDerivWithinAt_congr_set

theorem differentiableWithinAt_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h
#align differentiable_within_at_congr_set' differentiableWithinAt_congr_set'

theorem differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set h
#align differentiable_within_at_congr_set differentiableWithinAt_congr_set

theorem fderivWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  have : s =ᶠ[𝓝[{x}ᶜ] x] t := nhdsWithin_compl_singleton_le x y h
  have : 𝓝[s \ {x}] x = 𝓝[t \ {x}] x := by
    simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', diff_eq,
      inter_comm] using this
  simp only [fderivWithin, hasFDerivWithinAt_congr_set' y h, this]
#align fderiv_within_congr_set' fderivWithin_congr_set'

theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_congr_set' x <| h.filter_mono inf_le_left
#align fderiv_within_congr_set fderivWithin_congr_set

theorem fderivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y
#align fderiv_within_eventually_congr_set' fderivWithin_eventually_congr_set'

theorem fderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  fderivWithin_eventually_congr_set' x <| h.filter_mono inf_le_left
#align fderiv_within_eventually_congr_set fderivWithin_eventually_congr_set

theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x := by
  refine isLittleO_congr ((h.prod_mk_nhds h).mono ?_) .rfl
  rintro p ⟨hp₁, hp₂⟩
  simp only [*]
#align filter.eventually_eq.has_strict_fderiv_at_iff Filter.EventuallyEq.hasStrictFDerivAt_iff

theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h

theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=
  h' ▸ h

theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
    (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt f₁ f' x :=
  (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h
#align has_strict_fderiv_at.congr_of_eventually_eq HasStrictFDerivAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasFDerivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : ∀ x, f₀' x = f₁' x) : HasFDerivAtFilter f₀ f₀' x L ↔ HasFDerivAtFilter f₁ f₁' x L := by
  simp only [hasFDerivAtFilter_iff_isLittleO]
  exact isLittleO_congr (h₀.mono fun y hy => by simp only [hy, h₁, hx]) .rfl
#align filter.eventually_eq.has_fderiv_at_filter_iff Filter.EventuallyEq.hasFDerivAtFilter_iff

theorem HasFDerivAtFilter.congr_of_eventuallyEq (h : HasFDerivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasFDerivAtFilter f₁ f' x L :=
  (hL.hasFDerivAtFilter_iff hx fun _ => rfl).2 h
#align has_fderiv_at_filter.congr_of_eventually_eq HasFDerivAtFilter.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x :=
  h.hasFDerivAtFilter_iff h.eq_of_nhds fun _ => _root_.rfl
#align filter.eventually_eq.has_fderiv_at_iff Filter.EventuallyEq.hasFDerivAt_iff

theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x :=
  exists_congr fun _ => h.hasFDerivAt_iff
#align filter.eventually_eq.differentiable_at_iff Filter.EventuallyEq.differentiableAt_iff

theorem Filter.EventuallyEq.hasFDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.hasFDerivAtFilter_iff hx fun _ => _root_.rfl
#align filter.eventually_eq.has_fderiv_within_at_iff Filter.EventuallyEq.hasFDerivWithinAt_iff

theorem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)
#align filter.eventually_eq.has_fderiv_within_at_iff_of_mem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem

theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun _ => h.hasFDerivWithinAt_iff hx
#align filter.eventually_eq.differentiable_within_at_iff Filter.EventuallyEq.differentiableWithinAt_iff

theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)
#align filter.eventually_eq.differentiable_within_at_iff_of_mem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem

theorem HasFDerivWithinAt.congr_mono (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasFDerivWithinAt f₁ f' t x :=
  HasFDerivAtFilter.congr_of_eventuallyEq (h.mono h₁) (Filter.mem_inf_of_right ht) hx
#align has_fderiv_within_at.congr_mono HasFDerivWithinAt.congr_mono

theorem HasFDerivWithinAt.congr (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_fderiv_within_at.congr HasFDerivWithinAt.congr

theorem HasFDerivWithinAt.congr' (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasFDerivWithinAt f₁ f' s x :=
  h.congr hs (hs hx)
#align has_fderiv_within_at.congr' HasFDerivWithinAt.congr'

theorem HasFDerivWithinAt.congr_of_eventuallyEq (h : HasFDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  HasFDerivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_fderiv_within_at.congr_of_eventually_eq HasFDerivWithinAt.congr_of_eventuallyEq

theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasFDerivAt f₁ f' x :=
  HasFDerivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_fderiv_at.congr_of_eventually_eq HasFDerivAt.congr_of_eventuallyEq

theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt
#align differentiable_within_at.congr_mono DifferentiableWithinAt.congr_mono

theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)
#align differentiable_within_at.congr DifferentiableWithinAt.congr

theorem DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt
#align differentiable_within_at.congr_of_eventually_eq DifferentiableWithinAt.congr_of_eventuallyEq

theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : DifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align differentiable_on.congr_mono DifferentiableOn.congr_mono

theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)
#align differentiable_on.congr DifferentiableOn.congr

theorem differentiableOn_congr (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩
#align differentiable_on_congr differentiableOn_congr

theorem DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    DifferentiableAt 𝕜 f₁ x :=
  hL.differentiableAt_iff.2 h
#align differentiable_at.congr_of_eventually_eq DifferentiableAt.congr_of_eventuallyEq

theorem DifferentiableWithinAt.fderivWithin_congr_mono (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt
#align differentiable_within_at.fderiv_within_congr_mono DifferentiableWithinAt.fderivWithin_congr_mono

theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  simp only [fderivWithin, hs.hasFDerivWithinAt_iff hx]
#align filter.eventually_eq.fderiv_within_eq Filter.EventuallyEq.fderivWithin_eq

theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
    fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 f t :=
  (eventually_nhdsWithin_nhdsWithin.2 hs).mp <|
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)
#align filter.eventually_eq.fderiv_within' Filter.EventuallyEq.fderivWithin'

protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] fderivWithin 𝕜 f s :=
  hs.fderivWithin' Subset.rfl
#align filter.eventually_eq.fderiv_within Filter.EventuallyEq.fderivWithin

theorem Filter.EventuallyEq.fderivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds
#align filter.eventually_eq.fderiv_within_eq_nhds Filter.EventuallyEq.fderivWithin_eq_nhds

theorem fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx
#align fderiv_within_congr fderivWithin_congr

theorem fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  fderivWithin_congr hs (hs hx)
#align fderiv_within_congr' fderivWithin_congr'

theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ, ← fderivWithin_univ, h.fderivWithin_eq_nhds]
#align filter.eventually_eq.fderiv_eq Filter.EventuallyEq.fderiv_eq

protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq
#align filter.eventually_eq.fderiv Filter.EventuallyEq.fderiv

end congr

section id

/-! ### Derivative of the identity -/

@[fun_prop]
theorem hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (id 𝕜 E) x :=
  (isLittleO_zero _ _).congr_left <| by simp
#align has_strict_fderiv_at_id hasStrictFDerivAt_id

theorem hasFDerivAtFilter_id (x : E) (L : Filter E) : HasFDerivAtFilter id (id 𝕜 E) x L :=
  .of_isLittleO <| (isLittleO_zero _ _).congr_left <| by simp
#align has_fderiv_at_filter_id hasFDerivAtFilter_id

@[fun_prop]
theorem hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDerivWithinAt id (id 𝕜 E) s x :=
  hasFDerivAtFilter_id _ _
#align has_fderiv_within_at_id hasFDerivWithinAt_id

@[fun_prop]
theorem hasFDerivAt_id (x : E) : HasFDerivAt id (id 𝕜 E) x :=
  hasFDerivAtFilter_id _ _
#align has_fderiv_at_id hasFDerivAt_id

@[simp, fun_prop]
theorem differentiableAt_id : DifferentiableAt 𝕜 id x :=
  (hasFDerivAt_id x).differentiableAt
#align differentiable_at_id differentiableAt_id

@[simp]
theorem differentiableAt_id' : DifferentiableAt 𝕜 (fun x => x) x :=
  (hasFDerivAt_id x).differentiableAt
#align differentiable_at_id' differentiableAt_id'

@[fun_prop]
theorem differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.differentiableWithinAt
#align differentiable_within_at_id differentiableWithinAt_id

@[simp, fun_prop]
theorem differentiable_id : Differentiable 𝕜 (id : E → E) := fun _ => differentiableAt_id
#align differentiable_id differentiable_id

@[simp]
theorem differentiable_id' : Differentiable 𝕜 fun x : E => x := fun _ => differentiableAt_id
#align differentiable_id' differentiable_id'

@[fun_prop]
theorem differentiableOn_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.differentiableOn
#align differentiable_on_id differentiableOn_id

@[simp]
theorem fderiv_id : fderiv 𝕜 id x = id 𝕜 E :=
  HasFDerivAt.fderiv (hasFDerivAt_id x)
#align fderiv_id fderiv_id

@[simp]
theorem fderiv_id' : fderiv 𝕜 (fun x : E => x) x = ContinuousLinearMap.id 𝕜 E :=
  fderiv_id
#align fderiv_id' fderiv_id'

theorem fderivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = id 𝕜 E := by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id
#align fderiv_within_id fderivWithin_id

theorem fderivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => x) s x = ContinuousLinearMap.id 𝕜 E :=
  fderivWithin_id hxs
#align fderiv_within_id' fderivWithin_id'

end id

section Const

/-! ### Derivative of a constant function -/

@[fun_prop]
theorem hasStrictFDerivAt_const (c : F) (x : E) :
    HasStrictFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  (isLittleO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_strict_fderiv_at_const hasStrictFDerivAt_const

theorem hasFDerivAtFilter_const (c : F) (x : E) (L : Filter E) :
    HasFDerivAtFilter (fun _ => c) (0 : E →L[𝕜] F) x L :=
  .of_isLittleO <| (isLittleO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_fderiv_at_filter_const hasFDerivAtFilter_const

@[fun_prop]
theorem hasFDerivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFDerivWithinAt (fun _ => c) (0 : E →L[𝕜] F) s x :=
  hasFDerivAtFilter_const _ _ _
#align has_fderiv_within_at_const hasFDerivWithinAt_const

@[fun_prop]
theorem hasFDerivAt_const (c : F) (x : E) : HasFDerivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  hasFDerivAtFilter_const _ _ _
#align has_fderiv_at_const hasFDerivAt_const

@[simp, fun_prop]
theorem differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun _ => c) x :=
  ⟨0, hasFDerivAt_const c x⟩
#align differentiable_at_const differentiableAt_const

@[fun_prop]
theorem differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun _ => c) s x :=
  DifferentiableAt.differentiableWithinAt (differentiableAt_const _)
#align differentiable_within_at_const differentiableWithinAt_const

theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun _ => c) x = 0 :=
  HasFDerivAt.fderiv (hasFDerivAt_const c x)
#align fderiv_const_apply fderiv_const_apply

@[simp]
theorem fderiv_const (c : F) : (fderiv 𝕜 fun _ : E => c) = 0 := by
  ext m
  rw [fderiv_const_apply]
  rfl
#align fderiv_const fderiv_const

theorem fderivWithin_const_apply (c : F) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun _ => c) s x = 0 := by
  rw [DifferentiableAt.fderivWithin (differentiableAt_const _) hxs]
  exact fderiv_const_apply _
#align fderiv_within_const_apply fderivWithin_const_apply

@[simp, fun_prop]
theorem differentiable_const (c : F) : Differentiable 𝕜 fun _ : E => c := fun _ =>
  differentiableAt_const _
#align differentiable_const differentiable_const

@[fun_prop]
theorem differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun _ => c) s :=
  (differentiable_const _).differentiableOn
#align differentiable_on_const differentiableOn_const

@[fun_prop]
theorem hasFDerivWithinAt_singleton (f : E → F) (x : E) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) {x} x := by
  simp only [HasFDerivWithinAt, nhdsWithin_singleton, hasFDerivAtFilter_iff_isLittleO,
    isLittleO_pure, ContinuousLinearMap.zero_apply, sub_self]
#align has_fderiv_within_at_singleton hasFDerivWithinAt_singleton

@[fun_prop]
theorem hasFDerivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [← hasFDerivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFDerivWithinAt_singleton f x
#align has_fderiv_at_of_subsingleton hasFDerivAt_of_subsingleton

@[fun_prop]
theorem differentiableOn_empty : DifferentiableOn 𝕜 f ∅ := fun _ => False.elim
#align differentiable_on_empty differentiableOn_empty

@[fun_prop]
theorem differentiableOn_singleton : DifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasFDerivWithinAt_singleton f x).differentiableWithinAt
#align differentiable_on_singleton differentiableOn_singleton

@[fun_prop]
theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn 𝕜 f s :=
  hs.induction_on differentiableOn_empty fun _ => differentiableOn_singleton
#align set.subsingleton.differentiable_on Set.Subsingleton.differentiableOn

theorem hasFDerivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun _ => c) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (hasFDerivAt_const _ _).congr_of_eventuallyEq hf
#align has_fderiv_at_zero_of_eventually_const hasFDerivAt_zero_of_eventually_const

end Const

end

/-! ### Support of derivatives -/

section Support

open Function

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {x : E}

theorem HasStrictFDerivAt.of_nmem_tsupport (h : x ∉ tsupport f) :
    HasStrictFDerivAt f (0 : E →L[𝕜] F) x := by
  rw [not_mem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictFDerivAt_const (0 : F) x).congr_of_eventuallyEq h.symm

theorem HasFDerivAt.of_nmem_tsupport (h : x ∉ tsupport f) :
    HasFDerivAt f (0 : E →L[𝕜] F) x :=
  (HasStrictFDerivAt.of_nmem_tsupport 𝕜 h).hasFDerivAt

theorem HasFDerivWithinAt.of_not_mem_tsupport {s : Set E} {x : E} (h : x ∉ tsupport f) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x :=
  (HasFDerivAt.of_nmem_tsupport 𝕜 h).hasFDerivWithinAt

theorem fderiv_of_not_mem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0 :=
  (HasFDerivAt.of_nmem_tsupport 𝕜 h).fderiv

theorem support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f := fun x ↦ by
  rw [← not_imp_not, nmem_support]
  exact fderiv_of_not_mem_tsupport _
#align support_fderiv_subset support_fderiv_subset

theorem tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) ⊆ tsupport f :=
  closure_minimal (support_fderiv_subset 𝕜) isClosed_closure
#align tsupport_fderiv_subset tsupport_fderiv_subset

protected theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) :
    HasCompactSupport (fderiv 𝕜 f) :=
  hf.mono' <| support_fderiv_subset 𝕜
#align has_compact_support.fderiv HasCompactSupport.fderiv

end Support
