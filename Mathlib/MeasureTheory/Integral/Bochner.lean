/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.SetToL1

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined through the extension process described in the file `SetToL1`,
which follows these steps:

1. Define the integral of the indicator of a set. This is `weightedSMul μ s x = (μ s).toReal * x`.
  `weightedSMul μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `SetToL1`) with respect to the set `s`.

2. Define the integral on simple functions of the type `SimpleFunc α E` (notation : `α →ₛ E`)
  where `E` is a real normed space. (See `SimpleFunc.integral` for details.)

3. Transfer this definition to define the integral on `L1.simpleFunc α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simpleFunc.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `ContinuousLinearMap.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

5. Define the Bochner integral on functions as the Bochner integral of its equivalence class in L1
  space, if it is in L1, and 0 otherwise.

The result of that construction is `∫ a, f a ∂μ`, which is definitionally equal to
`setToFun (dominatedFinMeasAdditive_weightedSMul μ) f`. Some basic properties of the integral
(like linearity) are particular cases of the properties of `setToFun` (which are described in the
file `SetToL1`).

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ`

2. Basic properties of the Bochner integral on functions of type `α → ℝ`, where `α` is a measure
  space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ℝ≥0∞`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` :
    `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. (In the file `DominatedConvergence`)
  `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

5. (In the file `SetIntegral`) integration commutes with continuous linear maps.

  * `ContinuousLinearMap.integral_comp_comm`
  * `LinearIsometry.integral_comp_comm`


## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `Integrable.induction` in the file `SimpleFuncDenseLp` (or one
of the related results, like `Lp.induction` for functions in `Lp`), which allows you to prove
something for an arbitrary integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_pos_part_sub_lintegral_neg_part` for a complicated example, which proves
that `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and second and third integral sign being the integral on `ℝ≥0∞`-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_pos_part_sub_lintegral_neg_part`
is scattered in sections with the name `posPart`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ENNReal.toReal (∫⁻ a, ENNReal.ofReal <| ‖f a‖)`, that is the norm of
   `f` in `L¹` space. Rewrite using `L1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `isClosed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `SimpleFunc` counterpart, using lemmas
   like `L1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `isClosed_property` or `DenseRange.induction_on` for this argument.

## Notations

* `α →ₛ E` : simple functions (defined in `MeasureTheory/Integration`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `MeasureTheory/LpSpace`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions (defined in `MeasureTheory/SimpleFuncDense`)
* `∫ a, f a ∂μ` : integral of `f` with respect to a measure `μ`
* `∫ a, f a` : integral of `f` with respect to `volume`, the default measure on the ambient type

We also define notations for integral on a set, which are described in the file
`MeasureTheory/SetIntegral`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/


assert_not_exists Differentiable

noncomputable section

open scoped Topology NNReal ENNReal MeasureTheory

open Set Filter TopologicalSpace ENNReal EMetric

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

section WeightedSMul

open ContinuousLinearMap

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

/-- Given a set `s`, return the continuous linear map `fun x => (μ s).toReal • x`. The extension
of that set function through `setToL1` gives the Bochner integral of L1 functions. -/
def weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F →L[ℝ] F :=
  (μ s).toReal • ContinuousLinearMap.id ℝ F

theorem weightedSMul_apply {m : MeasurableSpace α} (μ : Measure α) (s : Set α) (x : F) :
    weightedSMul μ s x = (μ s).toReal • x := by simp [weightedSMul]

@[simp]
theorem weightedSMul_zero_measure {m : MeasurableSpace α} :
    weightedSMul (0 : Measure α) = (0 : Set α → F →L[ℝ] F) := by ext1; simp [weightedSMul]

@[simp]
theorem weightedSMul_empty {m : MeasurableSpace α} (μ : Measure α) :
    weightedSMul μ ∅ = (0 : F →L[ℝ] F) := by ext1 x; rw [weightedSMul_apply]; simp

theorem weightedSMul_add_measure {m : MeasurableSpace α} (μ ν : Measure α) {s : Set α}
    (hμs : μ s ≠ ∞) (hνs : ν s ≠ ∞) :
    (weightedSMul (μ + ν) s : F →L[ℝ] F) = weightedSMul μ s + weightedSMul ν s := by
  ext1 x
  push_cast
  simp_rw [Pi.add_apply, weightedSMul_apply]
  push_cast
  rw [Pi.add_apply, ENNReal.toReal_add hμs hνs, add_smul]

theorem weightedSMul_smul_measure {m : MeasurableSpace α} (μ : Measure α) (c : ℝ≥0∞) {s : Set α} :
    (weightedSMul (c • μ) s : F →L[ℝ] F) = c.toReal • weightedSMul μ s := by
  ext1 x
  push_cast
  simp_rw [Pi.smul_apply, weightedSMul_apply]
  push_cast
  simp_rw [Pi.smul_apply, smul_eq_mul, toReal_mul, smul_smul]

theorem weightedSMul_congr (s t : Set α) (hst : μ s = μ t) :
    (weightedSMul μ s : F →L[ℝ] F) = weightedSMul μ t := by
  ext1 x; simp_rw [weightedSMul_apply]; congr 2

theorem weightedSMul_null {s : Set α} (h_zero : μ s = 0) : (weightedSMul μ s : F →L[ℝ] F) = 0 := by
  ext1 x; rw [weightedSMul_apply, h_zero]; simp

theorem weightedSMul_union' (s t : Set α) (ht : MeasurableSet t) (hs_finite : μ s ≠ ∞)
    (ht_finite : μ t ≠ ∞) (h_inter : s ∩ t = ∅) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t := by
  ext1 x
  simp_rw [add_apply, weightedSMul_apply,
    measure_union (Set.disjoint_iff_inter_eq_empty.mpr h_inter) ht,
    ENNReal.toReal_add hs_finite ht_finite, add_smul]

@[nolint unusedArguments]
theorem weightedSMul_union (s t : Set α) (_hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs_finite : μ s ≠ ∞) (ht_finite : μ t ≠ ∞) (h_inter : s ∩ t = ∅) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t :=
  weightedSMul_union' s t ht hs_finite ht_finite h_inter

theorem weightedSMul_smul [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜)
    (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weightedSMul μ s x := by
  simp_rw [weightedSMul_apply, smul_comm]

theorem norm_weightedSMul_le (s : Set α) : ‖(weightedSMul μ s : F →L[ℝ] F)‖ ≤ (μ s).toReal :=
  calc
    ‖(weightedSMul μ s : F →L[ℝ] F)‖ = ‖(μ s).toReal‖ * ‖ContinuousLinearMap.id ℝ F‖ :=
      norm_smul (μ s).toReal (ContinuousLinearMap.id ℝ F)
    _ ≤ ‖(μ s).toReal‖ :=
      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
    _ = abs (μ s).toReal := Real.norm_eq_abs _
    _ = (μ s).toReal := abs_eq_self.mpr ENNReal.toReal_nonneg

theorem dominatedFinMeasAdditive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) :
    DominatedFinMeasAdditive μ (weightedSMul μ : Set α → F →L[ℝ] F) 1 :=
  ⟨weightedSMul_union, fun s _ _ => (norm_weightedSMul_le s).trans (one_mul _).symm.le⟩

theorem weightedSMul_nonneg (s : Set α) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ weightedSMul μ s x := by
  simp only [weightedSMul, Algebra.id.smul_eq_mul, coe_smul', _root_.id, coe_id', Pi.smul_apply]
  exact mul_nonneg toReal_nonneg hx

end WeightedSMul

@[inherit_doc] local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section PosPart

variable [LinearOrder E] [Zero E] [MeasurableSpace α]

/-- Positive part of a simple function. -/
def posPart (f : α →ₛ E) : α →ₛ E :=
  f.map fun b => max b 0

/-- Negative part of a simple function. -/
def negPart [Neg E] (f : α →ₛ E) : α →ₛ E :=
  posPart (-f)

theorem posPart_map_norm (f : α →ₛ ℝ) : (posPart f).map norm = posPart f := by
  ext; rw [map_apply, Real.norm_eq_abs, abs_of_nonneg]; exact le_max_right _ _

theorem negPart_map_norm (f : α →ₛ ℝ) : (negPart f).map norm = negPart f := by
  rw [negPart]; exact posPart_map_norm _

theorem posPart_sub_negPart (f : α →ₛ ℝ) : f.posPart - f.negPart = f := by
  simp only [posPart, negPart]
  ext a
  rw [coe_sub]
  exact max_zero_sub_eq_self (f a)

end PosPart

section Integral

/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic property of this integral.
-/


open Finset

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {G F' : Type*}
  [NormedAddCommGroup G] [NormedAddCommGroup F'] [NormedSpace ℝ F'] {m : MeasurableSpace α}
  {μ : Measure α}

/-- Bochner integral of simple functions whose codomain is a real `NormedSpace`.
This is equal to `∑ x ∈ f.range, (μ (f ⁻¹' {x})).toReal • x` (see `integral_eq`). -/
def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) : F :=
  f.setToSimpleFunc (weightedSMul μ)

theorem integral_def {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = f.setToSimpleFunc (weightedSMul μ) := rfl

theorem integral_eq {m : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = ∑ x ∈ f.range, (μ (f ⁻¹' {x})).toReal • x := by
  simp [integral, setToSimpleFunc, weightedSMul_apply]

theorem integral_eq_sum_filter [DecidablePred fun x : F => x ≠ 0] {m : MeasurableSpace α}
    (f : α →ₛ F) (μ : Measure α) :
    f.integral μ = ∑ x ∈ f.range.filter fun x => x ≠ 0, (μ (f ⁻¹' {x})).toReal • x := by
  simp_rw [integral_def, setToSimpleFunc_eq_sum_filter, weightedSMul_apply]

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
theorem integral_eq_sum_of_subset [DecidablePred fun x : F => x ≠ 0] {f : α →ₛ F} {s : Finset F}
    (hs : (f.range.filter fun x => x ≠ 0) ⊆ s) :
    f.integral μ = ∑ x ∈ s, (μ (f ⁻¹' {x})).toReal • x := by
  rw [SimpleFunc.integral_eq_sum_filter, Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  -- Porting note: reordered for clarity
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  -- Porting note: added
  simp only [Set.mem_range, not_exists] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx]

@[simp]
theorem integral_const {m : MeasurableSpace α} (μ : Measure α) (y : F) :
    (const α y).integral μ = (μ univ).toReal • y := by
  classical
  calc
    (const α y).integral μ = ∑ z ∈ {y}, (μ (const α y ⁻¹' {z})).toReal • z :=
      integral_eq_sum_of_subset <| (filter_subset _ _).trans (range_const_subset _ _)
    _ = (μ univ).toReal • y := by simp [Set.preimage] -- Porting note: added `Set.preimage`

@[simp]
theorem integral_piecewise_zero {m : MeasurableSpace α} (f : α →ₛ F) (μ : Measure α) {s : Set α}
    (hs : MeasurableSet s) : (piecewise s hs f 0).integral μ = f.integral (μ.restrict s) := by
  classical
  refine (integral_eq_sum_of_subset ?_).trans
      ((sum_congr rfl fun y hy => ?_).trans (integral_eq_sum_filter _ _).symm)
  · intro y hy
    simp only [mem_filter, mem_range, coe_piecewise, coe_zero, piecewise_eq_indicator,
      mem_range_indicator] at *
    rcases hy with ⟨⟨rfl, -⟩ | ⟨x, -, rfl⟩, h₀⟩
    exacts [(h₀ rfl).elim, ⟨Set.mem_range_self _, h₀⟩]
  · dsimp
    rw [Set.piecewise_eq_indicator, indicator_preimage_of_not_mem,
      Measure.restrict_apply (f.measurableSet_preimage _)]
    exact fun h₀ => (mem_filter.1 hy).2 (Eq.symm h₀)

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
theorem map_integral (f : α →ₛ E) (g : E → F) (hf : Integrable f μ) (hg : g 0 = 0) :
    (f.map g).integral μ = ∑ x ∈ f.range, ENNReal.toReal (μ (f ⁻¹' {x})) • g x :=
  map_setToSimpleFunc _ weightedSMul_union hf hg

/-- `SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has type
    `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion.
    See `integral_eq_lintegral` for a simpler version. -/
theorem integral_eq_lintegral' {f : α →ₛ E} {g : E → ℝ≥0∞} (hf : Integrable f μ) (hg0 : g 0 = 0)
    (ht : ∀ b, g b ≠ ∞) :
    (f.map (ENNReal.toReal ∘ g)).integral μ = ENNReal.toReal (∫⁻ a, g (f a) ∂μ) := by
  have hf' : f.FinMeasSupp μ := integrable_iff_finMeasSupp.1 hf
  simp only [← map_apply g f, lintegral_eq_lintegral]
  rw [map_integral f _ hf, map_lintegral, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    -- Porting note: added `Function.comp_apply`
    rw [smul_eq_mul, toReal_mul, mul_comm, Function.comp_apply]
  · rintro a -
    by_cases a0 : a = 0
    · rw [a0, hg0, zero_mul]; exact WithTop.zero_ne_top
    · apply mul_ne_top (ht a) (hf'.meas_preimage_singleton_ne_zero a0).ne
  · simp [hg0]

variable [NormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]

theorem integral_congr {f g : α →ₛ E} (hf : Integrable f μ) (h : f =ᵐ[μ] g) :
    f.integral μ = g.integral μ :=
  setToSimpleFunc_congr (weightedSMul μ) (fun _ _ => weightedSMul_null) weightedSMul_union hf h

/-- `SimpleFunc.bintegral` and `SimpleFunc.integral` agree when the integrand has type
    `α →ₛ ℝ≥0∞`. But since `ℝ≥0∞` is not a `NormedSpace`, we need some form of coercion. -/
theorem integral_eq_lintegral {f : α →ₛ ℝ} (hf : Integrable f μ) (h_pos : 0 ≤ᵐ[μ] f) :
    f.integral μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
  have : f =ᵐ[μ] f.map (ENNReal.toReal ∘ ENNReal.ofReal) :=
    h_pos.mono fun a h => (ENNReal.toReal_ofReal h).symm
  rw [← integral_eq_lintegral' hf]
  exacts [integral_congr hf this, ENNReal.ofReal_zero, fun b => ENNReal.ofReal_ne_top]

theorem integral_add {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
    integral μ (f + g) = integral μ f + integral μ g :=
  setToSimpleFunc_add _ weightedSMul_union hf hg

theorem integral_neg {f : α →ₛ E} (hf : Integrable f μ) : integral μ (-f) = -integral μ f :=
  setToSimpleFunc_neg _ weightedSMul_union hf

theorem integral_sub {f g : α →ₛ E} (hf : Integrable f μ) (hg : Integrable g μ) :
    integral μ (f - g) = integral μ f - integral μ g :=
  setToSimpleFunc_sub _ weightedSMul_union hf hg

theorem integral_smul (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    integral μ (c • f) = c • integral μ f :=
  setToSimpleFunc_smul _ weightedSMul_union weightedSMul_smul c hf

theorem norm_setToSimpleFunc_le_integral_norm (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * (μ s).toReal) {f : α →ₛ E}
    (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ ≤ C * (f.map norm).integral μ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, ENNReal.toReal (μ (f ⁻¹' {x})) * ‖x‖ :=
      norm_setToSimpleFunc_le_sum_mul_norm_of_integrable T hT_norm f hf
    _ = C * (f.map norm).integral μ := by
      rw [map_integral f norm hf norm_zero]; simp_rw [smul_eq_mul]

theorem norm_integral_le_integral_norm (f : α →ₛ E) (hf : Integrable f μ) :
    ‖f.integral μ‖ ≤ (f.map norm).integral μ := by
  refine (norm_setToSimpleFunc_le_integral_norm _ (fun s _ _ => ?_) hf).trans (one_mul _).le
  exact (norm_weightedSMul_le s).trans (one_mul _).symm.le

theorem integral_add_measure {ν} (f : α →ₛ E) (hf : Integrable f (μ + ν)) :
    f.integral (μ + ν) = f.integral μ + f.integral ν := by
  simp_rw [integral_def]
  refine setToSimpleFunc_add_left'
    (weightedSMul μ) (weightedSMul ν) (weightedSMul (μ + ν)) (fun s _ hμνs => ?_) hf
  rw [lt_top_iff_ne_top, Measure.coe_add, Pi.add_apply, ENNReal.add_ne_top] at hμνs
  rw [weightedSMul_add_measure _ _ hμνs.1 hμνs.2]

end Integral

end SimpleFunc

namespace L1

open AEEqFun Lp.simpleFunc Lp

variable [NormedAddCommGroup E] [NormedAddCommGroup F] {m : MeasurableSpace α} {μ : Measure α}

namespace SimpleFunc

theorem norm_eq_integral (f : α →₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ := by
  rw [norm_eq_sum_mul f, (toSimpleFunc f).map_integral norm (SimpleFunc.integrable f) norm_zero]
  simp_rw [smul_eq_mul]

section PosPart

/-- Positive part of a simple function in L1 space.  -/
nonrec def posPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  ⟨Lp.posPart (f : α →₁[μ] ℝ), by
    rcases f with ⟨f, s, hsf⟩
    use s.posPart
    simp only [Subtype.coe_mk, Lp.coe_posPart, ← hsf, AEEqFun.posPart_mk,
      SimpleFunc.coe_map, mk_eq_mk]
    -- Porting note: added
    simp [SimpleFunc.posPart, Function.comp, EventuallyEq.rfl] ⟩

/-- Negative part of a simple function in L1 space. -/
def negPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  posPart (-f)

@[norm_cast]
theorem coe_posPart (f : α →₁ₛ[μ] ℝ) : (posPart f : α →₁[μ] ℝ) = Lp.posPart (f : α →₁[μ] ℝ) := rfl

@[norm_cast]
theorem coe_negPart (f : α →₁ₛ[μ] ℝ) : (negPart f : α →₁[μ] ℝ) = Lp.negPart (f : α →₁[μ] ℝ) := rfl

end PosPart

section SimpleFuncIntegral

/-!
### The Bochner integral of `L1`

Define the Bochner integral on `α →₁ₛ[μ] E` by extension from the simple functions `α →₁ₛ[μ] E`,
and prove basic properties of this integral. -/


variable [NormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E] {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

attribute [local instance] simpleFunc.normedSpace

/-- The Bochner integral over simple functions in L1 space. -/
def integral (f : α →₁ₛ[μ] E) : E :=
  (toSimpleFunc f).integral μ

theorem integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = (toSimpleFunc f).integral μ := rfl

nonrec theorem integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] toSimpleFunc f) :
    integral f = ENNReal.toReal (∫⁻ a, ENNReal.ofReal ((toSimpleFunc f) a) ∂μ) := by
  rw [integral, SimpleFunc.integral_eq_lintegral (SimpleFunc.integrable f) h_pos]

theorem integral_eq_setToL1S (f : α →₁ₛ[μ] E) : integral f = setToL1S (weightedSMul μ) f := rfl

nonrec theorem integral_congr {f g : α →₁ₛ[μ] E} (h : toSimpleFunc f =ᵐ[μ] toSimpleFunc g) :
    integral f = integral g :=
  SimpleFunc.integral_congr (SimpleFunc.integrable f) h

theorem integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
  setToL1S_add _ (fun _ _ => weightedSMul_null) weightedSMul_union _ _

theorem integral_smul (c : 𝕜) (f : α →₁ₛ[μ] E) : integral (c • f) = c • integral f :=
  setToL1S_smul _ (fun _ _ => weightedSMul_null) weightedSMul_union weightedSMul_smul c f

theorem norm_integral_le_norm (f : α →₁ₛ[μ] E) : ‖integral f‖ ≤ ‖f‖ := by
  rw [integral, norm_eq_integral]
  exact (toSimpleFunc f).norm_integral_le_integral_norm (SimpleFunc.integrable f)

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedSpace 𝕜 E']
variable (α E μ 𝕜)

/-- The Bochner integral over simple functions in L1 space as a continuous linear map. -/
def integralCLM' : (α →₁ₛ[μ] E) →L[𝕜] E :=
  LinearMap.mkContinuous ⟨⟨integral, integral_add⟩, integral_smul⟩ 1 fun f =>
    le_trans (norm_integral_le_norm _) <| by rw [one_mul]

/-- The Bochner integral over simple functions in L1 space as a continuous linear map over ℝ. -/
def integralCLM : (α →₁ₛ[μ] E) →L[ℝ] E :=
  integralCLM' α E ℝ μ

variable {α E μ 𝕜}

local notation "Integral" => integralCLM α E μ

open ContinuousLinearMap

theorem norm_Integral_le_one : ‖Integral‖ ≤ 1 :=
  -- Porting note: Old proof was `LinearMap.mkContinuous_norm_le _ zero_le_one _`
  LinearMap.mkContinuous_norm_le _ zero_le_one (fun f => by
    rw [one_mul]
    exact norm_integral_le_norm f)

section PosPart

theorem posPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart := by
  have eq : ∀ a, (toSimpleFunc f).posPart a = max ((toSimpleFunc f) a) 0 := fun a => rfl
  have ae_eq : ∀ᵐ a ∂μ, toSimpleFunc (posPart f) a = max ((toSimpleFunc f) a) 0 := by
    filter_upwards [toSimpleFunc_eq_toFun (posPart f), Lp.coeFn_posPart (f : α →₁[μ] ℝ),
      toSimpleFunc_eq_toFun f] with _ _ h₂ h₃
    convert h₂ using 1
    -- Porting note: added
    rw [h₃]
  refine ae_eq.mono fun a h => ?_
  rw [h, eq]

theorem negPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (negPart f) =ᵐ[μ] (toSimpleFunc f).negPart := by
  rw [SimpleFunc.negPart, MeasureTheory.SimpleFunc.negPart]
  filter_upwards [posPart_toSimpleFunc (-f), neg_toSimpleFunc f]
  intro a h₁ h₂
  rw [h₁]
  show max _ _ = max _ _
  rw [h₂]
  rfl

theorem integral_eq_norm_posPart_sub (f : α →₁ₛ[μ] ℝ) : integral f = ‖posPart f‖ - ‖negPart f‖ := by
  -- Convert things in `L¹` to their `SimpleFunc` counterpart
  have ae_eq₁ : (toSimpleFunc f).posPart =ᵐ[μ] (toSimpleFunc (posPart f)).map norm := by
    filter_upwards [posPart_toSimpleFunc f] with _ h
    rw [SimpleFunc.map_apply, h]
    conv_lhs => rw [← SimpleFunc.posPart_map_norm, SimpleFunc.map_apply]
  -- Convert things in `L¹` to their `SimpleFunc` counterpart
  have ae_eq₂ : (toSimpleFunc f).negPart =ᵐ[μ] (toSimpleFunc (negPart f)).map norm := by
    filter_upwards [negPart_toSimpleFunc f] with _ h
    rw [SimpleFunc.map_apply, h]
    conv_lhs => rw [← SimpleFunc.negPart_map_norm, SimpleFunc.map_apply]
  rw [integral, norm_eq_integral, norm_eq_integral, ← SimpleFunc.integral_sub]
  · show (toSimpleFunc f).integral μ =
      ((toSimpleFunc (posPart f)).map norm - (toSimpleFunc (negPart f)).map norm).integral μ
    apply MeasureTheory.SimpleFunc.integral_congr (SimpleFunc.integrable f)
    filter_upwards [ae_eq₁, ae_eq₂] with _ h₁ h₂
    rw [SimpleFunc.sub_apply, ← h₁, ← h₂]
    exact DFunLike.congr_fun (toSimpleFunc f).posPart_sub_negPart.symm _
  · exact (SimpleFunc.integrable f).pos_part.congr ae_eq₁
  · exact (SimpleFunc.integrable f).neg_part.congr ae_eq₂

end PosPart

end SimpleFuncIntegral

end SimpleFunc

open SimpleFunc

local notation "Integral" => @integralCLM α E _ _ _ _ _ μ _

variable [NormedSpace ℝ E] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  [NormedSpace ℝ F] [CompleteSpace E]

section IntegrationInL1

attribute [local instance] simpleFunc.normedSpace

open ContinuousLinearMap

variable (𝕜)

/-- The Bochner integral in L1 space as a continuous linear map. -/
nonrec def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
  (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.uniformInducing

variable {𝕜}

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
  integralCLM' ℝ

-- Porting note: added `(E := E)` in several places below.
/-- The Bochner integral in L1 space -/
irreducible_def integral : (α →₁[μ] E) → E :=
  integralCLM (E := E)

theorem integral_eq (f : α →₁[μ] E) : integral f = integralCLM (E := E) f := by
  simp only [integral]

theorem integral_eq_setToL1 (f : α →₁[μ] E) :
    integral f = setToL1 (E := E) (dominatedFinMeasAdditive_weightedSMul μ) f := by
  simp only [integral]; rfl

@[norm_cast]
theorem SimpleFunc.integral_L1_eq_integral (f : α →₁ₛ[μ] E) :
    L1.integral (f : α →₁[μ] E) = SimpleFunc.integral f := by
  simp only [integral, L1.integral]
  exact setToL1_eq_setToL1SCLM (dominatedFinMeasAdditive_weightedSMul μ) f

variable (α E)

@[simp]
theorem integral_zero : integral (0 : α →₁[μ] E) = 0 := by
  simp only [integral]
  exact map_zero integralCLM

variable {α E}

@[integral_simps]
theorem integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g := by
  simp only [integral]
  exact map_add integralCLM f g

@[integral_simps]
theorem integral_neg (f : α →₁[μ] E) : integral (-f) = -integral f := by
  simp only [integral]
  exact map_neg integralCLM f

@[integral_simps]
theorem integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g := by
  simp only [integral]
  exact map_sub integralCLM f g

@[integral_simps]
theorem integral_smul (c : 𝕜) (f : α →₁[μ] E) : integral (c • f) = c • integral f := by
  simp only [integral]
  show (integralCLM' (E := E) 𝕜) (c • f) = c • (integralCLM' (E := E) 𝕜) f
  exact map_smul (integralCLM' (E := E) 𝕜) c f

local notation "Integral" => @integralCLM α E _ _ μ _ _

local notation "sIntegral" => @SimpleFunc.integralCLM α E _ _ μ _

theorem norm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖ ≤ 1 :=
  norm_setToL1_le (dominatedFinMeasAdditive_weightedSMul μ) zero_le_one

theorem nnnorm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ 1 :=
  norm_Integral_le_one

theorem norm_integral_le (f : α →₁[μ] E) : ‖integral f‖ ≤ ‖f‖ :=
  calc
    ‖integral f‖ = ‖integralCLM (E := E) f‖ := by simp only [integral]
    _ ≤ ‖integralCLM (α := α) (E := E) (μ := μ)‖ * ‖f‖ := le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right norm_Integral_le_one <| norm_nonneg _
    _ = ‖f‖ := one_mul _

theorem nnnorm_integral_le (f : α →₁[μ] E) : ‖integral f‖₊ ≤ ‖f‖₊ :=
  norm_integral_le f

@[continuity]
theorem continuous_integral : Continuous fun f : α →₁[μ] E => integral f := by
  simp only [integral]
  exact L1.integralCLM.continuous

section PosPart

theorem integral_eq_norm_posPart_sub (f : α →₁[μ] ℝ) :
    integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖ := by
  -- Use `isClosed_property` and `isClosed_eq`
  refine @isClosed_property _ _ _ ((↑) : (α →₁ₛ[μ] ℝ) → α →₁[μ] ℝ)
      (fun f : α →₁[μ] ℝ => integral f = ‖Lp.posPart f‖ - ‖Lp.negPart f‖)
      (simpleFunc.denseRange one_ne_top) (isClosed_eq ?_ ?_) ?_ f
  · simp only [integral]
    exact cont _
  · refine Continuous.sub (continuous_norm.comp Lp.continuous_posPart)
      (continuous_norm.comp Lp.continuous_negPart)
  -- Show that the property holds for all simple functions in the `L¹` space.
  · intro s
    norm_cast
    exact SimpleFunc.integral_eq_norm_posPart_sub _

end PosPart

end IntegrationInL1

end L1

/-!
## The Bochner integral on functions

Define the Bochner integral on functions generally to be the `L1` Bochner integral, for integrable
functions, and 0 otherwise; prove its basic properties.
-/

variable [NormedAddCommGroup E] [hE : CompleteSpace E] [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

open Classical in
/-- The Bochner integral -/
irreducible_def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α → G) : G :=
  if _ : CompleteSpace G then
    if hf : Integrable f μ then L1.integral (hf.toL1 f) else 0
  else 0

/-! In the notation for integrals, an expression like `∫ x, g ‖x‖ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => integral μ r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)", "r:60:(scoped f => integral volume f) => r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => integral (Measure.restrict μ s) r

@[inherit_doc MeasureTheory.integral]
notation3 "∫ "(...)" in "s", "r:60:(scoped f => integral (Measure.restrict volume s) f) => r

section Properties

open ContinuousLinearMap MeasureTheory.SimpleFunc

variable [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]
variable {f g : α → E} {m : MeasurableSpace α} {μ : Measure α}

theorem integral_eq (f : α → E) (hf : Integrable f μ) : ∫ a, f a ∂μ = L1.integral (hf.toL1 f) := by
  simp [integral, hE, hf]

theorem integral_eq_setToFun (f : α → E) :
    ∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul μ) f := by
  simp only [integral, hE, L1.integral]; rfl

theorem L1.integral_eq_integral (f : α →₁[μ] E) : L1.integral f = ∫ a, f a ∂μ := by
  simp only [integral, L1.integral, integral_eq_setToFun]
  exact (L1.setToFun_eq_setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f).symm

theorem integral_undef {f : α → G} (h : ¬Integrable f μ) : ∫ a, f a ∂μ = 0 := by
  by_cases hG : CompleteSpace G
  · simp [integral, hG, h]
  · simp [integral, hG]

theorem Integrable.of_integral_ne_zero {f : α → G} (h : ∫ a, f a ∂μ ≠ 0) : Integrable f μ :=
  Not.imp_symm integral_undef h

theorem integral_non_aestronglyMeasurable {f : α → G} (h : ¬AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = 0 :=
  integral_undef <| not_and_of_not_left _ h

variable (α G)

@[simp]
theorem integral_zero : ∫ _ : α, (0 : G) ∂μ = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_zero (dominatedFinMeasAdditive_weightedSMul μ)
  · simp [integral, hG]

@[simp]
theorem integral_zero' : integral μ (0 : α → G) = 0 :=
  integral_zero α G

variable {α G}

theorem integrable_of_integral_eq_one {f : α → ℝ} (h : ∫ x, f x ∂μ = 1) : Integrable f μ :=
  .of_integral_ne_zero <| h ▸ one_ne_zero

theorem integral_add {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_add (dominatedFinMeasAdditive_weightedSMul μ) hf hg
  · simp [integral, hG]

theorem integral_add' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg

theorem integral_finset_sum {ι} (s : Finset ι) {f : ι → α → G} (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫ a, f i a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_finset_sum (dominatedFinMeasAdditive_weightedSMul _) s hf
  · simp [integral, hG]

@[integral_simps]
theorem integral_neg (f : α → G) : ∫ a, -f a ∂μ = -∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_neg (dominatedFinMeasAdditive_weightedSMul μ) f
  · simp [integral, hG]

theorem integral_neg' (f : α → G) : ∫ a, (-f) a ∂μ = -∫ a, f a ∂μ :=
  integral_neg f

theorem integral_sub {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_sub (dominatedFinMeasAdditive_weightedSMul μ) hf hg
  · simp [integral, hG]

theorem integral_sub' {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
  integral_sub hf hg

@[integral_simps]
theorem integral_smul [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G] (c : 𝕜) (f : α → G) :
    ∫ a, c • f a ∂μ = c • ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_smul (dominatedFinMeasAdditive_weightedSMul μ) weightedSMul_smul c f
  · simp [integral, hG]

theorem integral_mul_left {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ :=
  integral_smul r f

theorem integral_mul_right {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r := by
  simp only [mul_comm]; exact integral_mul_left r f

theorem integral_div {L : Type*} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r := by
  simpa only [← div_eq_mul_inv] using integral_mul_right r⁻¹ f

theorem integral_congr_ae {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_congr_ae (dominatedFinMeasAdditive_weightedSMul μ) h
  · simp [integral, hG]

-- Porting note: `nolint simpNF` added because simplify fails on left-hand side
@[simp, nolint simpNF]
theorem L1.integral_of_fun_eq_integral {f : α → G} (hf : Integrable f μ) :
    ∫ a, (hf.toL1 f) a ∂μ = ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [MeasureTheory.integral, hG, L1.integral]
    exact setToFun_toL1 (dominatedFinMeasAdditive_weightedSMul μ) hf
  · simp [MeasureTheory.integral, hG]

@[continuity]
theorem continuous_integral : Continuous fun f : α →₁[μ] G => ∫ a, f a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuous_setToFun (dominatedFinMeasAdditive_weightedSMul μ)
  · simp [integral, hG, continuous_const]

theorem norm_integral_le_lintegral_norm (f : α → G) :
    ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) := by
  by_cases hG : CompleteSpace G
  · by_cases hf : Integrable f μ
    · rw [integral_eq f hf, ← Integrable.norm_toL1_eq_lintegral_norm f hf]
      exact L1.norm_integral_le _
    · rw [integral_undef hf, norm_zero]; exact toReal_nonneg
  · simp [integral, hG]

theorem ennnorm_integral_le_lintegral_ennnorm (f : α → G) :
    (‖∫ a, f a ∂μ‖₊ : ℝ≥0∞) ≤ ∫⁻ a, ‖f a‖₊ ∂μ := by
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  apply ENNReal.ofReal_le_of_le_toReal
  exact norm_integral_le_lintegral_norm f

theorem integral_eq_zero_of_ae {f : α → G} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 := by
  simp [integral_congr_ae hf, integral_zero]

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem HasFiniteIntegral.tendsto_setIntegral_nhds_zero {ι} {f : α → G}
    (hf : HasFiniteIntegral f μ) {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_setLIntegral_zero (ne_of_lt hf) hs) (fun i => zero_le _)
    fun i => ennnorm_integral_le_lintegral_ennnorm _

@[deprecated (since := "2024-04-17")]
alias HasFiniteIntegral.tendsto_set_integral_nhds_zero :=
  HasFiniteIntegral.tendsto_setIntegral_nhds_zero

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι} {f : α → G} (hf : Integrable f μ)
    {l : Filter ι} {s : ι → Set α} (hs : Tendsto (μ ∘ s) l (𝓝 0)) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) l (𝓝 0) :=
  hf.2.tendsto_setIntegral_nhds_zero hs

@[deprecated (since := "2024-04-17")]
alias Integrable.tendsto_set_integral_nhds_zero :=
  Integrable.tendsto_setIntegral_nhds_zero

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
theorem tendsto_integral_of_L1 {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖₊ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, F i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ) := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact tendsto_setToFun_of_L1 (dominatedFinMeasAdditive_weightedSMul μ) f hfi hFi hF
  · simp [integral, hG, tendsto_const_nhds]

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x ∂μ`. -/
lemma tendsto_integral_of_L1' {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
lemma tendsto_setIntegral_of_L1 {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G}
    {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖₊ ∂μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_nnnorm] at hF ⊢
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le')
      (fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)

@[deprecated (since := "2024-04-17")]
alias tendsto_set_integral_of_L1 := tendsto_setIntegral_of_L1

/-- If `F i → f` in `L1`, then `∫ x in s, F i x ∂μ → ∫ x in s, f x ∂μ`. -/
lemma tendsto_setIntegral_of_L1' {ι} (f : α → G) (hfi : Integrable f μ) {F : ι → α → G}
    {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ) (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ) l (𝓝 0))
    (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

@[deprecated (since := "2024-04-17")]
alias tendsto_set_integral_of_L1' := tendsto_setIntegral_of_L1'

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

theorem continuousWithinAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀) :
    ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousWithinAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousWithinAt_const]

theorem continuousAt_of_dominated {F : X → α → G} {x₀ : X} {bound : α → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) :
    ContinuousAt (fun x => ∫ a, F x a ∂μ) x₀ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousAt_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousAt_const]

theorem continuousOn_of_dominated {F : X → α → G} {bound : α → ℝ} {s : Set X}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_cont : ∀ᵐ a ∂μ, ContinuousOn (fun x => F x a) s) :
    ContinuousOn (fun x => ∫ a, F x a ∂μ) s := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuousOn_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuousOn_const]

theorem continuous_of_dominated {F : X → α → G} {bound : α → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ) (h_bound : ∀ x, ∀ᵐ a ∂μ, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ) (h_cont : ∀ᵐ a ∂μ, Continuous fun x => F x a) :
    Continuous fun x => ∫ a, F x a ∂μ := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact continuous_setToFun_of_dominated (dominatedFinMeasAdditive_weightedSMul μ)
      hF_meas h_bound bound_integrable h_cont
  · simp [integral, hG, continuous_const]

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`.  -/
theorem integral_eq_lintegral_pos_part_sub_lintegral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ =
      ENNReal.toReal (∫⁻ a, .ofReal (f a) ∂μ) - ENNReal.toReal (∫⁻ a, .ofReal (-f a) ∂μ) := by
  let f₁ := hf.toL1 f
  -- Go to the `L¹` space
  have eq₁ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ‖Lp.posPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_posPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    rw [Real.nnnorm_of_nonneg (le_max_right _ _)]
    rw [Real.coe_toNNReal', NNReal.coe_mk]
  -- Go to the `L¹` space
  have eq₂ : ENNReal.toReal (∫⁻ a, ENNReal.ofReal (-f a) ∂μ) = ‖Lp.negPart f₁‖ := by
    rw [L1.norm_def]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Lp.coeFn_negPart f₁, hf.coeFn_toL1] with _ h₁ h₂
    rw [h₁, h₂, ENNReal.ofReal]
    congr 1
    apply NNReal.eq
    simp only [Real.coe_toNNReal', coe_nnnorm, nnnorm_neg]
    rw [Real.norm_of_nonpos (min_le_right _ _), ← max_neg_neg, neg_zero]
  rw [eq₁, eq₂, integral, dif_pos, dif_pos]
  exact L1.integral_eq_norm_posPart_sub _

theorem integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f)
    (hfm : AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, ENNReal.ofReal (f a) ∂μ) := by
  by_cases hfi : Integrable f μ
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi]
    have h_min : ∫⁻ a, ENNReal.ofReal (-f a) ∂μ = 0 := by
      rw [lintegral_eq_zero_iff']
      · refine hf.mono ?_
        simp only [Pi.zero_apply]
        intro a h
        simp only [h, neg_nonpos, ofReal_eq_zero]
      · exact measurable_ofReal.comp_aemeasurable hfm.aemeasurable.neg
    rw [h_min, zero_toReal, _root_.sub_zero]
  · rw [integral_undef hfi]
    simp_rw [Integrable, hfm, hasFiniteIntegral_iff_norm, lt_top_iff_ne_top, Ne, true_and_iff,
      Classical.not_not] at hfi
    have : ∫⁻ a : α, ENNReal.ofReal (f a) ∂μ = ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ := by
      refine lintegral_congr_ae (hf.mono fun a h => ?_)
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg h]
    rw [this, hfi]; rfl

theorem integral_norm_eq_lintegral_nnnorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : AEStronglyMeasurable f μ) : ∫ x, ‖f x‖ ∂μ = ENNReal.toReal (∫⁻ x, ‖f x‖₊ ∂μ) := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hf.norm]
  · simp_rw [ofReal_norm_eq_coe_nnnorm]
  · filter_upwards; simp_rw [Pi.zero_apply, norm_nonneg, imp_true_iff]

theorem ofReal_integral_norm_eq_lintegral_nnnorm {P : Type*} [NormedAddCommGroup P] {f : α → P}
    (hf : Integrable f μ) : ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) = ∫⁻ x, ‖f x‖₊ ∂μ := by
  rw [integral_norm_eq_lintegral_nnnorm hf.aestronglyMeasurable,
    ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hf.2)]

theorem integral_eq_integral_pos_part_sub_integral_neg_part {f : α → ℝ} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∫ a, (Real.toNNReal (f a) : ℝ) ∂μ - ∫ a, (Real.toNNReal (-f a) : ℝ) ∂μ := by
  rw [← integral_sub hf.real_toNNReal]
  · simp
  · exact hf.neg.real_toNNReal

theorem integral_nonneg_of_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a, f a ∂μ := by
  have A : CompleteSpace ℝ := by infer_instance
  simp only [integral_def, A, L1.integral_def, dite_true]
  exact setToFun_nonneg (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf

theorem lintegral_coe_eq_integral (f : α → ℝ≥0) (hfi : Integrable (fun x => (f x : ℝ)) μ) :
    ∫⁻ a, f a ∂μ = ENNReal.ofReal (∫ a, f a ∂μ) := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall fun x => (f x).coe_nonneg)
      hfi.aestronglyMeasurable, ← ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_toReal]
  rw [← lt_top_iff_ne_top]
  convert hfi.hasFiniteIntegral
  -- Porting note: `convert` no longer unfolds `HasFiniteIntegral`
  simp_rw [HasFiniteIntegral, NNReal.nnnorm_eq]

theorem ofReal_integral_eq_lintegral_ofReal {f : α → ℝ} (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have : f =ᵐ[μ] (‖f ·‖) := f_nn.mono fun _x hx ↦ (abs_of_nonneg hx).symm
  simp_rw [integral_congr_ae this, ofReal_integral_norm_eq_lintegral_nnnorm hfi,
    ← ofReal_norm_eq_coe_nnnorm]
  exact lintegral_congr_ae (this.symm.fun_comp ENNReal.ofReal)

theorem integral_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : ∀ᵐ x ∂μ, f x < ∞) :
    ∫ a, (f a).toReal ∂μ = (∫⁻ a, f a ∂μ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.ennreal_toReal.aestronglyMeasurable,
    lintegral_congr_ae (ofReal_toReal_ae_eq hf)]
  exact eventually_of_forall fun x => ENNReal.toReal_nonneg

theorem lintegral_coe_le_coe_iff_integral_le {f : α → ℝ≥0} (hfi : Integrable (fun x => (f x : ℝ)) μ)
    {b : ℝ≥0} : ∫⁻ a, f a ∂μ ≤ b ↔ ∫ a, (f a : ℝ) ∂μ ≤ b := by
  rw [lintegral_coe_eq_integral f hfi, ENNReal.ofReal, ENNReal.coe_le_coe,
    Real.toNNReal_le_iff_le_coe]

theorem integral_coe_le_of_lintegral_coe_le {f : α → ℝ≥0} {b : ℝ≥0} (h : ∫⁻ a, f a ∂μ ≤ b) :
    ∫ a, (f a : ℝ) ∂μ ≤ b := by
  by_cases hf : Integrable (fun a => (f a : ℝ)) μ
  · exact (lintegral_coe_le_coe_iff_integral_le hf).1 h
  · rw [integral_undef hf]; exact b.2

theorem integral_nonneg {f : α → ℝ} (hf : 0 ≤ f) : 0 ≤ ∫ a, f a ∂μ :=
  integral_nonneg_of_ae <| eventually_of_forall hf

theorem integral_nonpos_of_ae {f : α → ℝ} (hf : f ≤ᵐ[μ] 0) : ∫ a, f a ∂μ ≤ 0 := by
  have hf : 0 ≤ᵐ[μ] -f := hf.mono fun a h => by rwa [Pi.neg_apply, Pi.zero_apply, neg_nonneg]
  have : 0 ≤ ∫ a, -f a ∂μ := integral_nonneg_of_ae hf
  rwa [integral_neg, neg_nonneg] at this

theorem integral_nonpos {f : α → ℝ} (hf : f ≤ 0) : ∫ a, f a ∂μ ≤ 0 :=
  integral_nonpos_of_ae <| eventually_of_forall hf

theorem integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ENNReal.toReal_eq_zero_iff,
    ← ENNReal.not_lt_top, ← hasFiniteIntegral_iff_ofReal hf, hfi.2, not_true_eq_false, or_false_iff]
  -- Porting note: split into parts, to make `rw` and `simp` work
  rw [lintegral_eq_zero_iff']
  · rw [← hf.le_iff_eq, Filter.EventuallyEq, Filter.EventuallyLE]
    simp only [Pi.zero_apply, ofReal_eq_zero]
  · exact (ENNReal.measurable_ofReal.comp_aemeasurable hfi.1.aemeasurable)

theorem integral_eq_zero_iff_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
  integral_eq_zero_iff_of_nonneg_ae (eventually_of_forall hf) hfi

lemma integral_eq_iff_of_ae_le {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ = ∫ a, g a ∂μ ↔ f =ᵐ[μ] g := by
  refine ⟨fun h_le ↦ EventuallyEq.symm ?_, fun h ↦ integral_congr_ae h⟩
  rw [← sub_ae_eq_zero,
    ← integral_eq_zero_iff_of_nonneg_ae ((sub_nonneg_ae _ _).mpr hfg) (hg.sub hf)]
  simpa [Pi.sub_apply, integral_sub hg hf, sub_eq_zero, eq_comm]

theorem integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) := by
  simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, Ne, @eq_comm ℝ 0,
    integral_eq_zero_iff_of_nonneg_ae hf hfi, Filter.EventuallyEq, ae_iff, Pi.zero_apply,
    Function.support]

theorem integral_pos_iff_support_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    (0 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support f) :=
  integral_pos_iff_support_of_nonneg_ae (eventually_of_forall hf) hfi

lemma integral_exp_pos {μ : Measure α} {f : α → ℝ} [hμ : NeZero μ]
    (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    0 < ∫ x, Real.exp (f x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (Real.exp_pos _).le) hf]
  suffices (Function.support fun x ↦ Real.exp (f x)) = Set.univ by simp [this, hμ.out]
  ext1 x
  simp only [Function.mem_support, ne_eq, (Real.exp_pos _).ne', not_false_eq_true, Set.mem_univ]

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  -- switch from the Bochner to the Lebesgue integral
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [f', ha (zero_le n)]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    simp_rw [integral_sub (hf _) (hf _), integral_sub' hF (hf 0), tendsto_sub_const_iff] at this
    exact this
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono (zero_le _))
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousAt_toReal (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ) ?_
  swap
  · rw [← ofReal_integral_eq_lintegral_ofReal (hF.sub (hf 0)) hF_ge]
    exact ENNReal.ofReal_ne_top
  refine h_cont.tendsto.comp ?_
  -- use the result for the Lebesgue integral
  refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · exact fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [f', tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

/-- Monotone convergence theorem for real-valued functions and Bochner integrals -/
lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n ↦ ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n ↦ ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simpa [neg_neg] using this
    convert this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx n m hnm using neg_le_neg_iff.mpr <| hx hnm
  · filter_upwards [h_tendsto] with x hx using hx.neg

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
lemma tendsto_of_integral_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  -- reduce to the `ℝ≥0∞` case
  let f' : ℕ → α → ℝ≥0∞ := fun n a ↦ ENNReal.ofReal (f n a - f 0 a)
  let F' : α → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (F a - f 0 a)
  have hf'_int_eq : ∀ i, ∫⁻ a, f' i a ∂μ = ENNReal.ofReal (∫ a, f i a ∂μ - ∫ a, f 0 a ∂μ) := by
    intro i
    unfold_let f'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub (hf_int i) (hf_int 0)]
    · exact (hf_int i).sub (hf_int 0)
    · filter_upwards [hf_mono] with a h_mono
      simp [h_mono (zero_le i)]
  have hF'_int_eq : ∫⁻ a, F' a ∂μ = ENNReal.ofReal (∫ a, F a ∂μ - ∫ a, f 0 a ∂μ) := by
    unfold_let F'
    rw [← ofReal_integral_eq_lintegral_ofReal, integral_sub hF_int (hf_int 0)]
    · exact hF_int.sub (hf_int 0)
    · filter_upwards [hf_bound] with a h_bound
      simp [h_bound 0]
  have h_tendsto : Tendsto (fun i ↦ ∫⁻ a, f' i a ∂μ) atTop (𝓝 (∫⁻ a, F' a ∂μ)) := by
    simp_rw [hf'_int_eq, hF'_int_eq]
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rwa [tendsto_sub_const_iff]
  have h_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f' i a) := by
    filter_upwards [hf_mono] with a ha_mono i j hij
    refine ENNReal.ofReal_le_ofReal ?_
    simp [ha_mono hij]
  have h_bound : ∀ᵐ a ∂μ, ∀ i, f' i a ≤ F' a := by
    filter_upwards [hf_bound] with a ha_bound i
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel, ha_bound i]
  -- use the corresponding lemma for `ℝ≥0∞`
  have h := tendsto_of_lintegral_tendsto_of_monotone ?_ h_tendsto h_mono h_bound ?_
  rotate_left
  · exact (hF_int.1.aemeasurable.sub (hf_int 0).1.aemeasurable).ennreal_ofReal
  · exact ((lintegral_ofReal_le_lintegral_nnnorm _).trans_lt (hF_int.sub (hf_int 0)).2).ne
  filter_upwards [h, hf_mono, hf_bound] with a ha ha_mono ha_bound
  have h1 : (fun i ↦ f i a) = fun i ↦ (f' i a).toReal + f 0 a := by
    unfold_let f'
    ext i
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_mono (zero_le i)]
  have h2 : F a = (F' a).toReal + f 0 a := by
    unfold_let F'
    rw [ENNReal.toReal_ofReal]
    · abel
    · simp [ha_bound 0]
  rw [h1, h2]
  refine Filter.Tendsto.add ?_ tendsto_const_nhds
  exact (ENNReal.continuousAt_toReal ENNReal.ofReal_ne_top).tendsto.comp ha

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
lemma tendsto_of_integral_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf_int : ∀ n, Integrable (f n) μ) (hF_int : Integrable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫ a, f i a ∂μ) atTop (𝓝 (∫ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (hf_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  let f' : ℕ → α → ℝ := fun i a ↦ - f i a
  let F' : α → ℝ := fun a ↦ - F a
  suffices ∀ᵐ a ∂μ, Tendsto (fun i ↦ f' i a) atTop (𝓝 (F' a)) by
    filter_upwards [this] with a ha_tendsto
    convert ha_tendsto.neg
    · simp [f']
    · simp [F']
  refine tendsto_of_integral_tendsto_of_monotone (fun n ↦ (hf_int n).neg) hF_int.neg ?_ ?_ ?_
  · convert hf_tendsto.neg
    · rw [integral_neg]
    · rw [integral_neg]
  · filter_upwards [hf_mono] with a ha i j hij
    simp [f', ha hij]
  · filter_upwards [hf_bound] with a ha i
    simp [f', F', ha i]

section NormedAddCommGroup

variable {H : Type*} [NormedAddCommGroup H]

theorem L1.norm_eq_integral_norm (f : α →₁[μ] H) : ‖f‖ = ∫ a, ‖f a‖ ∂μ := by
  simp only [eLpNorm, eLpNorm', ENNReal.one_toReal, ENNReal.rpow_one, Lp.norm_def, if_false,
    ENNReal.one_ne_top, one_ne_zero, _root_.div_one]
  rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall (by simp [norm_nonneg]))
      (Lp.aestronglyMeasurable f).norm]
  simp [ofReal_norm_eq_coe_nnnorm]

theorem L1.dist_eq_integral_dist (f g : α →₁[μ] H) : dist f g = ∫ a, dist (f a) (g a) ∂μ := by
  simp only [dist_eq_norm, L1.norm_eq_integral_norm]
  exact integral_congr_ae <| (Lp.coeFn_sub _ _).fun_comp norm

theorem L1.norm_of_fun_eq_integral_norm {f : α → H} (hf : Integrable f μ) :
    ‖hf.toL1 f‖ = ∫ a, ‖f a‖ ∂μ := by
  rw [L1.norm_eq_integral_norm]
  exact integral_congr_ae <| hf.coeFn_toL1.fun_comp _

theorem Memℒp.eLpNorm_eq_integral_rpow_norm {f : α → H} {p : ℝ≥0∞} (hp1 : p ≠ 0) (hp2 : p ≠ ∞)
    (hf : Memℒp f p μ) :
    eLpNorm f p μ = ENNReal.ofReal ((∫ a, ‖f a‖ ^ p.toReal ∂μ) ^ p.toReal⁻¹) := by
  have A : ∫⁻ a : α, ENNReal.ofReal (‖f a‖ ^ p.toReal) ∂μ = ∫⁻ a : α, ‖f a‖₊ ^ p.toReal ∂μ := by
    simp_rw [← ofReal_rpow_of_nonneg (norm_nonneg _) toReal_nonneg, ofReal_norm_eq_coe_nnnorm]
  simp only [eLpNorm_eq_lintegral_rpow_nnnorm hp1 hp2, one_div]
  rw [integral_eq_lintegral_of_nonneg_ae]; rotate_left
  · exact ae_of_all _ fun x => by positivity
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  rw [A, ← ofReal_rpow_of_nonneg toReal_nonneg (inv_nonneg.2 toReal_nonneg), ofReal_toReal]
  exact (lintegral_rpow_nnnorm_lt_top_of_eLpNorm_lt_top hp1 hp2 hf.2).ne

@[deprecated (since := "2024-07-27")]
alias Memℒp.snorm_eq_integral_rpow_norm := Memℒp.eLpNorm_eq_integral_rpow_norm

end NormedAddCommGroup

theorem integral_mono_ae {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  have A : CompleteSpace ℝ := by infer_instance
  simp only [integral, A, L1.integral]
  exact setToFun_mono (dominatedFinMeasAdditive_weightedSMul μ)
    (fun s _ _ => weightedSMul_nonneg s) hf hg h

@[mono]
theorem integral_mono {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (h : f ≤ g) :
    ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
  integral_mono_ae hf hg <| eventually_of_forall h

theorem integral_mono_of_nonneg {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgi : Integrable g μ)
    (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  by_cases hfm : AEStronglyMeasurable f μ
  · refine integral_mono_ae ⟨hfm, ?_⟩ hgi h
    refine hgi.hasFiniteIntegral.mono <| h.mp <| hf.mono fun x hf hfg => ?_
    simpa [abs_of_nonneg hf, abs_of_nonneg (le_trans hf hfg)]
  · rw [integral_non_aestronglyMeasurable hfm]
    exact integral_nonneg_of_ae (hf.trans h)

theorem integral_mono_measure {f : α → ℝ} {ν} (hle : μ ≤ ν) (hf : 0 ≤ᵐ[ν] f)
    (hfi : Integrable f ν) : ∫ a, f a ∂μ ≤ ∫ a, f a ∂ν := by
  have hfi' : Integrable f μ := hfi.mono_measure hle
  have hf' : 0 ≤ᵐ[μ] f := hle.absolutelyContinuous hf
  rw [integral_eq_lintegral_of_nonneg_ae hf' hfi'.1, integral_eq_lintegral_of_nonneg_ae hf hfi.1,
    ENNReal.toReal_le_toReal]
  exacts [lintegral_mono' hle le_rfl, ((hasFiniteIntegral_iff_ofReal hf').1 hfi'.2).ne,
    ((hasFiniteIntegral_iff_ofReal hf).1 hfi.2).ne]

theorem norm_integral_le_integral_norm (f : α → G) : ‖∫ a, f a ∂μ‖ ≤ ∫ a, ‖f a‖ ∂μ := by
  have le_ae : ∀ᵐ a ∂μ, 0 ≤ ‖f a‖ := eventually_of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ
  · calc
      ‖∫ a, f a ∂μ‖ ≤ ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) :=
        norm_integral_le_lintegral_norm _
      _ = ∫ a, ‖f a‖ ∂μ := (integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm).symm
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    exact integral_nonneg_of_ae le_ae

theorem norm_integral_le_of_norm_le {f : α → G} {g : α → ℝ} (hg : Integrable g μ)
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) : ‖∫ x, f x ∂μ‖ ≤ ∫ x, g x ∂μ :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm f
    _ ≤ ∫ x, g x ∂μ := integral_mono_of_nonneg (eventually_of_forall fun _ => norm_nonneg _) hg h

theorem SimpleFunc.integral_eq_integral (f : α →ₛ E) (hfi : Integrable f μ) :
    f.integral μ = ∫ x, f x ∂μ := by
  rw [MeasureTheory.integral_eq f hfi, ← L1.SimpleFunc.toLp_one_eq_toL1,
    L1.SimpleFunc.integral_L1_eq_integral, L1.SimpleFunc.integral_eq_integral]
  exact SimpleFunc.integral_congr hfi (Lp.simpleFunc.toSimpleFunc_toLp _ _).symm

theorem SimpleFunc.integral_eq_sum (f : α →ₛ E) (hfi : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ f.range, ENNReal.toReal (μ (f ⁻¹' {x})) • x := by
  rw [← f.integral_eq_integral hfi, SimpleFunc.integral, ← SimpleFunc.integral_eq]; rfl

@[simp]
theorem integral_const (c : E) : ∫ _ : α, c ∂μ = (μ univ).toReal • c := by
  cases' (@le_top _ _ _ (μ univ)).lt_or_eq with hμ hμ
  · haveI : IsFiniteMeasure μ := ⟨hμ⟩
    simp only [integral, hE, L1.integral]
    exact setToFun_const (dominatedFinMeasAdditive_weightedSMul _) _
  · by_cases hc : c = 0
    · simp [hc, integral_zero]
    · have : ¬Integrable (fun _ : α => c) μ := by
        simp only [integrable_const_iff, not_or]
        exact ⟨hc, hμ.not_lt⟩
      simp [integral_undef, *]

theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α → G} {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C * (μ univ).toReal :=
  calc
    ‖∫ x, f x ∂μ‖ ≤ ∫ _, C ∂μ := norm_integral_le_of_norm_le (integrable_const C) h
    _ = C * (μ univ).toReal := by rw [integral_const, smul_eq_mul, mul_comm]

theorem tendsto_integral_approxOn_of_measurable [MeasurableSpace E] [BorelSpace E] {f : α → E}
    {s : Set E} [SeparableSpace s] (hfi : Integrable f μ) (hfm : Measurable f)
    (hs : ∀ᵐ x ∂μ, f x ∈ closure s) {y₀ : E} (h₀ : y₀ ∈ s) (h₀i : Integrable (fun _ => y₀) μ) :
    Tendsto (fun n => (SimpleFunc.approxOn f hfm s y₀ h₀ n).integral μ)
      atTop (𝓝 <| ∫ x, f x ∂μ) := by
  have hfi' := SimpleFunc.integrable_approxOn hfm hfi h₀ h₀i
  simp only [SimpleFunc.integral_eq_integral _ (hfi' _), integral, hE, L1.integral]
  exact tendsto_setToFun_approxOn_of_measurable (dominatedFinMeasAdditive_weightedSMul μ)
    hfi hfm hs h₀ h₀i

theorem tendsto_integral_approxOn_of_measurable_of_range_subset [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (fmeas : Measurable f) (hf : Integrable f μ) (s : Set E) [SeparableSpace s]
    (hs : range f ∪ {0} ⊆ s) :
    Tendsto (fun n => (SimpleFunc.approxOn f fmeas s 0 (hs <| by simp) n).integral μ) atTop
      (𝓝 <| ∫ x, f x ∂μ) := by
  apply tendsto_integral_approxOn_of_measurable hf fmeas _ _ (integrable_zero _ _ _)
  exact eventually_of_forall fun x => subset_closure (hs (Set.mem_union_left _ (mem_range_self _)))

-- We redeclare `E` here to temporarily avoid
-- the `[CompleteSpace E]` and `[NormedSpace ℝ E]` instances.
theorem tendsto_integral_norm_approxOn_sub
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {f : α → E}
    (fmeas : Measurable f) (hf : Integrable f μ) [SeparableSpace (range f ∪ {0} : Set E)] :
    Tendsto (fun n ↦ ∫ x, ‖SimpleFunc.approxOn f fmeas (range f ∪ {0}) 0 (by simp) n x - f x‖ ∂μ)
      atTop (𝓝 0) := by
  convert (tendsto_toReal zero_ne_top).comp (tendsto_approxOn_range_L1_nnnorm fmeas hf) with n
  rw [integral_norm_eq_lintegral_nnnorm]
  · simp
  · apply (SimpleFunc.aestronglyMeasurable _).sub
    apply (stronglyMeasurable_iff_measurable_separable.2 ⟨fmeas, ?_⟩ ).aestronglyMeasurable
    exact .mono (.of_subtype (range f ∪ {0})) subset_union_left

variable {ν : Measure α}

theorem integral_add_measure {f : α → G} (hμ : Integrable f μ) (hν : Integrable f ν) :
    ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  have hfi := hμ.add_measure hν
  simp_rw [integral_eq_setToFun]
  have hμ_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul μ : Set α → G →L[ℝ] G) 1 :=
    DominatedFinMeasAdditive.add_measure_right μ ν (dominatedFinMeasAdditive_weightedSMul μ)
      zero_le_one
  have hν_dfma : DominatedFinMeasAdditive (μ + ν) (weightedSMul ν : Set α → G →L[ℝ] G) 1 :=
    DominatedFinMeasAdditive.add_measure_left μ ν (dominatedFinMeasAdditive_weightedSMul ν)
      zero_le_one
  rw [← setToFun_congr_measure_of_add_right hμ_dfma
        (dominatedFinMeasAdditive_weightedSMul μ) f hfi,
    ← setToFun_congr_measure_of_add_left hν_dfma (dominatedFinMeasAdditive_weightedSMul ν) f hfi]
  refine setToFun_add_left' _ _ _ (fun s _ hμνs => ?_) f
  rw [Measure.coe_add, Pi.add_apply, add_lt_top] at hμνs
  rw [weightedSMul, weightedSMul, weightedSMul, ← add_smul, Measure.coe_add, Pi.add_apply,
  toReal_add hμνs.1.ne hμνs.2.ne]

@[simp]
theorem integral_zero_measure {m : MeasurableSpace α} (f : α → G) :
    (∫ x, f x ∂(0 : Measure α)) = 0 := by
  by_cases hG : CompleteSpace G
  · simp only [integral, hG, L1.integral]
    exact setToFun_measure_zero (dominatedFinMeasAdditive_weightedSMul _) rfl
  · simp [integral, hG]

theorem integral_finset_sum_measure {ι} {m : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    {s : Finset ι} (hf : ∀ i ∈ s, Integrable f (μ i)) :
    ∫ a, f a ∂(∑ i ∈ s, μ i) = ∑ i ∈ s, ∫ a, f a ∂μ i := by
  induction s using Finset.cons_induction_on with
  | h₁ => simp
  | h₂ h ih =>
    rw [Finset.forall_mem_cons] at hf
    rw [Finset.sum_cons, Finset.sum_cons, ← ih hf.2]
    exact integral_add_measure hf.1 (integrable_finset_sum_measure.2 hf.2)

theorem nndist_integral_add_measure_le_lintegral
    {f : α → G} (h₁ : Integrable f μ) (h₂ : Integrable f ν) :
    (nndist (∫ x, f x ∂μ) (∫ x, f x ∂(μ + ν)) : ℝ≥0∞) ≤ ∫⁻ x, ‖f x‖₊ ∂ν := by
  rw [integral_add_measure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact ennnorm_integral_le_lintegral_ennnorm _

theorem hasSum_integral_measure {ι} {m : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    (hf : Integrable f (Measure.sum μ)) :
    HasSum (fun i => ∫ a, f a ∂μ i) (∫ a, f a ∂Measure.sum μ) := by
  have hfi : ∀ i, Integrable f (μ i) := fun i => hf.mono_measure (Measure.le_sum _ _)
  simp only [HasSum, ← integral_finset_sum_measure fun i _ => hfi i]
  refine Metric.nhds_basis_ball.tendsto_right_iff.mpr fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le
  have hf_lt : (∫⁻ x, ‖f x‖₊ ∂Measure.sum μ) < ∞ := hf.2
  have hmem : ∀ᶠ y in 𝓝 (∫⁻ x, ‖f x‖₊ ∂Measure.sum μ), (∫⁻ x, ‖f x‖₊ ∂Measure.sum μ) < y + ε := by
    refine tendsto_id.add tendsto_const_nhds (lt_mem_nhds (α := ℝ≥0∞) <| ENNReal.lt_add_right ?_ ?_)
    exacts [hf_lt.ne, ENNReal.coe_ne_zero.2 (NNReal.coe_ne_zero.1 ε0.ne')]
  refine ((hasSum_lintegral_measure (fun x => ‖f x‖₊) μ).eventually hmem).mono fun s hs => ?_
  obtain ⟨ν, hν⟩ : ∃ ν, (∑ i ∈ s, μ i) + ν = Measure.sum μ := by
    refine ⟨Measure.sum fun i : ↥(sᶜ : Set ι) => μ i, ?_⟩
    simpa only [← Measure.sum_coe_finset] using Measure.sum_add_sum_compl (s : Set ι) μ
  rw [Metric.mem_ball, ← coe_nndist, NNReal.coe_lt_coe, ← ENNReal.coe_lt_coe, ← hν]
  rw [← hν, integrable_add_measure] at hf
  refine (nndist_integral_add_measure_le_lintegral hf.1 hf.2).trans_lt ?_
  rw [← hν, lintegral_add_measure, lintegral_finset_sum_measure] at hs
  exact lt_of_add_lt_add_left hs

theorem integral_sum_measure {ι} {_ : MeasurableSpace α} {f : α → G} {μ : ι → Measure α}
    (hf : Integrable f (Measure.sum μ)) : ∫ a, f a ∂Measure.sum μ = ∑' i, ∫ a, f a ∂μ i :=
  (hasSum_integral_measure hf).tsum_eq.symm

@[simp]
theorem integral_smul_measure (f : α → G) (c : ℝ≥0∞) :
    ∫ x, f x ∂c • μ = c.toReal • ∫ x, f x ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  -- First we consider the “degenerate” case `c = ∞`
  rcases eq_or_ne c ∞ with (rfl | hc)
  · rw [ENNReal.top_toReal, zero_smul, integral_eq_setToFun, setToFun_top_smul_measure]
  -- Main case: `c ≠ ∞`
  simp_rw [integral_eq_setToFun, ← setToFun_smul_left]
  have hdfma : DominatedFinMeasAdditive μ (weightedSMul (c • μ) : Set α → G →L[ℝ] G) c.toReal :=
    mul_one c.toReal ▸ (dominatedFinMeasAdditive_weightedSMul (c • μ)).of_smul_measure c hc
  have hdfma_smul := dominatedFinMeasAdditive_weightedSMul (F := G) (c • μ)
  rw [← setToFun_congr_smul_measure c hc hdfma hdfma_smul f]
  exact setToFun_congr_left' _ _ (fun s _ _ => weightedSMul_smul_measure μ c) f

@[simp]
theorem integral_smul_nnreal_measure (f : α → G) (c : ℝ≥0) :
    ∫ x, f x ∂(c • μ) = c • ∫ x, f x ∂μ :=
  integral_smul_measure f (c : ℝ≥0∞)

theorem integral_map_of_stronglyMeasurable {β} [MeasurableSpace β] {φ : α → β} (hφ : Measurable φ)
    {f : β → G} (hfm : StronglyMeasurable f) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  by_cases hfi : Integrable f (Measure.map φ μ); swap
  · rw [integral_undef hfi, integral_undef]
    exact fun hfφ => hfi ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).2 hfφ)
  borelize G
  have : SeparableSpace (range f ∪ {0} : Set G) := hfm.separableSpace_range_union_singleton
  refine tendsto_nhds_unique
    (tendsto_integral_approxOn_of_measurable_of_range_subset hfm.measurable hfi _ Subset.rfl) ?_
  convert tendsto_integral_approxOn_of_measurable_of_range_subset (hfm.measurable.comp hφ)
    ((integrable_map_measure hfm.aestronglyMeasurable hφ.aemeasurable).1 hfi) (range f ∪ {0})
    (by simp [insert_subset_insert, Set.range_comp_subset_range]) using 1
  ext1 i
  simp only [SimpleFunc.approxOn_comp, SimpleFunc.integral_eq, Measure.map_apply, hφ,
    SimpleFunc.measurableSet_preimage, ← preimage_comp, SimpleFunc.coe_comp]
  refine (Finset.sum_subset (SimpleFunc.range_comp_subset_range _ hφ) fun y _ hy => ?_).symm
  rw [SimpleFunc.mem_range, ← Set.preimage_singleton_eq_empty, SimpleFunc.coe_comp] at hy
  rw [hy]
  simp

theorem integral_map {β} [MeasurableSpace β] {φ : α → β} (hφ : AEMeasurable φ μ) {f : β → G}
    (hfm : AEStronglyMeasurable f (Measure.map φ μ)) :
    ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  let g := hfm.mk f
  calc
    ∫ y, f y ∂Measure.map φ μ = ∫ y, g y ∂Measure.map φ μ := integral_congr_ae hfm.ae_eq_mk
    _ = ∫ y, g y ∂Measure.map (hφ.mk φ) μ := by congr 1; exact Measure.map_congr hφ.ae_eq_mk
    _ = ∫ x, g (hφ.mk φ x) ∂μ :=
      (integral_map_of_stronglyMeasurable hφ.measurable_mk hfm.stronglyMeasurable_mk)
    _ = ∫ x, g (φ x) ∂μ := integral_congr_ae (hφ.ae_eq_mk.symm.fun_comp _)
    _ = ∫ x, f (φ x) ∂μ := integral_congr_ae <| ae_eq_comp hφ hfm.ae_eq_mk.symm

theorem _root_.MeasurableEmbedding.integral_map {β} {_ : MeasurableSpace β} {f : α → β}
    (hf : MeasurableEmbedding f) (g : β → G) : ∫ y, g y ∂Measure.map f μ = ∫ x, g (f x) ∂μ := by
  by_cases hgm : AEStronglyMeasurable g (Measure.map f μ)
  · exact MeasureTheory.integral_map hf.measurable.aemeasurable hgm
  · rw [integral_non_aestronglyMeasurable hgm, integral_non_aestronglyMeasurable]
    exact fun hgf => hgm (hf.aestronglyMeasurable_map_iff.2 hgf)

theorem _root_.ClosedEmbedding.integral_map {β} [TopologicalSpace α] [BorelSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] {φ : α → β} (hφ : ClosedEmbedding φ)
    (f : β → G) : ∫ y, f y ∂Measure.map φ μ = ∫ x, f (φ x) ∂μ :=
  hφ.measurableEmbedding.integral_map _

theorem integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β → G) :
    ∫ y, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ :=
  e.measurableEmbedding.integral_map f

theorem MeasurePreserving.integral_comp {β} {_ : MeasurableSpace β} {f : α → β} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν :=
  h₁.map_eq ▸ (h₂.integral_map g).symm

theorem MeasurePreserving.integral_comp' {β} [MeasurableSpace β] {ν} {f : α ≃ᵐ β}
    (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

theorem integral_subtype_comap {α} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f (x : α) ∂(Measure.comap Subtype.val μ) = ∫ x in s, f x ∂μ := by
  rw [← map_comap_subtype_coe hs]
  exact ((MeasurableEmbedding.subtype_coe hs).integral_map _).symm

attribute [local instance] Measure.Subtype.measureSpace in
theorem integral_subtype {α} [MeasureSpace α] {s : Set α} (hs : MeasurableSet s) (f : α → G) :
    ∫ x : s, f x = ∫ x in s, f x := integral_subtype_comap hs f

@[simp]
theorem integral_dirac' [MeasurableSpace α] (f : α → E) (a : α) (hfm : StronglyMeasurable f) :
    ∫ x, f x ∂Measure.dirac a = f a := by
  borelize E
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a :=
      integral_congr_ae <| ae_eq_dirac' hfm.measurable
    _ = f a := by simp [Measure.dirac_apply_of_mem]

@[simp]
theorem integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α) :
    ∫ x, f x ∂Measure.dirac a = f a :=
  calc
    ∫ x, f x ∂Measure.dirac a = ∫ _, f a ∂Measure.dirac a := integral_congr_ae <| ae_eq_dirac f
    _ = f a := by simp [Measure.dirac_apply_of_mem]

theorem setIntegral_dirac' {mα : MeasurableSpace α} {f : α → E} (hf : StronglyMeasurable f) (a : α)
    {s : Set α} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac' hs]
  split_ifs
  · exact integral_dirac' _ _ hf
  · exact integral_zero_measure _

@[deprecated (since := "2024-04-17")]
alias set_integral_dirac' := setIntegral_dirac'

theorem setIntegral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → E) (a : α)
    (s : Set α) [Decidable (a ∈ s)] :
    ∫ x in s, f x ∂Measure.dirac a = if a ∈ s then f a else 0 := by
  rw [restrict_dirac]
  split_ifs
  · exact integral_dirac _ _
  · exact integral_zero_measure _

@[deprecated (since := "2024-04-17")]
alias set_integral_dirac := setIntegral_dirac

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_integral_of_nonneg {f : α → ℝ} (hf_nonneg : 0 ≤ᵐ[μ] f)
    (hf_int : Integrable f μ) (ε : ℝ) : ε * (μ { x | ε ≤ f x }).toReal ≤ ∫ x, f x ∂μ := by
  cases' eq_top_or_lt_top (μ {x | ε ≤ f x}) with hμ hμ
  · simpa [hμ] using integral_nonneg_of_ae hf_nonneg
  · have := Fact.mk hμ
    calc
      ε * (μ { x | ε ≤ f x }).toReal = ∫ _ in {x | ε ≤ f x}, ε ∂μ := by simp [mul_comm]
      _ ≤ ∫ x in {x | ε ≤ f x}, f x ∂μ :=
        integral_mono_ae (integrable_const _) (hf_int.mono_measure μ.restrict_le_self) <|
          ae_restrict_mem₀ <| hf_int.aemeasurable.nullMeasurable measurableSet_Ici
      _ ≤ _ := integral_mono_measure μ.restrict_le_self hf_nonneg hf_int

/-- Hölder's inequality for the integral of a product of norms. The integral of the product of two
norms of functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are
conjugate exponents. -/
theorem integral_mul_norm_le_Lp_mul_Lq {E} [NormedAddCommGroup E] {f g : α → E} {p q : ℝ}
    (hpq : p.IsConjExponent q) (hf : Memℒp f (ENNReal.ofReal p) μ)
    (hg : Memℒp g (ENNReal.ofReal q) μ) :
    ∫ a, ‖f a‖ * ‖g a‖ ∂μ ≤ (∫ a, ‖f a‖ ^ p ∂μ) ^ (1 / p) * (∫ a, ‖g a‖ ^ q ∂μ) ^ (1 / q) := by
  -- translate the Bochner integrals into Lebesgue integrals.
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae,
    integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact eventually_of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _
  · exact (hg.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact eventually_of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _
  · exact (hf.1.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  · exact eventually_of_forall fun x => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · exact hf.1.norm.mul hg.1.norm
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  -- replace norms by nnnorm
  have h_left : ∫⁻ a, ENNReal.ofReal (‖f a‖ * ‖g a‖) ∂μ =
      ∫⁻ a, ((fun x => (‖f x‖₊ : ℝ≥0∞)) * fun x => (‖g x‖₊ : ℝ≥0∞)) a ∂μ := by
    simp_rw [Pi.mul_apply, ← ofReal_norm_eq_coe_nnnorm, ENNReal.ofReal_mul (norm_nonneg _)]
  have h_right_f : ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ p) ∂μ = ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_coe_nnnorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.nonneg]
  have h_right_g : ∫⁻ a, ENNReal.ofReal (‖g a‖ ^ q) ∂μ = ∫⁻ a, (‖g a‖₊ : ℝ≥0∞) ^ q ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_coe_nnnorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hpq.symm.nonneg]
  rw [h_left, h_right_f, h_right_g]
  -- we can now apply `ENNReal.lintegral_mul_le_Lp_mul_Lq` (up to the `toReal` application)
  refine ENNReal.toReal_mono ?_ ?_
  · refine ENNReal.mul_ne_top ?_ ?_
    · convert hf.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_nnnorm]
      · rw [ENNReal.toReal_ofReal hpq.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.pos
      · exact ENNReal.coe_ne_top
    · convert hg.eLpNorm_ne_top
      rw [eLpNorm_eq_lintegral_rpow_nnnorm]
      · rw [ENNReal.toReal_ofReal hpq.symm.nonneg]
      · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        exact hpq.symm.pos
      · exact ENNReal.coe_ne_top
  · exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.1.nnnorm.aemeasurable.coe_nnreal_ennreal
      hg.1.nnnorm.aemeasurable.coe_nnreal_ennreal

/-- Hölder's inequality for functions `α → ℝ`. The integral of the product of two nonnegative
functions is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.IsConjExponent q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : Memℒp f (ENNReal.ofReal p) μ)
    (hg : Memℒp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q) := by
  have h_left : ∫ a, f a * g a ∂μ = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg, hg_nonneg] with x hxf hxg
    rw [Real.norm_of_nonneg hxf, Real.norm_of_nonneg hxg]
  have h_right_f : ∫ a, f a ^ p ∂μ = ∫ a, ‖f a‖ ^ p ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf_nonneg] with x hxf
    rw [Real.norm_of_nonneg hxf]
  have h_right_g : ∫ a, g a ^ q ∂μ = ∫ a, ‖g a‖ ^ q ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hg_nonneg] with x hxg
    rw [Real.norm_of_nonneg hxg]
  rw [h_left, h_right_f, h_right_g]
  exact integral_mul_norm_le_Lp_mul_Lq hpq hf hg

theorem integral_countable' [Countable α] [MeasurableSingletonClass α] {μ : Measure α}
    {f : α → E} (hf : Integrable f μ) :
    ∫ a, f a ∂μ = ∑' a, (μ {a}).toReal • f a := by
  rw [← Measure.sum_smul_dirac μ] at hf
  rw [← Measure.sum_smul_dirac μ, integral_sum_measure hf]
  congr 1 with a : 1
  rw [integral_smul_measure, integral_dirac, Measure.sum_smul_dirac]

theorem integral_singleton' {μ : Measure α} {f : α → E} (hf : StronglyMeasurable f) (a : α) :
    ∫ a in {a}, f a ∂μ = (μ {a}).toReal • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac' f a hf, smul_eq_mul,
    mul_comm]

theorem integral_singleton [MeasurableSingletonClass α] {μ : Measure α} (f : α → E) (a : α) :
    ∫ a in {a}, f a ∂μ = (μ {a}).toReal • f a := by
  simp only [Measure.restrict_singleton, integral_smul_measure, integral_dirac, smul_eq_mul,
    mul_comm]

theorem integral_countable [MeasurableSingletonClass α] (f : α → E) {s : Set α} (hs : s.Countable)
    (hf : Integrable f (μ.restrict s)) :
    ∫ a in s, f a ∂μ = ∑' a : s, (μ {(a : α)}).toReal • f a := by
  have hi : Countable { x // x ∈ s } := Iff.mpr countable_coe_iff hs
  have hf' : Integrable (fun (x : s) => f x) (Measure.comap Subtype.val μ) := by
    rw [← map_comap_subtype_coe, integrable_map_measure] at hf
    · apply hf
    · exact Integrable.aestronglyMeasurable hf
    · exact Measurable.aemeasurable measurable_subtype_coe
    · exact Countable.measurableSet hs
  rw [← integral_subtype_comap hs.measurableSet, integral_countable' hf']
  congr 1 with a : 1
  rw [Measure.comap_apply Subtype.val Subtype.coe_injective
    (fun s' hs' => MeasurableSet.subtype_image (Countable.measurableSet hs) hs') _
    (MeasurableSet.singleton a)]
  simp

theorem integral_finset [MeasurableSingletonClass α] (s : Finset α) (f : α → E)
    (hf : Integrable f (μ.restrict s)) :
    ∫ x in s, f x ∂μ = ∑ x ∈ s, (μ {x}).toReal • f x := by
  rw [integral_countable _ s.countable_toSet hf, ← Finset.tsum_subtype']

theorem integral_fintype [MeasurableSingletonClass α] [Fintype α] (f : α → E)
    (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • f x := by
  -- NB: Integrable f does not follow from Fintype, because the measure itself could be non-finite
  rw [← integral_finset .univ, Finset.coe_univ, Measure.restrict_univ]
  simp only [Finset.coe_univ, Measure.restrict_univ, hf]

theorem integral_unique [Unique α] (f : α → E) : ∫ x, f x ∂μ = (μ univ).toReal • f default :=
  calc
    ∫ x, f x ∂μ = ∫ _, f default ∂μ := by congr with x; congr; exact Unique.uniq _ x
    _ = (μ univ).toReal • f default := by rw [integral_const]

theorem integral_pos_of_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    {f : α → ℝ} {x : α} (f_cont : Continuous f) (f_int : Integrable f μ) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ x, f x ∂μ :=
  (integral_pos_iff_support_of_nonneg f_nonneg f_int).2
    (IsOpen.measure_pos μ f_cont.isOpen_support ⟨x, f_x⟩)

end Properties

section IntegralTrim

variable {H β γ : Type*} [NormedAddCommGroup H] {m m0 : MeasurableSpace β} {μ : Measure β}

/-- Simple function seen as simple function of a larger `MeasurableSpace`. -/
def SimpleFunc.toLargerSpace (hm : m ≤ m0) (f : @SimpleFunc β m γ) : SimpleFunc β γ :=
  ⟨@SimpleFunc.toFun β m γ f, fun x => hm _ (@SimpleFunc.measurableSet_fiber β γ m f x),
    @SimpleFunc.finite_range β γ m f⟩

theorem SimpleFunc.coe_toLargerSpace_eq (hm : m ≤ m0) (f : @SimpleFunc β m γ) :
    ⇑(f.toLargerSpace hm) = f := rfl

theorem integral_simpleFunc_larger_space (hm : m ≤ m0) (f : @SimpleFunc β m F)
    (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ x ∈ @SimpleFunc.range β F m f, ENNReal.toReal (μ (f ⁻¹' {x})) • x := by
  simp_rw [← f.coe_toLargerSpace_eq hm]
  have hf_int : Integrable (f.toLargerSpace hm) μ := by rwa [SimpleFunc.coe_toLargerSpace_eq]
  rw [SimpleFunc.integral_eq_sum _ hf_int]
  congr 1

theorem integral_trim_simpleFunc (hm : m ≤ m0) (f : @SimpleFunc β m F) (hf_int : Integrable f μ) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  have hf : StronglyMeasurable[m] f := @SimpleFunc.stronglyMeasurable β F m _ f
  have hf_int_m := hf_int.trim hm hf
  rw [integral_simpleFunc_larger_space (le_refl m) f hf_int_m,
    integral_simpleFunc_larger_space hm f hf_int]
  congr with x
  congr 2
  exact (trim_measurableSet_eq hm (@SimpleFunc.measurableSet_fiber β F m f x)).symm

theorem integral_trim (hm : m ≤ m0) {f : β → G} (hf : StronglyMeasurable[m] f) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, hG]
  borelize G
  by_cases hf_int : Integrable f μ
  swap
  · have hf_int_m : ¬Integrable f (μ.trim hm) := fun hf_int_m =>
      hf_int (integrable_of_integrable_trim hm hf_int_m)
    rw [integral_undef hf_int, integral_undef hf_int_m]
  haveI : SeparableSpace (range f ∪ {0} : Set G) := hf.separableSpace_range_union_singleton
  let f_seq := @SimpleFunc.approxOn G β _ _ _ m _ hf.measurable (range f ∪ {0}) 0 (by simp) _
  have hf_seq_meas : ∀ n, StronglyMeasurable[m] (f_seq n) := fun n =>
    @SimpleFunc.stronglyMeasurable β G m _ (f_seq n)
  have hf_seq_int : ∀ n, Integrable (f_seq n) μ :=
    SimpleFunc.integrable_approxOn_range (hf.mono hm).measurable hf_int
  have hf_seq_int_m : ∀ n, Integrable (f_seq n) (μ.trim hm) := fun n =>
    (hf_seq_int n).trim hm (hf_seq_meas n)
  have hf_seq_eq : ∀ n, ∫ x, f_seq n x ∂μ = ∫ x, f_seq n x ∂μ.trim hm := fun n =>
    integral_trim_simpleFunc hm (f_seq n) (hf_seq_int n)
  have h_lim_1 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_L1 f hf_int (eventually_of_forall hf_seq_int) ?_
    exact SimpleFunc.tendsto_approxOn_range_L1_nnnorm (hf.mono hm).measurable hf_int
  have h_lim_2 : atTop.Tendsto (fun n => ∫ x, f_seq n x ∂μ) (𝓝 (∫ x, f x ∂μ.trim hm)) := by
    simp_rw [hf_seq_eq]
    refine @tendsto_integral_of_L1 β G _ _ m (μ.trim hm) _ f (hf_int.trim hm hf) _ _
      (eventually_of_forall hf_seq_int_m) ?_
    exact @SimpleFunc.tendsto_approxOn_range_L1_nnnorm β G m _ _ _ f _ _ hf.measurable
      (hf_int.trim hm hf)
  exact tendsto_nhds_unique h_lim_1 h_lim_2

theorem integral_trim_ae (hm : m ≤ m0) {f : β → G} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm := by
  rw [integral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), integral_congr_ae hf.ae_eq_mk]
  exact integral_trim hm hf.stronglyMeasurable_mk

theorem ae_eq_trim_of_stronglyMeasurable [TopologicalSpace γ] [MetrizableSpace γ] (hm : m ≤ m0)
    {f g : β → γ} (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
    (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.trim hm] g := by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl

theorem ae_eq_trim_iff [TopologicalSpace γ] [MetrizableSpace γ] (hm : m ≤ m0) {f g : β → γ}
    (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

theorem ae_le_trim_of_stronglyMeasurable [LinearOrder γ] [TopologicalSpace γ]
    [OrderClosedTopology γ] [PseudoMetrizableSpace γ] (hm : m ≤ m0) {f g : β → γ}
    (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) (hfg : f ≤ᵐ[μ] g) :
    f ≤ᵐ[μ.trim hm] g := by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl

theorem ae_le_trim_iff [LinearOrder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    [PseudoMetrizableSpace γ] (hm : m ≤ m0) {f g : β → γ} (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) : f ≤ᵐ[μ.trim hm] g ↔ f ≤ᵐ[μ] g :=
  ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

end IntegralTrim

section SnormBound

variable {m0 : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}

theorem eLpNorm_one_le_of_le {r : ℝ≥0} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * r := by
  by_cases hr : r = 0
  · suffices f =ᵐ[μ] 0 by
      rw [eLpNorm_congr_ae this, eLpNorm_zero, hr, ENNReal.coe_zero, mul_zero]
    rw [hr] at hf
    norm_cast at hf
    -- Porting note: two lines above were
    --rw [hr, Nonneg.coe_zero] at hf
    have hnegf : ∫ x, -f x ∂μ = 0 := by
      rw [integral_neg, neg_eq_zero]
      exact le_antisymm (integral_nonpos_of_ae hf) hfint'
    have := (integral_eq_zero_iff_of_nonneg_ae ?_ hfint.neg).1 hnegf
    · filter_upwards [this] with ω hω
      rwa [Pi.neg_apply, Pi.zero_apply, neg_eq_zero] at hω
    · filter_upwards [hf] with ω hω
      rwa [Pi.zero_apply, Pi.neg_apply, Right.nonneg_neg_iff]
  by_cases hμ : IsFiniteMeasure μ
  swap
  · have : μ Set.univ = ∞ := by
      by_contra hμ'
      exact hμ (IsFiniteMeasure.mk <| lt_top_iff_ne_top.2 hμ')
    rw [this, ENNReal.mul_top', if_neg, ENNReal.top_mul', if_neg]
    · exact le_top
    · simp [hr]
    · norm_num
  haveI := hμ
  rw [integral_eq_integral_pos_part_sub_integral_neg_part hfint, sub_nonneg] at hfint'
  have hposbdd : ∫ ω, max (f ω) 0 ∂μ ≤ (μ Set.univ).toReal • (r : ℝ) := by
    rw [← integral_const]
    refine integral_mono_ae hfint.real_toNNReal (integrable_const (r : ℝ)) ?_
    filter_upwards [hf] with ω hω using Real.toNNReal_le_iff_le_coe.2 hω
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (memℒp_one_iff_integrable.2 hfint),
    ENNReal.ofReal_le_iff_le_toReal
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.two_ne_top <| @measure_ne_top _ _ _ hμ _)
        ENNReal.coe_ne_top)]
  simp_rw [ENNReal.one_toReal, _root_.inv_one, Real.rpow_one, Real.norm_eq_abs, ←
    max_zero_add_max_neg_zero_eq_abs_self, ← Real.coe_toNNReal']
  rw [integral_add hfint.real_toNNReal]
  · simp only [Real.coe_toNNReal', ENNReal.toReal_mul, ENNReal.one_toReal, ENNReal.coe_toReal,
      Left.nonneg_neg_iff, Left.neg_nonpos_iff, toReal_ofNat] at hfint' ⊢
    refine (add_le_add_left hfint' _).trans ?_
    rwa [← two_mul, mul_assoc, mul_le_mul_left (two_pos : (0 : ℝ) < 2)]
  · exact hfint.neg.sup (integrable_zero _ _ μ)

@[deprecated (since := "2024-07-27")]
alias snorm_one_le_of_le := eLpNorm_one_le_of_le

theorem eLpNorm_one_le_of_le' {r : ℝ} (hfint : Integrable f μ) (hfint' : 0 ≤ ∫ x, f x ∂μ)
    (hf : ∀ᵐ ω ∂μ, f ω ≤ r) : eLpNorm f 1 μ ≤ 2 * μ Set.univ * ENNReal.ofReal r := by
  refine eLpNorm_one_le_of_le hfint hfint' ?_
  simp only [Real.coe_toNNReal', le_max_iff]
  filter_upwards [hf] with ω hω using Or.inl hω

@[deprecated (since := "2024-07-27")]
alias snorm_one_le_of_le' := eLpNorm_one_le_of_le'

end SnormBound

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Qq Lean Meta MeasureTheory

/-- Positivity extension for integrals.

This extension only proves non-negativity, strict positivity is more delicate for integration and
requires more assumptions. -/
@[positivity MeasureTheory.integral _ _]
def evalIntegral : PositivityExt where eval {u α} zα pα e := do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@MeasureTheory.integral $i ℝ _ $inst2 _ _ $f) =>
    let i : Q($i) ← mkFreshExprMVarQ q($i) .syntheticOpaque
    have body : Q(ℝ) := .betaRev f #[i]
    let rbody ← core zα pα body
    let pbody ← rbody.toNonneg
    let pr : Q(∀ x, 0 ≤ $f x) ← mkLambdaFVars #[i] pbody
    assertInstancesCommute
    return .nonnegative q(integral_nonneg $pr)
  | _ => throwError "not MeasureTheory.integral"

end Mathlib.Meta.Positivity
