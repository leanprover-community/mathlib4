/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.SetToL1

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here
for L1 functions by extending the integral on simple functions. See the file
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` for the integral of functions
and corresponding API.

## Main definitions

The Bochner integral is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `weightedSMul μ s x = μ.real s * x`.
  `weightedSMul μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on simple functions of the type `SimpleFunc α E` (notation : `α →ₛ E`)
  where `E` is a real normed space. (See `SimpleFunc.integral` for details.)

3. Transfer this definition to define the integral on `L1.simpleFunc α E` (notation :
  `α →₁ₛ[μ] E`), see `L1.simpleFunc.integral`. Show that this integral is a continuous linear
  map from `α →₁ₛ[μ] E` to `E`.

4. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `ContinuousLinearMap.extend` and the fact that the embedding of
  `α →₁ₛ[μ] E` into `α →₁[μ] E` is dense.

## Notations

* `α →ₛ E` : simple functions (defined in `Mathlib/MeasureTheory/Function/SimpleFunc.lean`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions (defined in `Mathlib/MeasureTheory/Function/SimpleFuncDense`)

We also define notations for integral on a set, which are described in the file
`Mathlib/MeasureTheory/Integral/SetIntegral.lean`.

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if the font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/


assert_not_exists Differentiable

noncomputable section

open Filter ENNReal Set
open scoped NNReal ENNReal MeasureTheory

namespace MeasureTheory

variable {α E F 𝕜 : Type*}

section WeightedSMul

open ContinuousLinearMap

variable [NormedAddCommGroup F] [NormedSpace ℝ F] {m : MeasurableSpace α} {μ : Measure α}

/-- Given a set `s`, return the continuous linear map `fun x => μ.real s • x`. The extension
of that set function through `setToL1` gives the Bochner integral of L1 functions. -/
def weightedSMul {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : F →L[ℝ] F :=
  μ.real s • ContinuousLinearMap.id ℝ F

theorem weightedSMul_apply {m : MeasurableSpace α} (μ : Measure α) (s : Set α) (x : F) :
    weightedSMul μ s x = μ.real s • x := by simp [weightedSMul]

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
  rw [measureReal_add_apply, add_smul]

theorem weightedSMul_smul_measure {m : MeasurableSpace α} (μ : Measure α) (c : ℝ≥0∞) {s : Set α} :
    (weightedSMul (c • μ) s : F →L[ℝ] F) = c.toReal • weightedSMul μ s := by
  ext1 x
  simp [weightedSMul_apply, smul_smul]

theorem weightedSMul_congr (s t : Set α) (hst : μ s = μ t) :
    (weightedSMul μ s : F →L[ℝ] F) = weightedSMul μ t := by
  ext1 x; simp_rw [weightedSMul_apply, measureReal_def]; congr 2

theorem weightedSMul_null {s : Set α} (h_zero : μ s = 0) : (weightedSMul μ s : F →L[ℝ] F) = 0 := by
  ext1 x; rw [weightedSMul_apply, measureReal_def, h_zero]; simp

theorem weightedSMul_union' (s t : Set α) (ht : MeasurableSet t) (hs_finite : μ s ≠ ∞)
    (ht_finite : μ t ≠ ∞) (hdisj : Disjoint s t) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t := by
  ext1 x
  simp_rw [add_apply, weightedSMul_apply, measureReal_union hdisj ht,add_smul]

@[nolint unusedArguments]
theorem weightedSMul_union (s t : Set α) (_hs : MeasurableSet s) (ht : MeasurableSet t)
    (hs_finite : μ s ≠ ∞) (ht_finite : μ t ≠ ∞) (hdisj : Disjoint s t) :
    (weightedSMul μ (s ∪ t) : F →L[ℝ] F) = weightedSMul μ s + weightedSMul μ t :=
  weightedSMul_union' s t ht hs_finite ht_finite hdisj

theorem weightedSMul_smul [SMul 𝕜 F] [SMulCommClass ℝ 𝕜 F] (c : 𝕜)
    (s : Set α) (x : F) : weightedSMul μ s (c • x) = c • weightedSMul μ s x := by
  simp_rw [weightedSMul_apply, smul_comm]

theorem norm_weightedSMul_le (s : Set α) : ‖(weightedSMul μ s : F →L[ℝ] F)‖ ≤ μ.real s :=
  calc
    ‖(weightedSMul μ s : F →L[ℝ] F)‖ = ‖μ.real s‖ * ‖ContinuousLinearMap.id ℝ F‖ :=
      norm_smul (μ.real s) (ContinuousLinearMap.id ℝ F)
    _ ≤ ‖μ.real s‖ :=
      ((mul_le_mul_of_nonneg_left norm_id_le (norm_nonneg _)).trans (mul_one _).le)
    _ = abs μ.real s := Real.norm_eq_abs _
    _ = μ.real s := abs_eq_self.mpr ENNReal.toReal_nonneg

theorem dominatedFinMeasAdditive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) :
    DominatedFinMeasAdditive μ (weightedSMul μ : Set α → F →L[ℝ] F) 1 :=
  ⟨weightedSMul_union, fun s _ _ => (norm_weightedSMul_le s).trans (one_mul _).symm.le⟩

theorem weightedSMul_nonneg [PartialOrder F] [IsOrderedModule ℝ F]
    (s : Set α) (x : F) (hx : 0 ≤ x) : 0 ≤ weightedSMul μ s x := by
  simp only [weightedSMul, coe_smul', _root_.id, coe_id', Pi.smul_apply]
  exact smul_nonneg toReal_nonneg hx

end WeightedSMul

local infixr:25 " →ₛ " => SimpleFunc

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

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : MeasurableSpace α} {μ : Measure α}

/-- Bochner integral of simple functions whose codomain is a real `NormedSpace`.
This is equal to `∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x` (see `integral_eq`). -/
def integral {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) : F :=
  f.setToSimpleFunc (weightedSMul μ)

theorem integral_def {_ : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = f.setToSimpleFunc (weightedSMul μ) := rfl

theorem integral_eq {m : MeasurableSpace α} (μ : Measure α) (f : α →ₛ F) :
    f.integral μ = ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) • x := by
  simp [integral, setToSimpleFunc, weightedSMul_apply]

theorem integral_eq_sum_filter [DecidablePred fun x : F => x ≠ 0] {m : MeasurableSpace α}
    (f : α →ₛ F) (μ : Measure α) :
    f.integral μ = ∑ x ∈ {x ∈ f.range | x ≠ 0}, μ.real (f ⁻¹' {x}) • x := by
  simp_rw [integral_def, setToSimpleFunc_eq_sum_filter, weightedSMul_apply]

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
theorem integral_eq_sum_of_subset [DecidablePred fun x : F => x ≠ 0] {f : α →ₛ F} {s : Finset F}
    (hs : {x ∈ f.range | x ≠ 0} ⊆ s) :
    f.integral μ = ∑ x ∈ s, μ.real (f ⁻¹' {x}) • x := by
  rw [SimpleFunc.integral_eq_sum_filter, Finset.sum_subset hs]
  rintro x - hx; rw [Finset.mem_filter, not_and_or, Ne, Classical.not_not] at hx
  rcases hx.symm with (rfl | hx)
  · simp
  rw [SimpleFunc.mem_range] at hx
  rw [preimage_eq_empty] <;> simp [Set.disjoint_singleton_left, hx]

@[simp]
theorem integral_const {m : MeasurableSpace α} (μ : Measure α) (y : F) :
    (const α y).integral μ = μ.real univ • y := by
  classical
  calc
    (const α y).integral μ = ∑ z ∈ {y}, μ.real (const α y ⁻¹' {z}) • z :=
      integral_eq_sum_of_subset <| (filter_subset _ _).trans (range_const_subset _ _)
    _ = μ.real univ • y := by simp [Set.preimage]

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
    rw [Set.piecewise_eq_indicator, indicator_preimage_of_notMem,
      measureReal_restrict_apply (f.measurableSet_preimage _)]
    exact fun h₀ => (mem_filter.1 hy).2 (Eq.symm h₀)

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
theorem map_integral (f : α →ₛ E) (g : E → F) (hf : Integrable f μ) (hg : g 0 = 0) :
    (f.map g).integral μ = ∑ x ∈ f.range, (μ.real (f ⁻¹' {x})) • g x :=
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
    rw [smul_eq_mul, toReal_mul, mul_comm, Function.comp_apply, measureReal_def]
  · rintro a -
    by_cases a0 : a = 0
    · rw [a0, hg0, zero_mul]; exact WithTop.zero_ne_top
    · apply mul_ne_top (ht a) (hf'.meas_preimage_singleton_ne_zero a0).ne
  · simp [hg0]

variable [NormedSpace ℝ E]

theorem integral_congr {f g : α →ₛ E} (hf : Integrable f μ) (h : f =ᵐ[μ] g) :
    f.integral μ = g.integral μ :=
  setToSimpleFunc_congr (weightedSMul μ) (fun _ _ => weightedSMul_null) weightedSMul_union hf h

/-- `SimpleFunc.integral` and `SimpleFunc.lintegral` agree when the integrand has type
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

theorem integral_smul [DistribSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
    (c : 𝕜) {f : α →ₛ E} (hf : Integrable f μ) :
    integral μ (c • f) = c • integral μ f :=
  setToSimpleFunc_smul _ weightedSMul_union weightedSMul_smul c hf

theorem norm_setToSimpleFunc_le_integral_norm (T : Set α → E →L[ℝ] F) {C : ℝ}
    (hT_norm : ∀ s, MeasurableSet s → μ s < ∞ → ‖T s‖ ≤ C * μ.real s) {f : α →ₛ E}
    (hf : Integrable f μ) : ‖f.setToSimpleFunc T‖ ≤ C * (f.map norm).integral μ :=
  calc
    ‖f.setToSimpleFunc T‖ ≤ C * ∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * ‖x‖ :=
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

section Order

variable [PartialOrder F] [IsOrderedAddMonoid F] [IsOrderedModule ℝ F]

lemma integral_nonneg {f : α →ₛ F} (hf : 0 ≤ᵐ[μ] f) :
    0 ≤ f.integral μ := by
  rw [integral_eq]
  apply Finset.sum_nonneg
  rw [forall_mem_range]
  intro y
  by_cases hy : 0 ≤ f y
  · positivity
  · suffices μ (f ⁻¹' {f y}) = 0 by simp [this, measureReal_def]
    rw [← nonpos_iff_eq_zero]
    refine le_of_le_of_eq (measure_mono fun x hx ↦ ?_) (ae_iff.mp hf)
    simp only [Set.mem_preimage, mem_singleton_iff, mem_setOf_eq] at hx ⊢
    exact hx ▸ hy

lemma integral_mono {f g : α →ₛ F} (h : f ≤ᵐ[μ] g) (hf : Integrable f μ) (hg : Integrable g μ) :
    f.integral μ ≤ g.integral μ := by
  rw [← sub_nonneg, ← integral_sub hg hf]
  rw [← sub_nonneg_ae] at h
  exact integral_nonneg h

lemma integral_mono_measure {ν} {f : α →ₛ F} (hf : 0 ≤ᵐ[ν] f) (hμν : μ ≤ ν) (hfν : Integrable f ν) :
    f.integral μ ≤ f.integral ν := by
  simp only [integral_eq]
  apply Finset.sum_le_sum
  simp only [forall_mem_range]
  intro x
  by_cases hx : 0 ≤ f x
  · obtain (hx | hx) := hx.eq_or_lt
    · simp [← hx]
    simp only [measureReal_def]
    gcongr
    · exact integrable_iff.mp hfν (f x) hx.ne' |>.ne
    · exact hμν _
  · suffices ν (f ⁻¹' {f x}) = 0 by
      have A : μ (f ⁻¹' {f x}) = 0 := by simpa using (hμν _ |>.trans_eq this)
      simp [measureReal_def, A, this]
    rw [← nonpos_iff_eq_zero, ← ae_iff.mp hf]
    refine measure_mono fun y hy ↦ ?_
    simp_all

end Order

end Integral

end SimpleFunc

namespace L1

open AEEqFun Lp.simpleFunc Lp

variable [NormedAddCommGroup E] {m : MeasurableSpace α} {μ : Measure α}

namespace SimpleFunc

theorem norm_eq_integral (f : α →₁ₛ[μ] E) : ‖f‖ = ((toSimpleFunc f).map norm).integral μ := by
  rw [norm_eq_sum_mul f, (toSimpleFunc f).map_integral norm (SimpleFunc.integrable f) norm_zero]
  simp_rw [smul_eq_mul]

section PosPart

/-- Positive part of a simple function in L1 space. -/
nonrec def posPart (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ :=
  ⟨Lp.posPart (f : α →₁[μ] ℝ), by
    rcases f with ⟨f, s, hsf⟩
    use s.posPart
    simp only [SimpleFunc.posPart, SimpleFunc.coe_map, Function.comp_def, coe_posPart, ← hsf,
      posPart_mk] ⟩

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

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E] [SMulCommClass ℝ 𝕜 E]

attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module simpleFunc.normedSpace

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
  LinearMap.mkContinuous_norm_le _ zero_le_one fun f ↦ by
    simpa [one_mul] using norm_integral_le_norm f

section PosPart

theorem posPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (posPart f) =ᵐ[μ] (toSimpleFunc f).posPart := by
  have eq : ∀ a, (toSimpleFunc f).posPart a = max ((toSimpleFunc f) a) 0 := fun a => rfl
  have ae_eq : ∀ᵐ a ∂μ, toSimpleFunc (posPart f) a = max ((toSimpleFunc f) a) 0 := by
    filter_upwards [toSimpleFunc_eq_toFun (posPart f), Lp.coeFn_posPart (f : α →₁[μ] ℝ),
      toSimpleFunc_eq_toFun f] with _ _ h₂ h₃
    convert h₂ using 1
    rw [h₃]
  refine ae_eq.mono fun a h => ?_
  rw [h, eq]

theorem negPart_toSimpleFunc (f : α →₁ₛ[μ] ℝ) :
    toSimpleFunc (negPart f) =ᵐ[μ] (toSimpleFunc f).negPart := by
  rw [SimpleFunc.negPart, MeasureTheory.SimpleFunc.negPart]
  filter_upwards [posPart_toSimpleFunc (-f), neg_toSimpleFunc f]
  intro a h₁ h₂
  rw [h₁]
  change max _ _ = max _ _
  rw [h₂]
  simp

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
  · change (toSimpleFunc f).integral μ =
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

variable [NormedSpace ℝ E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [SMulCommClass ℝ 𝕜 E]
  [CompleteSpace E]

section IntegrationInL1

attribute [local instance] simpleFunc.isBoundedSMul simpleFunc.module

open ContinuousLinearMap

variable (𝕜) in
/-- The Bochner integral in L1 space as a continuous linear map. -/
nonrec def integralCLM' : (α →₁[μ] E) →L[𝕜] E :=
  (integralCLM' α E 𝕜 μ).extend (coeToLp α E 𝕜) (simpleFunc.denseRange one_ne_top)
    simpleFunc.isUniformInducing

/-- The Bochner integral in L1 space as a continuous linear map over ℝ. -/
def integralCLM : (α →₁[μ] E) →L[ℝ] E :=
  integralCLM' ℝ

/-- The Bochner integral in L1 space -/
irreducible_def integral : (α →₁[μ] E) → E :=
  integralCLM

theorem integral_eq (f : α →₁[μ] E) : integral f = integralCLM f := by
  simp only [integral]

theorem integral_eq_setToL1 (f : α →₁[μ] E) :
    integral f = setToL1 (dominatedFinMeasAdditive_weightedSMul μ) f := by
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
  change (integralCLM' 𝕜) (c • f) = c • (integralCLM' 𝕜) f
  exact map_smul (integralCLM' 𝕜) c f

theorem norm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖ ≤ 1 :=
  norm_setToL1_le (dominatedFinMeasAdditive_weightedSMul μ) zero_le_one

theorem nnnorm_Integral_le_one : ‖integralCLM (α := α) (E := E) (μ := μ)‖₊ ≤ 1 :=
  norm_Integral_le_one
-- TODO rename capitalisation ^

theorem norm_integral_le (f : α →₁[μ] E) : ‖integral f‖ ≤ ‖f‖ :=
  calc
    ‖integral f‖ = ‖integralCLM f‖ := by simp only [integral]
    _ ≤ ‖integralCLM (α := α) (μ := μ)‖ * ‖f‖ := le_opNorm _ _
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

end MeasureTheory
