/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `γ` be a countably generated measurable space and `κ ν : kernel α γ` be finite kernels.
Then there exists a function `kernel.rnDeriv κ ν : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `kernel.singularPart κ ν : kernel α γ` such that
* `κ = kernel.withDensity ν (kernel.rnDeriv κ ν) + kernel.singularPart κ ν`,
* for all `a : α`, `kernel.singularPart κ ν a ⟂ₘ ν a`,
* for all `a : α`, `kernel.singularPart κ ν a = 0 ↔ κ a ≪ ν a`,
* for all `a : α`, `kernel.withDensity ν (kernel.rnDeriv κ ν) a = 0 ↔ κ a ⟂ₘ ν a`.

Furthermore, the sets `{a | κ a ≪ ν a}` and `{a | κ a ⟂ₘ ν a}` are measurable.

## Main definitions

* `ProbabilityTheory.kernel.rnDeriv`: a function `α → γ → ℝ≥0∞` jointly measurable on `α × γ`
* `ProbabilityTheory.kernel.singularPart`: a `kernel α γ`

## Main statements

* `ProbabilityTheory.kernel.mutuallySingular_singularPart`: for all `a : α`,
  `kernel.singularPart κ ν a ⟂ₘ ν a`
* `ProbabilityTheory.kernel.rnDeriv_add_singularPart`:
  `kernel.withDensity ν (kernel.rnDeriv κ ν) + kernel.singularPart κ ν = κ`
* `ProbabilityTheory.kernel.measurableSet_absolutelyContinuous` : the set `{a | κ a ≪ ν a}`
  is Measurable
* `ProbabilityTheory.kernel.measurableSet_mutuallySingular` : the set `{a | κ a ⟂ₘ ν a}`
  is Measurable

## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  [MeasurableSpace.CountablyGenerated γ] {κ ν : kernel α γ}

lemma fst_map_prod_le_of_le (hκν : κ ≤ ν) :
    kernel.fst (kernel.map κ (fun a ↦ (a, ()))
      (@measurable_prod_mk_right γ Unit _ inferInstance _)) ≤ ν := by
  rwa [kernel.fst_map_prod _ measurable_id' measurable_const, kernel.map_id']

/-- Auxiliary function used to define `ProbabilityTheory.kernel.rnDeriv` and
`ProbabilityTheory.kernel.singularPart`. -/
noncomputable
def rnDerivAux (κ ν : kernel α γ) (a : α) (x : γ) : ℝ :=
  kernel.density (kernel.map κ (fun a ↦ (a, ()))
    (@measurable_prod_mk_right γ Unit _ inferInstance _)) ν a x univ

lemma rnDerivAux_nonneg (hκν : κ ≤ ν) {a : α} {x : γ} : 0 ≤ kernel.rnDerivAux κ ν a x :=
  density_nonneg (kernel.fst_map_prod_le_of_le hκν) _ _ _

lemma rnDerivAux_le_one (hκν : κ ≤ ν) {a : α} {x : γ} : kernel.rnDerivAux κ ν a x ≤ 1 :=
  density_le_one (kernel.fst_map_prod_le_of_le hκν) _ _ _

lemma measurable_rnDerivAux (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDerivAux κ ν p.1 p.2) :=
  measurable_density _ ν MeasurableSet.univ

lemma measurable_rnDerivAux_right (κ ν : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ kernel.rnDerivAux κ ν a x) := by
  change Measurable ((fun p : α × γ ↦ kernel.rnDerivAux κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDerivAux _ _).comp measurable_prod_mk_left

lemma set_lintegral_rnDerivAux (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x) ∂(κ + ν) a = κ a s := by
  have h_le : κ ≤ κ + ν := le_add_of_nonneg_right bot_le
  simp_rw [kernel.rnDerivAux]
  rw [set_lintegral_density (kernel.fst_map_prod_le_of_le h_le) _ MeasurableSet.univ hs,
    kernel.map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
  congr with x
  simp

lemma withDensity_rnDerivAux (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν)
      (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)) = κ := by
  ext a s hs
  rw [kernel.withDensity_apply']
  swap; exact (measurable_rnDerivAux _ _).ennreal_ofReal
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this]
  exact set_lintegral_rnDerivAux κ ν a hs

lemma withDensity_one_sub_rnDerivAux (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity (κ + ν)
      (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x)) = ν := by
  have h_le : κ ≤ κ + ν := le_add_of_nonneg_right bot_le
  suffices kernel.withDensity (κ + ν)
        (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))
      + kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x))
      = κ + ν by
    ext a s
    have h : (kernel.withDensity (κ + ν)
          (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))
        + kernel.withDensity (κ + ν)
          (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x))) a s
        = κ a s + ν a s := by
      rw [this]
      simp
    simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
      at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [kernel.withDensity_sub_add_cancel]
  · rw [kernel.withDensity_one']
  · exact measurable_const
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · refine fun a ↦ ae_of_all _ (fun x ↦ ?_)
    simp only [ENNReal.ofReal_le_one]
    exact density_le_one (kernel.fst_map_prod_le_of_le h_le) _ _ _

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `ν`. -/
def mutuallySingularSet (κ ν : kernel α γ) : Set (α × γ) :=
  {p | kernel.rnDerivAux κ (κ + ν) p.1 p.2 = 1}

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `ν`. That is,
* `kernel.withDensity ν (kernel.rnDeriv κ ν) a (kernel.mutuallySingularSetSlice κ ν a) = 0`,
* `kernel.singularPart κ ν a (kernel.mutuallySingularSetSlice κ ν a)ᶜ = 0`.
 -/
def mutuallySingularSetSlice (κ ν : kernel α γ) (a : α) : Set γ :=
  {x | kernel.rnDerivAux κ (κ + ν) a x = 1}

lemma measurableSet_mutuallySingularSet (κ ν : kernel α γ) :
    MeasurableSet (kernel.mutuallySingularSet κ ν) :=
  measurable_rnDerivAux κ (κ + ν) (measurableSet_singleton 1)

lemma measurableSet_mutuallySingularSetSlice (κ ν : kernel α γ) (a : α) :
    MeasurableSet (kernel.mutuallySingularSetSlice κ ν a) :=
  measurable_prod_mk_left (measurableSet_mutuallySingularSet κ ν)

lemma measure_mutuallySingularSetSlice (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    ν a (kernel.mutuallySingularSetSlice κ ν a) = 0 := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  suffices kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal
      (1 - kernel.rnDerivAux κ (κ + ν) a x)) a {x | kernel.rnDerivAux κ (κ + ν) a x = 1} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ ν] at this
  simp_rw [h_coe]
  rw [kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq, ae_restrict_iff]
  rotate_left
  · exact (measurable_const.sub
      ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
      (measurableSet_singleton _)
  · exact (measurable_const.sub
      ((measurable_rnDerivAux _ _).comp measurable_prod_mk_left)).ennreal_ofReal
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_setOf_eq] at hx
  simp [hx]

/-- Radon-Nikodym derivative of the kernel `κ` with respect to the kernel `ν`. -/
noncomputable
def rnDeriv (κ ν : kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x)
    / ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x)

lemma rnDeriv_def (κ ν : kernel α γ) :
    kernel.rnDeriv κ ν = fun a x ↦ ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x)
      / ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x) := rfl

lemma measurable_rnDeriv (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDeriv κ ν p.1 p.2) :=
  (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

lemma measurable_rnDeriv_right (κ ν : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ kernel.rnDeriv κ ν a x) := by
  change Measurable ((fun p : α × γ ↦ kernel.rnDeriv κ ν p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDeriv _ _).comp measurable_prod_mk_left

lemma rnDeriv_eq_top_iff (κ ν : kernel α γ) (a : α) (x : γ) :
    kernel.rnDeriv κ ν a x = ∞ ↔ (a, x) ∈ kernel.mutuallySingularSet κ ν := by
  simp only [kernel.rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    kernel.mutuallySingularSet, mem_setOf_eq]
  exact ⟨fun h ↦ le_antisymm (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) h.2,
    fun h ↦ by simp [h]⟩

lemma rnDeriv_eq_top_iff' (κ ν : kernel α γ) (a : α) (x : γ) :
    kernel.rnDeriv κ ν a x = ∞ ↔ x ∈ kernel.mutuallySingularSetSlice κ ν a := by
  rw [rnDeriv_eq_top_iff]
  rfl

/-- Singular part of the kernel `κ` with respect to the kernel `ν`. -/
noncomputable
def singularPart (κ ν : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel ν] :
    kernel α γ :=
  kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)
    - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x)

lemma measurable_singularPart_fun (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) p.1 p.2)
      - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) p.1 p.2) * kernel.rnDeriv κ ν p.1 p.2) :=
  (measurable_rnDerivAux _ _).ennreal_ofReal.sub
    ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul (measurable_rnDeriv _ _))

lemma measurable_singularPart_fun_right (κ ν : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)
      - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x) := by
  change Measurable ((Function.uncurry fun a b ↦
    ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a b)
    - ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a b) * kernel.rnDeriv κ ν a b)
    ∘ (fun b ↦ (a, b)))
  exact (measurable_singularPart_fun κ ν).comp measurable_prod_mk_left

lemma singularPart_compl_mutuallySingularSetSlice (κ ν : kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel ν] (a : α) :
    kernel.singularPart κ ν a (kernel.mutuallySingularSetSlice κ ν a)ᶜ = 0 := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  rw [kernel.singularPart, kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
    ae_restrict_iff]
  all_goals simp_rw [h_coe]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ ν a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ ν a
  · exact measurable_singularPart_fun κ ν
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_compl_iff, mem_setOf_eq] at hx
  simp_rw [kernel.rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
    mul_inv_cancel, one_mul, tsub_self]
  · rfl
  · rw [ne_eq, sub_eq_zero]
    exact Ne.symm hx
  · simp [rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
  · simp [lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) hx]

lemma singularPart_subset_compl_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel ν] {a : α} {s : Set γ}
    (hs : s ⊆ (kernel.mutuallySingularSetSlice κ ν a)ᶜ) :
    kernel.singularPart κ ν a s = 0 := by
  exact measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ ν a)

lemma singularPart_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel ν] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ kernel.mutuallySingularSetSlice κ ν a) :
    kernel.singularPart κ ν a s = κ a s := by
  have hs' : ∀ x ∈ s, kernel.rnDerivAux κ (κ + ν) a x = 1 := fun _ hx ↦ hs hx
  rw [kernel.singularPart, kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ ν
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)) -
      ↑(Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x)) * kernel.rnDeriv κ ν a x
      ∂(κ + ν) a
    = ∫⁻ _ in s, 1 ∂(κ + ν) a := by
        refine set_lintegral_congr_fun hsm (ae_of_all _ fun x hx ↦ ?_)
        simp [hs' x hx]
  _ = (κ + ν) a s := by simp
  _ = κ a s := by
        suffices ν a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ ν a)

lemma withDensity_rnDeriv_mutuallySingularSetSlice (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a (kernel.mutuallySingularSetSlice κ ν a) = 0 := by
  rw [kernel.withDensity_apply']
  · exact set_lintegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ ν a)
  · exact measurable_rnDeriv κ ν

lemma withDensity_rnDeriv_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel ν] {a : α} {s : Set γ}
    (hs : s ⊆ kernel.mutuallySingularSetSlice κ ν a) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ ν a)

lemma withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel ν] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ (kernel.mutuallySingularSetSlice κ ν a)ᶜ) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a s = κ a s := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  have : kernel.withDensity ν (kernel.rnDeriv κ ν)
      = kernel.withDensity (kernel.withDensity (κ + ν)
        (fun a x ↦ Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x))) (kernel.rnDeriv κ ν) := by
    rw [kernel.rnDeriv_def]
    congr
    exact (withDensity_one_sub_rnDerivAux κ ν).symm
  rw [this, ← kernel.withDensity_mul, kernel.withDensity_apply']
  rotate_left
  · exact ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul
    (measurable_rnDeriv _ _))
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).real_toNNReal
  · exact measurable_rnDeriv _ _
  simp_rw [kernel.rnDeriv]
  have hs' : ∀ x ∈ s, kernel.rnDerivAux κ (κ + ν) a x < 1 :=
    fun x hx ↦ lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) (hs hx)
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x)) *
      (ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x) /
        ENNReal.ofReal (1 - kernel.rnDerivAux κ (κ + ν) a x)) ∂(κ + ν) a
  _ = ∫⁻ x in s, ENNReal.ofReal (kernel.rnDerivAux κ (κ + ν) a x) ∂(κ + ν) a := by
      refine set_lintegral_congr_fun hsm (ae_of_all _ fun x hx ↦ ?_)
      rw [h_coe, ← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
        mul_inv_cancel, one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := set_lintegral_rnDerivAux κ ν a hsm

lemma mutuallySingular_singularPart (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν]
    (a : α) :
    kernel.singularPart κ ν a ⟂ₘ ν a := by
  symm
  exact ⟨mutuallySingularSetSlice κ ν a, measurableSet_mutuallySingularSetSlice κ ν a,
    measure_mutuallySingularSetSlice κ ν a, singularPart_compl_mutuallySingularSetSlice κ ν a⟩

lemma rnDeriv_add_singularPart (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    kernel.withDensity ν (kernel.rnDeriv κ ν) + kernel.singularPart κ ν = κ := by
  ext a s hs
  rw [← inter_union_diff s (mutuallySingularSetSlice κ ν a)]
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure,
    OuterMeasure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ ν a
  simp only [measure_union (Disjoint.mono (inter_subset_right _ _) subset_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_subset_mutuallySingularSetSlice (hs.inter hm) (inter_subset_right _ _),
    singularPart_subset_compl_mutuallySingularSetSlice (diff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_subset_mutuallySingularSetSlice (inter_subset_right _ _),
    zero_add, withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (diff_subset_iff.mpr (by simp)), add_comm]

lemma singularPart_eq_zero_iff_apply_eq_zero (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    kernel.singularPart κ ν a = 0
      ↔ kernel.singularPart κ ν a (kernel.mutuallySingularSetSlice κ ν a) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (kernel.mutuallySingularSetSlice κ ν a)
      ∪ (kernel.mutuallySingularSetSlice κ ν a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ ν a).compl,
    singularPart_compl_mutuallySingularSetSlice, add_zero]

lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a = 0
      ↔ kernel.withDensity ν (kernel.rnDeriv κ ν) a
        (kernel.mutuallySingularSetSlice κ ν a)ᶜ = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (kernel.mutuallySingularSetSlice κ ν a)
      ∪ (kernel.mutuallySingularSetSlice κ ν a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ ν a).compl,
    withDensity_rnDeriv_mutuallySingularSetSlice, zero_add]

lemma singularPart_eq_zero_iff_absolutelyContinuous (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.singularPart κ ν a = 0 ↔ κ a ≪ ν a := by
  conv_rhs => rw [← kernel.rnDeriv_add_singularPart κ ν]
  simp only [kernel.coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero]
    exact kernel.withDensity_absolutelyContinuous _ _
  rw [singularPart_eq_zero_iff_apply_eq_zero]
  specialize h (measure_mutuallySingularSetSlice κ ν a)
  simpa only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
    withDensity_rnDeriv_mutuallySingularSetSlice κ ν, zero_add] using h

lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a = 0 ↔ κ a ⟂ₘ ν a := by
  conv_rhs => rw [← kernel.rnDeriv_add_singularPart κ ν]
  simp only [kernel.coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, zero_add]
    exact kernel.mutuallySingular_singularPart _ _ _
  simp only [Measure.MutuallySingular.add_left_iff] at h
  have h_ac := kernel.withDensity_absolutelyContinuous (κ := ν) (kernel.rnDeriv κ ν) a
  have h_ms := h.1
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

lemma singularPart_eq_zero_iff_measure_eq_zero (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.singularPart κ ν a = 0 ↔ κ a (kernel.mutuallySingularSetSlice κ ν a) = 0 := by
  have h_eq_add := kernel.rnDeriv_add_singularPart κ ν
  simp_rw [kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (kernel.mutuallySingularSetSlice κ ν a)
    (measurableSet_mutuallySingularSetSlice κ ν a)
  simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ ν, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ ν a

lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a = 0
      ↔ κ a (kernel.mutuallySingularSetSlice κ ν a)ᶜ = 0 := by
  have h_eq_add := kernel.rnDeriv_add_singularPart κ ν
  simp_rw [kernel.ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (kernel.mutuallySingularSetSlice κ ν a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ ν a).compl
  simp only [kernel.coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ ν, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ ν a

lemma measurableSet_absolutelyContinuous (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    MeasurableSet {a | κ a ≪ ν a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact kernel.measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ ν)
    (measurableSet_singleton 0)

lemma measurableSet_mutuallySingular (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] :
    MeasurableSet {a | κ a ⟂ₘ ν a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact kernel.measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ ν).compl
    (measurableSet_singleton 0)

end ProbabilityTheory.kernel
