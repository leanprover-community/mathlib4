/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.MeasureCompProd

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
  have h_nonneg : ∀ a x, 0 ≤ kernel.rnDerivAux κ (κ + ν) a x :=
    fun _ _ ↦ density_nonneg (kernel.fst_map_prod_le_of_le h_le) _ _ _
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (h_nonneg _ _), ENNReal.ofReal_one]
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

/-- Singular part of the kernel `κ` with respect to the kernel `ν`. -/
noncomputable
def singularPart (κ ν : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel ν] :
    kernel α γ :=
  kernel.withDensity (κ + ν) (fun a x ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) a x)
    - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) a x) * kernel.rnDeriv κ ν a x)

lemma measurable_singularPart_fun (κ ν : kernel α γ) :
    Measurable (fun p : α × γ ↦ Real.toNNReal (kernel.rnDerivAux κ (κ + ν) p.1 p.2)
      - Real.toNNReal (1 - kernel.rnDerivAux κ (κ + ν) p.1 p.2) * kernel.rnDeriv κ ν p.1 p.2) := by
  refine (measurable_rnDerivAux _ _).ennreal_ofReal.sub
    (Measurable.mul ?_ (measurable_rnDeriv _ _))
  exact (measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal

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

lemma singularPart_subset_compl_mutuallySingularSetSlice (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) (s : Set γ)
    (hs : s ⊆ (kernel.mutuallySingularSetSlice κ ν a)ᶜ) :
    kernel.singularPart κ ν a s = 0 := by
  exact measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ ν a)

lemma singularPart_subset_mutuallySingularSetSlice (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) {s : Set γ} (hsm : MeasurableSet s)
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
  swap; · exact measurable_rnDeriv κ ν
  refine le_antisymm ?_ zero_le'
  calc ∫⁻ x in kernel.mutuallySingularSetSlice κ ν a, kernel.rnDeriv κ ν a x ∂(ν a)
    ≤ ∫⁻ _ in kernel.mutuallySingularSetSlice κ ν a, ∞ ∂(ν a) :=
        set_lintegral_mono (measurable_rnDeriv_right κ ν a) measurable_const (fun _ _ ↦ le_top)
  _ = ∞ * ν a (kernel.mutuallySingularSetSlice κ ν a) := by simp
  _ = 0 := by
        simp only [mul_eq_zero, ENNReal.top_ne_zero, false_or]
        exact measure_mutuallySingularSetSlice κ ν a

lemma withDensity_rnDeriv_subset_mutuallySingularSetSlice (κ ν : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel ν] (a : α) (s : Set γ)
    (hs : s ⊆ kernel.mutuallySingularSetSlice κ ν a) :
    kernel.withDensity ν (kernel.rnDeriv κ ν) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ ν a)

lemma withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) {s : Set γ} (hsm : MeasurableSet s)
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

lemma mutuallySingular_singularPart (κ ν : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
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
  rw [singularPart_subset_mutuallySingularSetSlice _ _ _ (hs.inter hm) (inter_subset_right _ _),
    singularPart_subset_compl_mutuallySingularSetSlice _ _ _ _ (diff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_subset_mutuallySingularSetSlice _ _ _ _ (inter_subset_right _ _),
    zero_add, withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice _ _ _ (hs.diff hm)
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

-- ok
lemma Measure.absolutelyContinuous_compProd_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : kernel α γ) [IsSFiniteKernel κ]  :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (measurable_kernel_prod_mk_left hs)]
    at hs_zero ⊢
  exact hμν.ae_eq hs_zero

-- ok
lemma Measure.absolutelyContinuous_compProd_right (μ : Measure α) {κ η : kernel α γ}
    [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (measurable_kernel_prod_mk_left hs)]
    at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

-- ok
lemma Measure.absolutelyContinuous_compProd {μ ν : Measure α} {κ η : kernel α γ}
    [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  (Measure.absolutelyContinuous_compProd_left hμν κ).trans
    (Measure.absolutelyContinuous_compProd_right ν hκη)

lemma Measure.mutuallySingular_compProd_left {μ ν : Measure α} [SFinite μ] [SFinite ν]
    (hμν : μ ⟂ₘ ν) (κ η : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  let s := hμν.nullSet
  have hs_prod : MeasurableSet (s ×ˢ (univ : Set γ)) :=
    hμν.measurableSet_nullSet.prod MeasurableSet.univ
  refine ⟨s ×ˢ univ, hs_prod, ?_⟩
  rw [Measure.compProd_apply_prod hμν.measurableSet_nullSet MeasurableSet.univ, compl_prod_eq_union]
  simp only [Measure.MutuallySingular.restrict_nullSet, lintegral_zero_measure, compl_univ,
    prod_empty, union_empty, true_and]
  rw [Measure.compProd_apply_prod hμν.measurableSet_nullSet.compl MeasurableSet.univ]
  simp

lemma Measure.mutuallySingular_compProd_right (μ ν : Measure α) [SFinite μ] [SFinite ν]
    {κ η : kernel α γ} [IsFiniteKernel κ] [IsFiniteKernel η] (hκη : ∀ a, κ a ⟂ₘ η a) :
    μ ⊗ₘ κ ⟂ₘ ν ⊗ₘ η := by
  let s := mutuallySingularSet κ η
  have hs : MeasurableSet s := measurableSet_mutuallySingularSet κ η
  symm
  refine ⟨s, hs, ?_⟩
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs.compl]
  have h1 : ∀ a, η a (Prod.mk a ⁻¹' s) = 0 := by
    intro a
    have : Prod.mk a ⁻¹' s = mutuallySingularSetSlice κ η a := rfl
    rw [this, measure_mutuallySingularSetSlice]
  have h2 : ∀ a, κ a (Prod.mk a ⁻¹' s)ᶜ = 0 := by
    intro a
    have : (Prod.mk a ⁻¹' s)ᶜ ⊆ Prod.mk a ⁻¹' sᶜ := by intro; simp
    refine measure_mono_null this ?_
    have : Prod.mk a ⁻¹' sᶜ = (mutuallySingularSetSlice κ η a)ᶜ := rfl
    rw [this, ← withDensity_rnDeriv_eq_zero_iff_measure_eq_zero κ η a,
      withDensity_rnDeriv_eq_zero_iff_mutuallySingular]
    exact hκη a
  simp [h1, h2]

lemma Measure.fst_map_compProd (μ : Measure α) [SFinite μ] (κ : kernel α γ)
    [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).map Prod.fst = μ := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.compProd_apply]
  swap; · exact measurable_fst hs
  have : ∀ a, (κ a) (Prod.mk a ⁻¹' (Prod.fst ⁻¹' s)) = s.indicator (fun a ↦ κ a univ) a := by
    intro a
    classical
    rw [indicator_apply]
    split_ifs with ha
    · congr with x
      simp [ha]
    · suffices Prod.mk a ⁻¹' (Prod.fst ⁻¹' s) = ∅ by rw [this]; simp
      ext x
      simp [ha]
  simp_rw [this]
  rw [lintegral_indicator _ hs]
  simp

lemma ae_compProd_of_ae_fst {μ : Measure α} (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {p : α → Prop} (hp : MeasurableSet {x | p x})
    (h : ∀ᵐ a ∂μ, p a) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x.1 := by
  refine ae_compProd_of_ae_ae (measurable_fst hp) ?_
  filter_upwards [h] with a ha
  simp [ha]

lemma ae_eq_compProd_of_ae_eq_fst {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → β}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun hf hg) h

lemma ae_eq_compProd_of_forall_ae_eq {β : Type*} {_ : MeasurableSpace β} [AddGroup β]
    [MeasurableSingletonClass β] [MeasurableSub₂ β]
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → γ → β}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

lemma ENNReal.ae_eq_compProd_of_ae_eq_fst (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    (fun p ↦ f p.1) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1) :=
  ae_compProd_of_ae_fst κ (measurableSet_eq_fun' hf hg) h

lemma ENNReal.ae_eq_compProd_of_forall_ae_eq
    (μ : Measure α) (κ : kernel α γ)
    [SFinite μ] [IsSFiniteKernel κ] {f g : α → γ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g))
    (h : ∀ a, f a =ᵐ[κ a] g a) :
    (fun p ↦ f p.1 p.2) =ᵐ[μ ⊗ₘ κ] (fun p ↦ g p.1 p.2) :=
  ae_compProd_of_ae_ae (measurableSet_eq_fun' hf hg)
    (ae_of_all _ (fun a ↦ measure_mono_null (fun x ↦ by simp) (h a)))

section Unique

variable {ξ : kernel α γ} {f : α → γ → ℝ≥0∞}

lemma eq_rnDeriv_measure [IsFiniteKernel ν] (h : κ = kernel.withDensity ν f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ ν a) (a : α) :
    f a =ᵐ[ν a] ∂(κ a)/∂(ν a) := by
  have : κ a = ξ a + (ν a).withDensity (f a) := by
    rw [h, coeFn_add, Pi.add_apply, kernel.withDensity_apply _ hf, add_comm]
  exact (κ a).eq_rnDeriv₀ (hf.comp measurable_prod_mk_left).aemeasurable (hξ a) this

lemma eq_singularPart_measure [IsFiniteKernel κ] [IsFiniteKernel ν]
    (h : κ = kernel.withDensity ν f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ ν a) (a : α) :
    ξ a = (κ a).singularPart (ν a) := by
  have : κ a = ξ a + (ν a).withDensity (f a) := by
    rw [h, coeFn_add, Pi.add_apply, kernel.withDensity_apply _ hf, add_comm]
  exact (κ a).eq_singularPart (hf.comp measurable_prod_mk_left) (hξ a) this

lemma rnDeriv_eq_rnDeriv_measure (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv κ ν a =ᵐ[ν a] ∂(κ a)/∂(ν a) :=
  eq_rnDeriv_measure (rnDeriv_add_singularPart κ ν).symm (measurable_rnDeriv κ ν)
    (mutuallySingular_singularPart κ ν) a

lemma singularPart_eq_singularPart_measure [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    singularPart κ ν a = (κ a).singularPart (ν a) :=
  eq_singularPart_measure (rnDeriv_add_singularPart κ ν).symm (measurable_rnDeriv κ ν)
    (mutuallySingular_singularPart κ ν) a

lemma eq_rnDeriv [IsFiniteKernel κ] [IsFiniteKernel ν] (h : κ = kernel.withDensity ν f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ ν a) (a : α) :
    f a =ᵐ[ν a] rnDeriv κ ν a :=
  (eq_rnDeriv_measure h hf hξ a).trans (rnDeriv_eq_rnDeriv_measure _ _ a).symm

lemma eq_singularPart [IsFiniteKernel κ] [IsFiniteKernel ν] (h : κ = kernel.withDensity ν f + ξ)
    (hf : Measurable (Function.uncurry f)) (hξ : ∀ a, ξ a ⟂ₘ ν a) (a : α) :
    ξ a = singularPart κ ν a :=
  (eq_singularPart_measure h hf hξ a).trans (singularPart_eq_singularPart_measure a).symm

end Unique

section MeasureCompProd

lemma set_lintegral_prod_rnDeriv {μ ν : Measure α} {κ η : kernel α γ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a)
    {s : Set α} (hs : MeasurableSet s) {t : Set γ} (ht : MeasurableSet t) :
    ∫⁻ x in s, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x) ∂ν = (μ ⊗ₘ κ) (s ×ˢ t) := by
  have : ∀ᵐ x ∂ν, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
      = (∂μ/∂ν) x * κ x t := by
    filter_upwards [hκη] with x hx
    calc ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x)
      = (∂μ/∂ν) x * ∫⁻ y in t, rnDeriv κ η x y ∂(η x) := by
          rw [lintegral_const_mul]
          exact measurable_rnDeriv_right κ η x
    _ = (∂μ/∂ν) x * ∫⁻ y in t, (∂(κ x)/∂(η x)) y ∂(η x) := by
          congr 1
          refine lintegral_congr_ae (ae_restrict_of_ae ?_)
          exact rnDeriv_eq_rnDeriv_measure _ _ x
    _ = (∂μ/∂ν) x * κ x t := by
          congr
          rw [Measure.set_lintegral_rnDeriv hx]
  rw [lintegral_congr_ae (ae_restrict_of_ae this),
    set_lintegral_rnDeriv_mul hμν (kernel.measurable_coe _ ht).aemeasurable hs,
    Measure.compProd_apply_prod hs ht]

lemma rnDeriv_measure_compProd_aux {μ ν : Measure α} {κ η : kernel α γ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂ν, κ a ≪ η a) :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  have h_meas : Measurable fun p : α × γ ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 :=
    ((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul (measurable_rnDeriv _ _)
  suffices ∀ s, MeasurableSet s → ∫⁻ p in s, (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p ∂(ν ⊗ₘ η)
      = ∫⁻ p in s, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂(ν ⊗ₘ η) from
    ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite (Measure.measurable_rnDeriv _ _) h_meas
      fun s hs _ ↦ this s hs
  have h_left : ∀ s, MeasurableSet s → ∫⁻ p in s, (∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η)) p ∂(ν ⊗ₘ η)
      = (μ ⊗ₘ κ) s := by
    intro s _
    rw [Measure.set_lintegral_rnDeriv]
    exact Measure.absolutelyContinuous_compProd hμν hκη
  have : ∀ s t, MeasurableSet s → MeasurableSet t →
      ∫⁻ x in s, ∫⁻ y in t, (∂μ/∂ν) x * rnDeriv κ η x y ∂(η x) ∂ν = (μ ⊗ₘ κ) (s ×ˢ t) :=
    fun _ _ hs ht ↦ set_lintegral_prod_rnDeriv hμν hκη hs ht
  intro s hs
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp
  · rintro _ ⟨t₁, ht₁, t₂, ht₂, rfl⟩
    simp only [mem_setOf_eq] at ht₁ ht₂
    rw [h_left (t₁ ×ˢ t₂) (ht₁.prod ht₂), Measure.set_lintegral_compProd h_meas ht₁ ht₂,
      this t₁ t₂ ht₁ ht₂]
  · intro t ht ht_eq
    calc ∫⁻ p in tᶜ, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η
      = ∫⁻ p, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η - ∫⁻ p in t, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η := by
          refine (ENNReal.sub_eq_of_add_eq ?_ ?_).symm
          · rw [h_left _ ht]
            exact measure_ne_top _ _
          · rw [add_comm, lintegral_add_compl _ ht]
    _ = ∫⁻ p, (∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p ∂ν ⊗ₘ η
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by rw [ht_eq]
    _ = (μ ⊗ₘ κ) univ
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          have h := h_left univ MeasurableSet.univ
          rw [set_lintegral_univ] at h
          rw [h]
    _ = ∫⁻ x, ∫⁻ y, (∂μ/∂ν) x * rnDeriv κ η x y ∂η x ∂ν
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          have h := this univ univ MeasurableSet.univ MeasurableSet.univ
          simp only [Measure.restrict_univ, univ_prod_univ] at h
          rw [← h]
    _ = ∫⁻ p, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η
        - ∫⁻ p in t, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          congr
          rw [Measure.lintegral_compProd h_meas]
    _ = ∫⁻ p in tᶜ, (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 ∂ν ⊗ₘ η := by
          refine ENNReal.sub_eq_of_add_eq ?_ ?_
          · rw [← ht_eq, h_left _ ht]
            exact measure_ne_top _ _
          rw [add_comm, lintegral_add_compl _ ht]
  · intro f' hf_disj hf_meas hf_eq
    rw [lintegral_iUnion hf_meas hf_disj, lintegral_iUnion hf_meas hf_disj]
    congr with i
    exact hf_eq i

instance instIsFiniteKernel_withDensity_rnDeriv [hκ : IsFiniteKernel κ] [IsFiniteKernel ν] :
    IsFiniteKernel (withDensity ν (rnDeriv κ ν)) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  rw [kernel.withDensity_apply', set_lintegral_univ]
  swap; · exact measurable_rnDeriv κ ν
  rw [lintegral_congr_ae (rnDeriv_eq_rnDeriv_measure _ _ a), ← set_lintegral_univ]
  exact (Measure.set_lintegral_rnDeriv_le _).trans (measure_le_bound _ _ _)

instance instIsFiniteKernel_singularPart [hκ : IsFiniteKernel κ] [IsFiniteKernel ν] :
    IsFiniteKernel (singularPart κ ν) := by
  constructor
  refine ⟨hκ.bound, hκ.bound_lt_top, fun a ↦ ?_⟩
  have h : withDensity ν (rnDeriv κ ν) a univ + singularPart κ ν a univ = κ a univ := by
    conv_rhs => rw [← rnDeriv_add_singularPart κ ν]
  exact (self_le_add_left _ _).trans (h.le.trans (measure_le_bound _ _ _))

lemma rnDeriv_add (κ ν η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] [IsFiniteKernel η]
    (a : α) :
    rnDeriv (κ + ν) η a =ᵐ[η a] rnDeriv κ η a + rnDeriv ν η a := by
  filter_upwards [rnDeriv_eq_rnDeriv_measure (κ + ν) η a, rnDeriv_eq_rnDeriv_measure κ η a,
    rnDeriv_eq_rnDeriv_measure ν η a, Measure.rnDeriv_add (κ a) (ν a) (η a)] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, h3, coeFn_add, Pi.add_apply, h4, Pi.add_apply]

lemma rnDeriv_singularPart (κ ν : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel ν] (a : α) :
    rnDeriv (singularPart κ ν) ν a =ᵐ[ν a] 0 := by
  filter_upwards [rnDeriv_eq_rnDeriv_measure (singularPart κ ν) ν a,
    (Measure.rnDeriv_eq_zero _ _).mpr (mutuallySingular_singularPart κ ν a)] with x h1 h2
  rw [h1, h2]

lemma rnDeriv_measure_compProd (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  have h1 : μ = μ' + μ.singularPart ν := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have h2 : κ = κ' + singularPart κ η := by
    conv_lhs => rw [← rnDeriv_add_singularPart κ η]
  have h3 : μ ⊗ₘ κ = μ' ⊗ₘ κ' + (μ.singularPart ν) ⊗ₘ κ + μ' ⊗ₘ (singularPart κ η) := by
    conv_lhs => rw [h1, Measure.compProd_add_left]
    conv_lhs => conv in μ' ⊗ₘ κ => rw [h2]
    rw [Measure.compProd_add_right, add_assoc, add_comm (μ' ⊗ₘ singularPart κ η), ← add_assoc]
  have h_left : ∂(μ' ⊗ₘ κ')/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
    rw [h3]
    have h_add := Measure.rnDeriv_add (μ' ⊗ₘ κ' + μ.singularPart ν ⊗ₘ κ)
      (μ' ⊗ₘ (singularPart κ η)) (ν ⊗ₘ η)
    have h_add' := Measure.rnDeriv_add (μ' ⊗ₘ κ') (μ.singularPart ν ⊗ₘ κ) (ν ⊗ₘ η)
    have h01 : ∂(μ.singularPart ν ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
      rw [Measure.rnDeriv_eq_zero]
      exact Measure.mutuallySingular_compProd_left (Measure.mutuallySingular_singularPart _ _) κ η
    have h02 : ∂(μ' ⊗ₘ (singularPart κ η))/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] 0 := by
      rw [Measure.rnDeriv_eq_zero]
      exact Measure.mutuallySingular_compProd_right μ' ν (mutuallySingular_singularPart _ _)
    filter_upwards [h_add, h_add', h01, h02] with a h_add h_add' h01 h02
    rw [h_add, Pi.add_apply, h_add', Pi.add_apply, h01, h02]
    simp
  have h_right : (fun p ↦ (∂μ'/∂ν) p.1 * rnDeriv κ' η p.1 p.2)
      =ᵐ[ν ⊗ₘ η] (fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2) := by
    refine EventuallyEq.mul ?_ ?_
    · have h := Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)
      rw [EventuallyEq, ae_iff] at h ⊢
      exact ENNReal.ae_eq_compProd_of_ae_eq_fst ν η (Measure.measurable_rnDeriv μ' ν)
        (Measure.measurable_rnDeriv μ ν) h
    · have : ∀ a, rnDeriv κ' η a =ᵐ[η a] rnDeriv κ η a := by
        intro a
        rw [h2]
        filter_upwards [rnDeriv_add κ' (singularPart κ η) η a,
          rnDeriv_singularPart κ η a] with x hx1 hx2
        rw [hx1, Pi.add_apply, hx2, Pi.zero_apply, add_zero]
      exact ENNReal.ae_eq_compProd_of_forall_ae_eq _ _ (measurable_rnDeriv κ' η)
        (measurable_rnDeriv κ η) this
  refine h_left.symm.trans (EventuallyEq.trans ?_ h_right)
  refine rnDeriv_measure_compProd_aux ?_ ?_
  · exact MeasureTheory.withDensity_absolutelyContinuous _ _
  · exact ae_of_all _ (fun _ ↦ withDensity_absolutelyContinuous _ _)

lemma rnDeriv_self (κ : kernel α γ) [IsFiniteKernel κ] (a : α) :
    rnDeriv κ κ a =ᵐ[κ a] 1 :=
  (rnDeriv_eq_rnDeriv_measure κ κ a).trans (Measure.rnDeriv_self _)

lemma rnDeriv_measure_compProd_left (μ ν : Measure α) (κ : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ κ) =ᵐ[ν ⊗ₘ κ] fun p ↦ (∂μ/∂ν) p.1 := by
  have h : (fun p ↦ rnDeriv κ κ p.1 p.2) =ᵐ[ν ⊗ₘ κ] (fun p ↦ (1 : α → γ → ℝ≥0∞) p.1 p.2) :=
    ENNReal.ae_eq_compProd_of_forall_ae_eq ν κ (measurable_rnDeriv _ _) measurable_const
      (rnDeriv_self κ)
  filter_upwards [rnDeriv_measure_compProd μ ν κ κ, h] with p hp1 hp2
  rw [hp1, hp2]
  simp

lemma rnDeriv_measure_compProd_right (μ : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η] fun p ↦ rnDeriv κ η p.1 p.2 := by
  have h : (fun p ↦ (∂μ/∂μ) p.1) =ᵐ[μ ⊗ₘ η] (fun p ↦ (1 : α → ℝ≥0∞) p.1) :=
    ENNReal.ae_eq_compProd_of_ae_eq_fst μ η (Measure.measurable_rnDeriv _ _)
      measurable_const (Measure.rnDeriv_self _)
  filter_upwards [rnDeriv_measure_compProd μ μ κ η, h] with p hp1 hp2
  rw [hp1, hp2]
  simp

end MeasureCompProd

end ProbabilityTheory.kernel
