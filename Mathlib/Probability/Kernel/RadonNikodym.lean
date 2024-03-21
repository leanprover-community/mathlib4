/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `γ` be a countably generated measurable space and `κ η : kernel α γ` be finite kernels.
Then there exists a function `kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `kernel.singularPart κ η : kernel α γ` such that
* `κ = kernel.withDensity η (kernel.rnDeriv κ η) + kernel.singularPart κ η`,
* for all `a : α`, `kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `kernel.withDensity η (kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

## Main definitions

* `ProbabilityTheory.kernel.rnDeriv`: a function `α → γ → ℝ≥0∞` jointly measurable on `α × γ`
* `ProbabilityTheory.kernel.singularPart`: a `kernel α γ`

## Main statements

* `ProbabilityTheory.kernel.mutuallySingular_singularPart`: for all `a : α`,
  `kernel.singularPart κ η a ⟂ₘ η a`
* `ProbabilityTheory.kernel.rnDeriv_add_singularPart`:
  `kernel.withDensity η (kernel.rnDeriv κ η) + kernel.singularPart κ η = κ`
* `ProbabilityTheory.kernel.measurableSet_absolutelyContinuous` : the set `{a | κ a ≪ η a}`
  is Measurable
* `ProbabilityTheory.kernel.measurableSet_mutuallySingular` : the set `{a | κ a ⟂ₘ η a}`
  is Measurable

## References

Theorem 1.28 in [O. Kallenberg, Random Measures, Theory and Applications][kallenberg2017].

-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ}
  [MeasurableSpace.CountablyGenerated γ] {κ η : kernel α γ}

lemma fst_map_prod_le_of_le (hκη : κ ≤ η) :
    kernel.fst (kernel.map κ (fun a ↦ (a, ()))
      (@measurable_prod_mk_right γ Unit _ inferInstance _)) ≤ η := by
  rwa [kernel.fst_map_prod _ measurable_id' measurable_const, kernel.map_id']

/-- Auxiliary function used to define `ProbabilityTheory.kernel.rnDeriv` and
`ProbabilityTheory.kernel.singularPart`. -/
noncomputable
def rnDerivAux (κ η : kernel α γ) (a : α) (x : γ) : ℝ :=
  density (map κ (fun a ↦ (a, ()))
    (@measurable_prod_mk_right γ Unit _ inferInstance _)) η a x univ

lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x :=
  density_nonneg (fst_map_prod_le_of_le hκη) _ _ _

lemma rnDerivAux_le_one (hκη : κ ≤ η) {a : α} {x : γ} : rnDerivAux κ η a x ≤ 1 :=
  density_le_one (fst_map_prod_le_of_le hκη) _ _ _

lemma measurable_rnDerivAux (κ η : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDerivAux κ η p.1 p.2) :=
  measurable_density _ η MeasurableSet.univ

lemma measurable_rnDerivAux_right (κ η : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDerivAux κ η a x) := by
  change Measurable ((fun p : α × γ ↦ rnDerivAux κ η p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDerivAux _ _).comp measurable_prod_mk_left

lemma set_lintegral_rnDerivAux (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  rw [set_lintegral_density (fst_map_prod_le_of_le h_le) _ MeasurableSet.univ hs,
    map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
  congr with x
  simp

lemma withDensity_rnDerivAux (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)) = κ := by
  ext a s hs
  rw [kernel.withDensity_apply']
  swap; exact (measurable_rnDerivAux _ _).ennreal_ofReal
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this]
  exact set_lintegral_rnDerivAux κ η a hs

lemma withDensity_one_sub_rnDerivAux (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) = η := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
      + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))
      = κ + η by
    ext a s
    have h : (withDensity (κ + η) (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))
          + withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x))) a s
        = κ a s + η a s := by
      rw [this]
      simp
    simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add]
      at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · refine fun a ↦ ae_of_all _ (fun x ↦ ?_)
    simp only [ENNReal.ofReal_le_one]
    exact density_le_one (fst_map_prod_le_of_le h_le) _ _ _

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. -/
def mutuallySingularSet (κ η : kernel α γ) : Set (α × γ) := {p | rnDerivAux κ (κ + η) p.1 p.2 = 1}

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. That is,
* `kernel.withDensity η (kernel.rnDeriv κ η) a (kernel.mutuallySingularSetSlice κ η a) = 0`,
* `kernel.singularPart κ η a (kernel.mutuallySingularSetSlice κ η a)ᶜ = 0`.
 -/
def mutuallySingularSetSlice (κ η : kernel α γ) (a : α) : Set γ :=
  {x | rnDerivAux κ (κ + η) a x = 1}

lemma measurableSet_mutuallySingularSet (κ η : kernel α γ) :
    MeasurableSet (mutuallySingularSet κ η) :=
  measurable_rnDerivAux κ (κ + η) (measurableSet_singleton 1)

lemma measurableSet_mutuallySingularSetSlice (κ η : kernel α γ) (a : α) :
    MeasurableSet (mutuallySingularSetSlice κ η a) :=
  measurable_prod_mk_left (measurableSet_mutuallySingularSet κ η)

lemma measure_mutuallySingularSetSlice (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    η a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | rnDerivAux κ (κ + η) a x = 1} = 0 by
    rwa [withDensity_one_sub_rnDerivAux κ η] at this
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

/-- Radon-Nikodym derivative of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
def rnDeriv (κ η : kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
    / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)

lemma rnDeriv_def (κ η : kernel α γ) :
    rnDeriv κ η = fun a x ↦ ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
      / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x) := rfl

lemma measurable_rnDeriv (κ η : kernel α γ) :
    Measurable (fun p : α × γ ↦ rnDeriv κ η p.1 p.2) :=
  (measurable_rnDerivAux κ _).ennreal_ofReal.div
    (measurable_const.sub (measurable_rnDerivAux κ _)).ennreal_ofReal

lemma measurable_rnDeriv_right (κ η : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDeriv κ η a x) := by
  change Measurable ((fun p : α × γ ↦ rnDeriv κ η p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDeriv _ _).comp measurable_prod_mk_left

lemma rnDeriv_eq_top_iff (κ η : kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ (a, x) ∈ mutuallySingularSet κ η := by
  simp only [rnDeriv, ENNReal.div_eq_top, ne_eq, ENNReal.ofReal_eq_zero, not_le,
    tsub_le_iff_right, zero_add, ENNReal.ofReal_ne_top, not_false_eq_true, and_true, or_false,
    mutuallySingularSet, mem_setOf_eq]
  exact ⟨fun h ↦ le_antisymm (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) h.2,
    fun h ↦ by simp [h]⟩

lemma rnDeriv_eq_top_iff' (κ η : kernel α γ) (a : α) (x : γ) :
    rnDeriv κ η a x = ∞ ↔ x ∈ mutuallySingularSetSlice κ η a := by
  rw [rnDeriv_eq_top_iff]
  rfl

/-- Singular part of the kernel `κ` with respect to the kernel `η`. -/
noncomputable
def singularPart (κ η : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    kernel α γ :=
  withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
    - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x)

lemma measurable_singularPart_fun (κ η : kernel α γ) :
    Measurable (fun p : α × γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) p.1 p.2)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) p.1 p.2) * rnDeriv κ η p.1 p.2) :=
  (measurable_rnDerivAux _ _).ennreal_ofReal.sub
    ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul (measurable_rnDeriv _ _))

lemma measurable_singularPart_fun_right (κ η : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)
      - Real.toNNReal (1 - rnDerivAux κ (κ + η) a x) * rnDeriv κ η a x) := by
  change Measurable ((Function.uncurry fun a b ↦
    ENNReal.ofReal (rnDerivAux κ (κ + η) a b)
    - ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a b) * rnDeriv κ η a b) ∘ (fun b ↦ (a, b)))
  exact (measurable_singularPart_fun κ η).comp measurable_prod_mk_left

lemma singularPart_compl_mutuallySingularSetSlice (κ η : kernel α γ) [IsSFiniteKernel κ]
    [IsSFiniteKernel η] (a : α) :
    singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  rw [singularPart, kernel.withDensity_apply', lintegral_eq_zero_iff, EventuallyEq,
    ae_restrict_iff]
  all_goals simp_rw [h_coe]
  rotate_left
  · exact measurableSet_preimage (measurable_singularPart_fun_right κ η a)
      (measurableSet_singleton _)
  · exact measurable_singularPart_fun_right κ η a
  · exact measurable_singularPart_fun κ η
  refine ae_of_all _ (fun x hx ↦ ?_)
  simp only [mem_compl_iff, mem_setOf_eq] at hx
  simp_rw [rnDeriv]
  rw [← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
    mul_inv_cancel, one_mul, tsub_self]
  · rfl
  · rw [ne_eq, sub_eq_zero]
    exact Ne.symm hx
  · simp [rnDerivAux_le_one (le_add_of_nonneg_right bot_le)]
  · simp [lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) hx]

lemma singularPart_subset_compl_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 := by
  exact measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

lemma singularPart_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    singularPart κ η a s = κ a s := by
  have hs' : ∀ x ∈ s, rnDerivAux κ (κ + η) a x = 1 := fun _ hx ↦ hs hx
  rw [singularPart, kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine set_lintegral_congr_fun hsm (ae_of_all _ fun x hx ↦ ?_)
        simp [hs' x hx]
  _ = (κ + η) a s := by simp
  _ = κ a s := by
        suffices η a s = 0 by simp [this]
        exact measure_mono_null hs (measure_mutuallySingularSetSlice κ η a)

lemma withDensity_rnDeriv_mutuallySingularSetSlice (κ η : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [kernel.withDensity_apply']
  · exact set_lintegral_measure_zero _ _ (measure_mutuallySingularSetSlice κ η a)
  · exact measurable_rnDeriv κ η

lemma withDensity_rnDeriv_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    withDensity η (rnDeriv κ η) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)

lemma withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    withDensity η (rnDeriv κ η) a s = κ a s := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def]
    congr
    exact (withDensity_one_sub_rnDerivAux κ η).symm
  rw [this, ← withDensity_mul, kernel.withDensity_apply']
  rotate_left
  · exact ((measurable_const.sub (measurable_rnDerivAux _ _)).ennreal_ofReal.mul
    (measurable_rnDeriv _ _))
  · exact (measurable_const.sub (measurable_rnDerivAux _ _)).real_toNNReal
  · exact measurable_rnDeriv _ _
  simp_rw [rnDeriv]
  have hs' : ∀ x ∈ s, rnDerivAux κ (κ + η) a x < 1 :=
    fun x hx ↦ lt_of_le_of_ne (rnDerivAux_le_one (le_add_of_nonneg_right bot_le)) (hs hx)
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) *
      (ENNReal.ofReal (rnDerivAux κ (κ + η) a x) /
        ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)) ∂(κ + η) a
  _ = ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a := by
      refine set_lintegral_congr_fun hsm (ae_of_all _ fun x hx ↦ ?_)
      rw [h_coe, ← ENNReal.ofReal_div_of_pos, div_eq_inv_mul, ← ENNReal.ofReal_mul, ← mul_assoc,
        mul_inv_cancel, one_mul]
      · rw [ne_eq, sub_eq_zero]
        exact (hs' x hx).ne'
      · simp [(hs' x hx).le]
      · simp [hs' x hx]
  _ = κ a s := set_lintegral_rnDerivAux κ η a hsm

lemma mutuallySingular_singularPart (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    singularPart κ η a ⟂ₘ η a := by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

/-- Lebesgue decomposition of a finite kernel `κ` with respect to another one `η`. -/
lemma rnDeriv_add_singularPart (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity η (rnDeriv κ η) + singularPart κ η = κ := by
  ext a s hs
  rw [← inter_union_diff s (mutuallySingularSetSlice κ η a)]
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure,
    OuterMeasure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono (inter_subset_right _ _) subset_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_subset_mutuallySingularSetSlice (hs.inter hm) (inter_subset_right _ _),
    singularPart_subset_compl_mutuallySingularSetSlice (diff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_subset_mutuallySingularSetSlice (inter_subset_right _ _),
    zero_add, withDensity_rnDeriv_subset_compl_mutuallySingularSetSlice (hs.diff hm)
      (diff_subset_iff.mpr (by simp)), add_comm]

lemma singularPart_eq_zero_iff_apply_eq_zero (κ η : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ singularPart κ η a (mutuallySingularSetSlice κ η a) = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    singularPart_compl_mutuallySingularSetSlice, add_zero]

lemma withDensity_rnDeriv_eq_zero_iff_apply_eq_zero (κ η : kernel α γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0
      ↔ withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  rw [← Measure.measure_univ_eq_zero]
  have : univ = (mutuallySingularSetSlice κ η a) ∪ (mutuallySingularSetSlice κ η a)ᶜ := by simp
  rw [this, measure_union disjoint_compl_right (measurableSet_mutuallySingularSetSlice κ η a).compl,
    withDensity_rnDeriv_mutuallySingularSetSlice, zero_add]

lemma singularPart_eq_zero_iff_absolutelyContinuous (κ η : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a ≪ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η]
  simp only [coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [singularPart_eq_zero_iff_apply_eq_zero]
  specialize h (measure_mutuallySingularSetSlice κ η a)
  simpa only [Measure.add_toOuterMeasure, OuterMeasure.coe_add, Pi.add_apply,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] using h

lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η]
  simp only [coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  simp only [Measure.MutuallySingular.add_left_iff] at h
  have h_ac := withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a
  have h_ms := h.1
  rw [← Measure.MutuallySingular.self_iff]
  exact h_ms.mono_ac Measure.AbsolutelyContinuous.rfl h_ac

lemma singularPart_eq_zero_iff_measure_eq_zero (κ η : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    singularPart κ η a = 0 ↔ κ a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)
    (measurableSet_mutuallySingularSetSlice κ η a)
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add,
    withDensity_rnDeriv_mutuallySingularSetSlice κ η, zero_add] at h_eq_add
  rw [← h_eq_add]
  exact singularPart_eq_zero_iff_apply_eq_zero κ η a

lemma withDensity_rnDeriv_eq_zero_iff_measure_eq_zero (κ η : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a (mutuallySingularSetSlice κ η a)ᶜ = 0 := by
  have h_eq_add := rnDeriv_add_singularPart κ η
  simp_rw [ext_iff, Measure.ext_iff] at h_eq_add
  specialize h_eq_add a (mutuallySingularSetSlice κ η a)ᶜ
    (measurableSet_mutuallySingularSetSlice κ η a).compl
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure, OuterMeasure.coe_add,
    singularPart_compl_mutuallySingularSetSlice κ η, add_zero] at h_eq_add
  rw [← h_eq_add]
  exact withDensity_rnDeriv_eq_zero_iff_apply_eq_zero κ η a

lemma measurableSet_absolutelyContinuous (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≪ η a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

lemma measurableSet_mutuallySingular (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ⟂ₘ η a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η).compl
    (measurableSet_singleton 0)

end ProbabilityTheory.kernel
