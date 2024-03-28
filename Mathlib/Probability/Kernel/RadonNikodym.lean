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

Let `γ` be a countably generated measurable space and `κ, η : kernel α γ` be finite kernels.
Then there exists a function `kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `kernel.singularPart κ η : kernel α γ` such that
* `κ = kernel.withDensity η (kernel.rnDeriv κ η) + kernel.singularPart κ η`,
* for all `a : α`, `kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `kernel.withDensity η (kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

The construction of the derivative starts from `kernel.density`: for two finite kernels
`κ' : kernel α (γ × β)` and `η' : kernel α γ` with `fst κ' ≤ η'`, the function
`density κ' η' : α → γ → Set β → ℝ` is jointly measurable in the first two arguments and satisfies
that for all `a : α` and all measurable sets `s : Set β` and `A : Set γ`,
`∫ x in A, density κ' η' a x s ∂(η' a) = (κ' a (A ×ˢ s)).toReal`.
We use that definition for `β = Unit` and `κ' = map κ (fun a ↦ (a, ()))`. We can't choose `η' = η`
in general because we might not have `κ ≤ η`, but if we could, we would get a measurable function
`f` with the property `κ = withDensity η f`, which is the decomposition we want for `κ ≤ η`.
To circumvent that difficulty, we take `η' = κ + η` and thus define `rnDerivAux κ η`.
Finally, `rnDeriv κ η a x` is given by
`ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)`.
Up to some conversions between `ℝ` and `ℝ≥0`, the singular part is
`withDensity (κ + η) (rnDerivAux κ (κ + η) - (1 - rnDerivAux κ (κ + η)) * rnDeriv κ η)`.

The countably generated measurable space assumption is not needed to have a decomposition for
measures, but the additional difficulty with kernels is to obtain joint measurability of the
derivative. This is why we can't simply define `rnDeriv κ η` by `a ↦ (κ a).rnDeriv (ν a)`
everywhere (although `rnDeriv κ η` has that value almost everywhere). See the construction of
`kernel.density` for details on how the countably generated hypothesis is used.

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

/-- Auxiliary function used to define `ProbabilityTheory.kernel.rnDeriv` and
`ProbabilityTheory.kernel.singularPart`.

This has the properties we want for a Radon-Nikodym derivative only if `κ ≪ ν`. The definition of
`rnDeriv κ η` will be built from `rnDerivAux κ (κ + η)`. -/
noncomputable
def rnDerivAux (κ η : kernel α γ) (a : α) (x : γ) : ℝ :=
  density (map κ (fun a ↦ (a, ()))
    (@measurable_prod_mk_right γ Unit _ inferInstance _)) η a x univ

lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x :=
  density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

lemma rnDerivAux_le_one (hκη : κ ≤ η) {a : α} {x : γ} : rnDerivAux κ η a x ≤ 1 :=
  density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

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
  rw [set_lintegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
    MeasurableSet.univ hs, map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
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
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le h_le) _ _ _

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. -/
def mutuallySingularSet (κ η : kernel α γ) : Set (α × γ) := {p | rnDerivAux κ (κ + η) p.1 p.2 = 1}

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. That is,
* `withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0`,
* `singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0`.
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
irreducible_def rnDeriv (κ η : kernel α γ) (a : α) (x : γ) : ℝ≥0∞ :=
  ENNReal.ofReal (rnDerivAux κ (κ + η) a x) / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x)

lemma rnDeriv_def' (κ η : kernel α γ) :
    rnDeriv κ η = fun a x ↦ ENNReal.ofReal (rnDerivAux κ (κ + η) a x)
      / ENNReal.ofReal (1 - rnDerivAux κ (κ + η) a x) := by ext; rw [rnDeriv_def]

lemma measurable_rnDeriv (κ η : kernel α γ) :
    Measurable (fun p : α × γ ↦ rnDeriv κ η p.1 p.2) := by
  simp_rw [rnDeriv_def]
  exact (measurable_rnDerivAux κ _).ennreal_ofReal.div
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
irreducible_def singularPart (κ η : kernel α γ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
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

lemma singularPart_of_subset_compl_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 :=
  measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

lemma singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
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

lemma withDensity_rnDeriv_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ}
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    withDensity η (rnDeriv κ η) a s = 0 :=
  measure_mono_null hs (withDensity_rnDeriv_mutuallySingularSetSlice κ η a)

lemma withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice
    [IsFiniteKernel κ] [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    withDensity η (rnDeriv κ η) a s = κ a s := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  have : withDensity η (rnDeriv κ η)
      = withDensity (withDensity (κ + η)
        (fun a x ↦ Real.toNNReal (1 - rnDerivAux κ (κ + η) a x))) (rnDeriv κ η) := by
    rw [rnDeriv_def']
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

/-- The singular part of `κ` with respect to `η` is mutually singular with `η`. -/
lemma mutuallySingular_singularPart (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    singularPart κ η a ⟂ₘ η a := by
  symm
  exact ⟨mutuallySingularSetSlice κ η a, measurableSet_mutuallySingularSetSlice κ η a,
    measure_mutuallySingularSetSlice κ η a, singularPart_compl_mutuallySingularSetSlice κ η a⟩

/-- Lebesgue decomposition of a finite kernel `κ` with respect to another one `η`.
`κ` is the sum of an abolutely continuous part `withDensity η (rnDeriv κ η)` and a singular part
`singularPart κ η`. -/
lemma rnDeriv_add_singularPart (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity η (rnDeriv κ η) + singularPart κ η = κ := by
  ext a s hs
  rw [← inter_union_diff s (mutuallySingularSetSlice κ η a)]
  simp only [coeFn_add, Pi.add_apply, Measure.add_toOuterMeasure,
    OuterMeasure.coe_add]
  have hm := measurableSet_mutuallySingularSetSlice κ η a
  simp only [measure_union (Disjoint.mono (inter_subset_right _ _) subset_rfl disjoint_sdiff_right)
    (hs.diff hm)]
  rw [singularPart_of_subset_mutuallySingularSetSlice (hs.inter hm) (inter_subset_right _ _),
    singularPart_of_subset_compl_mutuallySingularSetSlice (diff_subset_iff.mpr (by simp)),
    add_zero, withDensity_rnDeriv_of_subset_mutuallySingularSetSlice (inter_subset_right _ _),
    zero_add, withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice (hs.diff hm)
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
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero]
    exact withDensity_absolutelyContinuous _ _
  rw [Measure.AbsolutelyContinuous.add_left_iff] at h
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h.2
    (mutuallySingular_singularPart _ _ _)

lemma withDensity_rnDeriv_eq_zero_iff_mutuallySingular (κ η : kernel α γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) :
    withDensity η (rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a := by
  conv_rhs => rw [← rnDeriv_add_singularPart κ η, coeFn_add, Pi.add_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, zero_add]
    exact mutuallySingular_singularPart _ _ _
  rw [Measure.MutuallySingular.add_left_iff] at h
  rw [← Measure.MutuallySingular.self_iff]
  exact h.1.mono_ac Measure.AbsolutelyContinuous.rfl
    (withDensity_absolutelyContinuous (κ := η) (rnDeriv κ η) a)

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

/-- The set of points `a : α` such that `κ a ≪ η a` is measurable. -/
@[measurability]
lemma measurableSet_absolutelyContinuous (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ≪ η a} := by
  simp_rw [← singularPart_eq_zero_iff_absolutelyContinuous,
    singularPart_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η)
    (measurableSet_singleton 0)

/-- The set of points `a : α` such that `κ a ⟂ₘ η a` is measurable. -/
@[measurability]
lemma measurableSet_mutuallySingular (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a ⟂ₘ η a} := by
  simp_rw [← withDensity_rnDeriv_eq_zero_iff_mutuallySingular,
    withDensity_rnDeriv_eq_zero_iff_measure_eq_zero]
  exact measurable_kernel_prod_mk_left (measurableSet_mutuallySingularSet κ η).compl
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

lemma todo1 (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(ν.withDensity (∂μ/∂ν) ⊗ₘ withDensity η (rnDeriv κ η))/∂(ν ⊗ₘ η)
      =ᵐ[ν ⊗ₘ η] ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  have h1 : μ = μ' + μ.singularPart ν := by
    conv_lhs => rw [μ.haveLebesgueDecomposition_add ν, add_comm]
  have h2 : μ ⊗ₘ κ = μ' ⊗ₘ κ' + (μ.singularPart ν) ⊗ₘ κ + μ' ⊗ₘ (singularPart κ η) := by
    conv_lhs => rw [h1, Measure.compProd_add_left]
    conv_lhs => conv in μ' ⊗ₘ κ => rw [← rnDeriv_add_singularPart κ η]
    rw [Measure.compProd_add_right, add_assoc, add_comm (μ' ⊗ₘ singularPart κ η), ← add_assoc]
  rw [h2]
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

lemma todo2 (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    (fun p ↦ (∂(ν.withDensity (∂μ/∂ν))/∂ν) p.1 * rnDeriv (withDensity η (rnDeriv κ η)) η p.1 p.2)
      =ᵐ[ν ⊗ₘ η] (fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2) := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  refine EventuallyEq.mul ?_ ?_
  · have h := Measure.rnDeriv_withDensity ν (Measure.measurable_rnDeriv μ ν)
    rw [EventuallyEq, ae_iff] at h ⊢
    exact ENNReal.ae_eq_compProd_of_ae_eq_fst ν η (Measure.measurable_rnDeriv μ' ν)
      (Measure.measurable_rnDeriv μ ν) h
  · have : ∀ a, rnDeriv κ' η a =ᵐ[η a] rnDeriv κ η a := by
      intro a
      rw [← rnDeriv_add_singularPart κ η]
      filter_upwards [rnDeriv_add κ' (singularPart κ η) η a,
        rnDeriv_singularPart κ η a] with x hx1 hx2
      rw [hx1, Pi.add_apply, hx2, Pi.zero_apply, add_zero]
    exact ENNReal.ae_eq_compProd_of_forall_ae_eq _ _ (measurable_rnDeriv κ' η)
      (measurable_rnDeriv κ η) this

lemma rnDeriv_measure_compProd (μ ν : Measure α) (κ η : kernel α γ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteKernel κ] [IsFiniteKernel η] :
    ∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ/∂ν) p.1 * rnDeriv κ η p.1 p.2 := by
  let μ' := ν.withDensity (∂μ/∂ν)
  let κ' := withDensity η (rnDeriv κ η)
  suffices ∂(μ' ⊗ₘ κ')/∂(ν ⊗ₘ η) =ᵐ[ν ⊗ₘ η] fun p ↦ (∂μ'/∂ν) p.1 * rnDeriv κ' η p.1 p.2 from
    (todo1 μ ν κ η).symm.trans (this.trans (todo2 μ ν κ η))
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
