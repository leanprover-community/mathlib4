/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.WithDensity

/-!
# Radon-Nikodym derivative and Lebesgue decomposition for kernels

Let `α` and `γ` be two measurable space, where either `α` is countable or `γ` is
countably generated. Let `κ, η : kernel α γ` be finite kernels.
Then there exists a function `kernel.rnDeriv κ η : α → γ → ℝ≥0∞` jointly measurable on `α × γ`
and a kernel `kernel.singularPart κ η : kernel α γ` such that
* `κ = kernel.withDensity η (kernel.rnDeriv κ η) + kernel.singularPart κ η`,
* for all `a : α`, `kernel.singularPart κ η a ⟂ₘ η a`,
* for all `a : α`, `kernel.singularPart κ η a = 0 ↔ κ a ≪ η a`,
* for all `a : α`, `kernel.withDensity η (kernel.rnDeriv κ η) a = 0 ↔ κ a ⟂ₘ η a`.

Furthermore, the sets `{a | κ a ≪ η a}` and `{a | κ a ⟂ₘ η a}` are measurable.

When `γ` is countably generated, the construction of the derivative starts from `kernel.density`:
for two finite kernels `κ' : kernel α (γ × β)` and `η' : kernel α γ` with `fst κ' ≤ η'`,
the function `density κ' η' : α → γ → Set β → ℝ` is jointly measurable in the first two arguments
and satisfies that for all `a : α` and all measurable sets `s : Set β` and `A : Set γ`,
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
everywhere unless `α` is countable (although `rnDeriv κ η` has that value almost everywhere).
See the construction of `kernel.density` for details on how the countably generated hypothesis
is used.

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

## TODO

* prove uniqueness results.
* link kernel Radon-Nikodym derivative and Radon-Nikodym derivative of measures, and similarly for
  singular parts.

-/

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.kernel

variable {α γ : Type*} {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} {κ η : kernel α γ}
  [hαγ : MeasurableSpace.CountableOrCountablyGenerated α γ]

open Classical in
/-- Auxiliary function used to define `ProbabilityTheory.kernel.rnDeriv` and
`ProbabilityTheory.kernel.singularPart`.

This has the properties we want for a Radon-Nikodym derivative only if `κ ≪ ν`. The definition of
`rnDeriv κ η` will be built from `rnDerivAux κ (κ + η)`. -/
noncomputable
def rnDerivAux (κ η : kernel α γ) (a : α) (x : γ) : ℝ :=
  if hα : Countable α then ((κ a).rnDeriv (η a) x).toReal
  else haveI := hαγ.countableOrCountablyGenerated.resolve_left hα
    density (map κ (fun a ↦ (a, ()))
      (@measurable_prod_mk_right γ Unit _ inferInstance _)) η a x univ

lemma rnDerivAux_nonneg (hκη : κ ≤ η) {a : α} {x : γ} : 0 ≤ rnDerivAux κ η a x := by
  rw [rnDerivAux]
  split_ifs with hα
  · exact ENNReal.toReal_nonneg
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_nonneg ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

lemma rnDerivAux_le_one [IsFiniteKernel η] (hκη : κ ≤ η) {a : α} :
    rnDerivAux κ η a ≤ᵐ[η a] 1 := by
  filter_upwards [Measure.rnDeriv_le_one_of_le (hκη a)] with x hx_le_one
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    simp only [Pi.one_apply, ENNReal.ofReal_one]
    exact hx_le_one
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact density_le_one ((fst_map_id_prod _ measurable_const).trans_le hκη) _ _ _

lemma measurable_rnDerivAux (κ η : kernel α γ) :
    Measurable (fun p : α × γ ↦ kernel.rnDerivAux κ η p.1 p.2) := by
  simp_rw [rnDerivAux]
  split_ifs with hα
  · refine Measurable.ennreal_toReal ?_
    change Measurable ((fun q : γ × α ↦ (κ q.2).rnDeriv (η q.2) q.1) ∘ Prod.swap)
    refine (measurable_from_prod_countable' (fun a ↦ ?_) ?_).comp measurable_swap
    · exact Measure.measurable_rnDeriv (κ a) (η a)
    · intro a a' c ha'_mem_a
      have h_eq : ∀ κ : kernel α γ, κ a' = κ a := fun κ ↦ by
        ext s hs
        exact mem_of_mem_measurableAtom ha'_mem_a
          (kernel.measurable_coe κ hs (measurableSet_singleton (κ a s))) rfl
      rw [h_eq κ, h_eq η]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    exact measurable_density _ η MeasurableSet.univ

lemma measurable_rnDerivAux_right (κ η : kernel α γ) (a : α) :
    Measurable (fun x : γ ↦ rnDerivAux κ η a x) := by
  change Measurable ((fun p : α × γ ↦ rnDerivAux κ η p.1 p.2) ∘ (fun x ↦ (a, x)))
  exact (measurable_rnDerivAux _ _).comp measurable_prod_mk_left

lemma set_lintegral_rnDerivAux (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) {s : Set γ} (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (rnDerivAux κ (κ + η) a x) ∂(κ + η) a = κ a s := by
  have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
  simp_rw [rnDerivAux]
  split_ifs with hα
  · have h_ac : κ a ≪ (κ + η) a := Measure.absolutelyContinuous_of_le (h_le a)
    rw [← Measure.set_lintegral_rnDeriv h_ac]
    refine set_lintegral_congr_fun hs ?_
    filter_upwards [Measure.rnDeriv_lt_top (κ a) ((κ + η) a)] with x hx_lt _
    rw [ENNReal.ofReal_toReal hx_lt.ne]
  · have := hαγ.countableOrCountablyGenerated.resolve_left hα
    rw [set_lintegral_density ((fst_map_id_prod _ measurable_const).trans_le h_le) _
      MeasurableSet.univ hs, map_apply' _ _ _ (hs.prod MeasurableSet.univ)]
    congr with x
    simp

lemma withDensity_rnDerivAux (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    withDensity (κ + η) (fun a x ↦ Real.toNNReal (rnDerivAux κ (κ + η) a x)) = κ := by
  ext a s hs
  rw [kernel.withDensity_apply']
  swap
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
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
    simp only [coeFn_add, Pi.add_apply, Measure.coe_add] at h
    rwa [withDensity_rnDerivAux, add_comm, ENNReal.add_right_inj (measure_ne_top _ _)] at h
  have : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  simp_rw [this, ENNReal.ofReal_sub _ (rnDerivAux_nonneg h_le), ENNReal.ofReal_one]
  rw [withDensity_sub_add_cancel]
  · rw [withDensity_one']
  · exact measurable_const
  · exact (measurable_rnDerivAux _ _).ennreal_ofReal
  · intro a
    filter_upwards [rnDerivAux_le_one h_le] with x hx
    simp only [ENNReal.ofReal_le_one]
    exact hx

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. -/
def mutuallySingularSet (κ η : kernel α γ) : Set (α × γ) := {p | 1 ≤ rnDerivAux κ (κ + η) p.1 p.2}

/-- A set of points in `α × γ` related to the absolute continuity / mutual singularity of
`κ` and `η`. That is,
* `withDensity η (rnDeriv κ η) a (mutuallySingularSetSlice κ η a) = 0`,
* `singularPart κ η a (mutuallySingularSetSlice κ η a)ᶜ = 0`.
 -/
def mutuallySingularSetSlice (κ η : kernel α γ) (a : α) : Set γ :=
  {x | 1 ≤ rnDerivAux κ (κ + η) a x}

lemma mem_mutuallySingularSetSlice (κ η : kernel α γ) (a : α) (x : γ) :
    x ∈ mutuallySingularSetSlice κ η a ↔ 1 ≤ rnDerivAux κ (κ + η) a x := by
  rw [mutuallySingularSetSlice]; rfl

lemma not_mem_mutuallySingularSetSlice (κ η : kernel α γ) (a : α) (x : γ) :
    x ∉ mutuallySingularSetSlice κ η a ↔ rnDerivAux κ (κ + η) a x < 1 := by
  simp [mutuallySingularSetSlice]

lemma measurableSet_mutuallySingularSet (κ η : kernel α γ) :
    MeasurableSet (mutuallySingularSet κ η) :=
  measurable_rnDerivAux κ (κ + η) measurableSet_Ici

lemma measurableSet_mutuallySingularSetSlice (κ η : kernel α γ) (a : α) :
    MeasurableSet (mutuallySingularSetSlice κ η a) :=
  measurable_prod_mk_left (measurableSet_mutuallySingularSet κ η)

lemma measure_mutuallySingularSetSlice (κ η : kernel α γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    (a : α) :
    η a (mutuallySingularSetSlice κ η a) = 0 := by
  have h_coe : ∀ b, (Real.toNNReal b : ℝ≥0∞) = ENNReal.ofReal b := fun _ ↦ rfl
  suffices withDensity (κ + η) (fun a x ↦ Real.toNNReal
      (1 - rnDerivAux κ (κ + η) a x)) a {x | 1 ≤ rnDerivAux κ (κ + η) a x} = 0 by
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
    mutuallySingularSet, mem_setOf_eq, and_iff_right_iff_imp]
  exact fun h ↦ zero_lt_one.trans_le h

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
    rw [not_mem_mutuallySingularSetSlice] at hx
    exact hx.ne'
  · rw [not_mem_mutuallySingularSetSlice] at hx
    simp [hx.le]
  · simp only [sub_pos]
    exact not_le.mp hx

lemma singularPart_of_subset_compl_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hs : s ⊆ (mutuallySingularSetSlice κ η a)ᶜ) :
    singularPart κ η a s = 0 :=
  measure_mono_null hs (singularPart_compl_mutuallySingularSetSlice κ η a)

lemma singularPart_of_subset_mutuallySingularSetSlice [IsFiniteKernel κ]
    [IsFiniteKernel η] {a : α} {s : Set γ} (hsm : MeasurableSet s)
    (hs : s ⊆ mutuallySingularSetSlice κ η a) :
    singularPart κ η a s = κ a s := by
  have hs' : ∀ x ∈ s, 1 ≤ rnDerivAux κ (κ + η) a x := fun _ hx ↦ hs hx
  rw [singularPart, kernel.withDensity_apply']
  swap; · exact measurable_singularPart_fun κ η
  calc
    ∫⁻ x in s, ↑(Real.toNNReal (rnDerivAux κ (κ + η) a x)) -
      ↑(Real.toNNReal (1 - rnDerivAux κ (κ + η) a x)) * rnDeriv κ η a x
      ∂(κ + η) a
    = ∫⁻ _ in s, 1 ∂(κ + η) a := by
        refine set_lintegral_congr_fun hsm ?_
        have h_le : κ ≤ κ + η := le_add_of_nonneg_right bot_le
        filter_upwards [rnDerivAux_le_one h_le] with x hx hxs
        have h_eq_one : rnDerivAux κ (κ + η) a x = 1 := le_antisymm hx (hs' x hxs)
        simp [h_eq_one]
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
  have hs' : ∀ x ∈ s, rnDerivAux κ (κ + η) a x < 1 := by
    simp_rw [← not_mem_mutuallySingularSetSlice]
    exact fun x hx hx_mem ↦ hs hx hx_mem
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
  simp only [coeFn_add, Pi.add_apply, Measure.coe_add]
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
  simp only [coeFn_add, Pi.add_apply, Measure.coe_add,
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
  simp only [coeFn_add, Pi.add_apply, Measure.coe_add,
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

end ProbabilityTheory.kernel
