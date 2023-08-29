/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.CondCdf
import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.Probability.Kernel.IntegralCompProd

#align_import probability.kernel.disintegration from "leanprover-community/mathlib"@"6315581f5650ffa2fbdbbbedc41243c8d7070981"

/-!
# Disintegration of measures on product spaces

Let `ρ` be a finite measure on `α × Ω`, where `Ω` is a standard Borel space. In mathlib terms, `Ω`
verifies `[Nonempty Ω] [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]`.
Then there exists a kernel `ρ.condKernel : kernel α Ω` such that for any measurable set
`s : Set (α × Ω)`, `ρ s = ∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst`.

In terms of kernels, `ρ.condKernel` is such that for any measurable space `γ`, we
have a disintegration of the constant kernel from `γ` with value `ρ`:
`kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prodMkLeft γ (condKernel ρ))`,
where `ρ.fst` is the marginal measure of `ρ` on `α`. In particular,
`ρ = ((kernel.const Unit ρ.fst) ⊗ₖ (kernel.prodMkLeft Unit (condKernel ρ))) ()`.

In order to obtain a disintegration for any standard Borel space, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`. In the real case,
we define a conditional kernel by taking for each `a : α` the measure associated to the Stieltjes
function `condCdf ρ a` (the conditional cumulative distribution function).

## Main definitions

* `MeasureTheory.Measure.condKernel ρ : kernel α Ω`: conditional kernel described above.

## Main statements

* `ProbabilityTheory.lintegral_condKernel`:
  `∫⁻ a, ∫⁻ ω, f (a, ω) ∂(ρ.condKernel a) ∂ρ.fst = ∫⁻ x, f x ∂ρ`
* `ProbabilityTheory.lintegral_condKernel_mem`:
  `∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s`
* `ProbabilityTheory.kernel.const_eq_compProd`:
  `kernel.const γ ρ = (kernel.const γ ρ.fst) ⊗ₖ (kernel.prodMkLeft γ ρ.condKernel)`
* `ProbabilityTheory.measure_eq_compProd`:
  `ρ = ((kernel.const Unit ρ.fst) ⊗ₖ (kernel.prodMkLeft Unit ρ.condKernel)) ()`

-/


open MeasureTheory Set Filter

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α}

section Real

/-! ### Disintegration of measures on `α × ℝ` -/


/-- Conditional measure on the second space of the product given the value on the first, as a
kernel. Use the more general `condKernel`. -/
noncomputable def condKernelReal (ρ : Measure (α × ℝ)) : kernel α ℝ where
  val a := (condCdf ρ a).measure
  property := measurable_measure_condCdf ρ
#align probability_theory.cond_kernel_real ProbabilityTheory.condKernelReal

instance (ρ : Measure (α × ℝ)) : IsMarkovKernel (condKernelReal ρ) :=
  ⟨fun a => by rw [condKernelReal]; exact instIsProbabilityMeasure ρ a⟩
               -- ⊢ IsProbabilityMeasure (↑{ val := fun a => StieltjesFunction.measure (condCdf  …
                                    -- 🎉 no goals

theorem condKernelReal_Iic (ρ : Measure (α × ℝ)) (a : α) (x : ℝ) :
    condKernelReal ρ a (Iic x) = ENNReal.ofReal (condCdf ρ a x) :=
  measure_condCdf_Iic ρ a x
#align probability_theory.cond_kernel_real_Iic ProbabilityTheory.condKernelReal_Iic

theorem set_lintegral_condKernelReal_Iic (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ)
    {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, condKernelReal ρ a (Iic x) ∂ρ.fst = ρ (s ×ˢ Iic x) := by
  simp_rw [condKernelReal_Iic]; exact set_lintegral_condCdf ρ x hs
  -- ⊢ ∫⁻ (a : α) in s, ENNReal.ofReal (↑(condCdf ρ a) x) ∂Measure.fst ρ = ↑↑ρ (s × …
                                -- 🎉 no goals
#align probability_theory.set_lintegral_cond_kernel_real_Iic ProbabilityTheory.set_lintegral_condKernelReal_Iic

theorem set_lintegral_condKernelReal_univ (ρ : Measure (α × ℝ)) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, condKernelReal ρ a univ ∂ρ.fst = ρ (s ×ˢ univ) := by
  simp only [measure_univ, lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter,
    one_mul, Measure.fst_apply hs, ← prod_univ]
#align probability_theory.set_lintegral_cond_kernel_real_univ ProbabilityTheory.set_lintegral_condKernelReal_univ

theorem lintegral_condKernelReal_univ (ρ : Measure (α × ℝ)) :
    ∫⁻ a, condKernelReal ρ a univ ∂ρ.fst = ρ univ := by
  rw [← set_lintegral_univ, set_lintegral_condKernelReal_univ ρ MeasurableSet.univ,
    univ_prod_univ]
#align probability_theory.lintegral_cond_kernel_real_univ ProbabilityTheory.lintegral_condKernelReal_univ

variable (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]

theorem set_lintegral_condKernelReal_prod {s : Set α} (hs : MeasurableSet s) {t : Set ℝ}
    (ht : MeasurableSet t) : ∫⁻ a in s, condKernelReal ρ a t ∂ρ.fst = ρ (s ×ˢ t) := by
  -- `set_lintegral_condKernelReal_Iic` gives the result for `t = Iic x`. These sets form a
  -- π-system that generates the Borel σ-algebra, hence we can get the same equality for any
  -- measurable set `t`.
  apply MeasurableSpace.induction_on_inter (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic _ _ _ _ ht
  · simp only [measure_empty, lintegral_const, zero_mul, prod_empty]
    -- 🎉 no goals
  · rintro t ⟨q, rfl⟩
    -- ⊢ ∫⁻ (a : α) in s, ↑↑(↑(condKernelReal ρ) a) (Iic q) ∂Measure.fst ρ = ↑↑ρ (s × …
    exact set_lintegral_condKernelReal_Iic ρ q hs
    -- 🎉 no goals
  · intro t ht ht_lintegral
    -- ⊢ ∫⁻ (a : α) in s, ↑↑(↑(condKernelReal ρ) a) tᶜ ∂Measure.fst ρ = ↑↑ρ (s ×ˢ tᶜ)
    calc
      ∫⁻ a in s, condKernelReal ρ a tᶜ ∂ρ.fst =
          ∫⁻ a in s, condKernelReal ρ a univ - condKernelReal ρ a t ∂ρ.fst := by
        congr with a; rw [measure_compl ht (measure_ne_top (condKernelReal ρ a) _)]
      _ = ∫⁻ a in s, condKernelReal ρ a univ ∂ρ.fst - ∫⁻ a in s, condKernelReal ρ a t ∂ρ.fst := by
        rw [lintegral_sub (kernel.measurable_coe (condKernelReal ρ) ht)]
        · rw [ht_lintegral]
          exact measure_ne_top ρ _
        · exact eventually_of_forall fun a => measure_mono (subset_univ _)
      _ = ρ (s ×ˢ univ) - ρ (s ×ˢ t) := by
        rw [set_lintegral_condKernelReal_univ ρ hs, ht_lintegral]
      _ = ρ (s ×ˢ tᶜ) := by
        rw [← measure_diff _ (hs.prod ht) (measure_ne_top ρ _)]
        · rw [prod_diff_prod, compl_eq_univ_diff]
          simp only [diff_self, empty_prod, union_empty]
        · rw [prod_subset_prod_iff]
          exact Or.inl ⟨subset_rfl, subset_univ t⟩
  · intro f hf_disj hf_meas hf_eq
    -- ⊢ ∫⁻ (a : α) in s, ↑↑(↑(condKernelReal ρ) a) (⋃ (i : ℕ), f i) ∂Measure.fst ρ = …
    simp_rw [measure_iUnion hf_disj hf_meas]
    -- ⊢ ∫⁻ (a : α) in s, ∑' (i : ℕ), ↑↑(↑(condKernelReal ρ) a) (f i) ∂Measure.fst ρ  …
    rw [lintegral_tsum fun i => (kernel.measurable_coe _ (hf_meas i)).aemeasurable.restrict,
      prod_iUnion, measure_iUnion]
    · simp_rw [hf_eq]
      -- 🎉 no goals
    · intro i j hij
      -- ⊢ (Disjoint on fun i => s ×ˢ f i) i j
      rw [Function.onFun, disjoint_prod]
      -- ⊢ Disjoint s s ∨ Disjoint (f i) (f j)
      exact Or.inr (hf_disj hij)
      -- 🎉 no goals
    · exact fun i => MeasurableSet.prod hs (hf_meas i)
      -- 🎉 no goals
#align probability_theory.set_lintegral_cond_kernel_real_prod ProbabilityTheory.set_lintegral_condKernelReal_prod

theorem lintegral_condKernelReal_mem {s : Set (α × ℝ)} (hs : MeasurableSet s) :
    ∫⁻ a, condKernelReal ρ a {x | (a, x) ∈ s} ∂ρ.fst = ρ s := by
  -- `set_lintegral_condKernelReal_prod` gives the result for sets of the form `t₁ × t₂`. These
  -- sets form a π-system that generates the product σ-algebra, hence we can get the same equality
  -- for any measurable set `s`.
  apply MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod _ _ _ _ hs
  · simp only [mem_empty_iff_false, setOf_false, measure_empty, lintegral_const,
      zero_mul]
  · intro t ht
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ t} ∂Measure.fst ρ = ↑↑ρ t
    rw [mem_image2] at ht
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ t} ∂Measure.fst ρ = ↑↑ρ t
    obtain ⟨t₁, t₂, ht₁, ht₂, rfl⟩ := ht
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ t₁ ×ˢ t₂} ∂Measure.fst ρ …
    have h_prod_eq_snd : ∀ a ∈ t₁, {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = t₂ := by
      intro a ha
      simp only [ha, prod_mk_mem_set_prod_eq, true_and_iff, setOf_mem_eq]
    cases' eq_empty_or_nonempty t₂ with h h
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ t₁ ×ˢ t₂} ∂Measure.fst ρ …
    · simp only [h, prod_empty, mem_empty_iff_false, setOf_false, measure_empty, lintegral_const,
        zero_mul]
    rw [← lintegral_add_compl _ ht₁]
    -- ⊢ ∫⁻ (x : α) in t₁, ↑↑(↑(condKernelReal ρ) x) {x_1 | (x, x_1) ∈ t₁ ×ˢ t₂} ∂Mea …
    have h_eq1 : ∫⁻ a in t₁, condKernelReal ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst =
        ∫⁻ a in t₁, condKernelReal ρ a t₂ ∂ρ.fst := by
      refine' set_lintegral_congr_fun ht₁ (eventually_of_forall fun a ha => _)
      rw [h_prod_eq_snd a ha]
    have h_eq2 : ∫⁻ a in t₁ᶜ, condKernelReal ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} ∂ρ.fst = 0 := by
      suffices h_eq_zero : ∀ a ∈ t₁ᶜ, condKernelReal ρ a {x : ℝ | (a, x) ∈ t₁ ×ˢ t₂} = 0
      · rw [set_lintegral_congr_fun ht₁.compl (eventually_of_forall h_eq_zero)]
        simp only [lintegral_const, zero_mul]
      intro a hat₁
      rw [mem_compl_iff] at hat₁
      simp only [hat₁, prod_mk_mem_set_prod_eq, false_and_iff, setOf_false, measure_empty]
    rw [h_eq1, h_eq2, add_zero]
    -- ⊢ ∫⁻ (a : α) in t₁, ↑↑(↑(condKernelReal ρ) a) t₂ ∂Measure.fst ρ = ↑↑ρ (t₁ ×ˢ t₂)
    exact set_lintegral_condKernelReal_prod ρ ht₁ ht₂
    -- 🎉 no goals
  · intro t ht ht_eq
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ tᶜ} ∂Measure.fst ρ = ↑↑ρ …
    calc
      ∫⁻ a, condKernelReal ρ a {x : ℝ | (a, x) ∈ tᶜ} ∂ρ.fst =
          ∫⁻ a, condKernelReal ρ a {x : ℝ | (a, x) ∈ t}ᶜ ∂ρ.fst := rfl
      _ = ∫⁻ a, condKernelReal ρ a univ - condKernelReal ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst := by
        congr with a : 1
        exact measure_compl (measurable_prod_mk_left ht) (measure_ne_top (condKernelReal ρ a) _)
      _ = ∫⁻ a, condKernelReal ρ a univ ∂ρ.fst -
          ∫⁻ a, condKernelReal ρ a {x : ℝ | (a, x) ∈ t} ∂ρ.fst := by
        have h_le : (fun a => condKernelReal ρ a {x : ℝ | (a, x) ∈ t}) ≤ᵐ[ρ.fst] fun a =>
            condKernelReal ρ a univ := eventually_of_forall fun a => measure_mono (subset_univ _)
        rw [lintegral_sub _ _ h_le]
        · exact kernel.measurable_kernel_prod_mk_left ht
        refine' ((lintegral_mono_ae h_le).trans_lt _).ne
        rw [lintegral_condKernelReal_univ]
        exact measure_lt_top ρ univ
      _ = ρ univ - ρ t := by rw [ht_eq, lintegral_condKernelReal_univ]
      _ = ρ tᶜ := (measure_compl ht (measure_ne_top _ _)).symm
  · intro f hf_disj hf_meas hf_eq
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) {x | (a, x) ∈ ⋃ (i : ℕ), f i} ∂Measure …
    have h_eq : ∀ a, {x | (a, x) ∈ ⋃ i, f i} = ⋃ i, {x | (a, x) ∈ f i} := by
      intro a
      ext1 x
      simp only [mem_iUnion, mem_setOf_eq]
    simp_rw [h_eq]
    -- ⊢ ∫⁻ (a : α), ↑↑(↑(condKernelReal ρ) a) (⋃ (i : ℕ), {x | (a, x) ∈ f i}) ∂Measu …
    have h_disj : ∀ a, Pairwise (Disjoint on fun i => {x | (a, x) ∈ f i}) := by
      intro a i j hij
      have h_disj := hf_disj hij
      rw [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj ⊢
      ext1 x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false_iff]
      intro h_mem_both
      suffices (a, x) ∈ ∅ by rwa [mem_empty_iff_false] at this
      rwa [← h_disj, mem_inter_iff]
    calc
      ∫⁻ a, condKernelReal ρ a (⋃ i, {x | (a, x) ∈ f i}) ∂ρ.fst =
          ∫⁻ a, ∑' i, condKernelReal ρ a {x | (a, x) ∈ f i} ∂ρ.fst := by
        congr with a : 1
        rw [measure_iUnion (h_disj a) fun i => measurable_prod_mk_left (hf_meas i)]
      _ = ∑' i, ∫⁻ a, condKernelReal ρ a {x | (a, x) ∈ f i} ∂ρ.fst :=
        (lintegral_tsum fun i => (kernel.measurable_kernel_prod_mk_left (hf_meas i)).aemeasurable)
      _ = ∑' i, ρ (f i) := by simp_rw [hf_eq]
      _ = ρ (iUnion f) := (measure_iUnion hf_disj hf_meas).symm
#align probability_theory.lintegral_cond_kernel_real_mem ProbabilityTheory.lintegral_condKernelReal_mem

theorem kernel.const_eq_compProd_real (γ : Type*) [MeasurableSpace γ] (ρ : Measure (α × ℝ))
    [IsFiniteMeasure ρ] :
    kernel.const γ ρ = kernel.const γ ρ.fst ⊗ₖ kernel.prodMkLeft γ (condKernelReal ρ) := by
  ext a s hs : 2
  -- ⊢ ↑↑(↑(const γ ρ) a) s = ↑↑(↑(const γ (Measure.fst ρ) ⊗ₖ prodMkLeft γ (condKer …
  rw [kernel.compProd_apply _ _ _ hs, kernel.const_apply, kernel.const_apply]
  -- ⊢ ↑↑ρ s = ∫⁻ (b : α), ↑↑(↑(prodMkLeft γ (condKernelReal ρ)) (a, b)) {c | (b, c …
  simp_rw [kernel.prodMkLeft_apply]
  -- ⊢ ↑↑ρ s = ∫⁻ (b : α), ↑↑(↑(condKernelReal ρ) b) {c | (b, c) ∈ s} ∂Measure.fst ρ
  rw [lintegral_condKernelReal_mem ρ hs]
  -- 🎉 no goals
#align probability_theory.kernel.const_eq_comp_prod_real ProbabilityTheory.kernel.const_eq_compProd_real

theorem measure_eq_compProd_real :
    ρ = (kernel.const Unit ρ.fst ⊗ₖ kernel.prodMkLeft Unit (condKernelReal ρ)) () := by
  rw [← kernel.const_eq_compProd_real Unit ρ, kernel.const_apply]
  -- 🎉 no goals
#align probability_theory.measure_eq_comp_prod_real ProbabilityTheory.measure_eq_compProd_real

theorem lintegral_condKernelReal {f : α × ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, ∫⁻ y, f (a, y) ∂condKernelReal ρ a ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  nth_rw 3 [measure_eq_compProd_real ρ]
  -- ⊢ ∫⁻ (a : α), ∫⁻ (y : ℝ), f (a, y) ∂↑(condKernelReal ρ) a ∂Measure.fst ρ = ∫⁻  …
  rw [kernel.lintegral_compProd _ _ _ hf, kernel.const_apply]
  -- ⊢ ∫⁻ (a : α), ∫⁻ (y : ℝ), f (a, y) ∂↑(condKernelReal ρ) a ∂Measure.fst ρ = ∫⁻  …
  simp_rw [kernel.prodMkLeft_apply]
  -- 🎉 no goals
#align probability_theory.lintegral_cond_kernel_real ProbabilityTheory.lintegral_condKernelReal

theorem ae_condKernelReal_eq_one {s : Set ℝ} (hs : MeasurableSet s) (hρ : ρ {x | x.snd ∈ sᶜ} = 0) :
    ∀ᵐ a ∂ρ.fst, condKernelReal ρ a s = 1 := by
  have h : ρ {x | x.snd ∈ sᶜ} = (kernel.const Unit ρ.fst ⊗ₖ
      kernel.prodMkLeft Unit (condKernelReal ρ)) () {x | x.snd ∈ sᶜ} := by
    rw [← measure_eq_compProd_real]
  rw [hρ, kernel.compProd_apply] at h
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, ↑↑(↑(condKernelReal ρ) a) s = 1
  swap; · exact measurable_snd hs.compl
  -- ⊢ MeasurableSet {x | x.snd ∈ sᶜ}
          -- 🎉 no goals
  rw [eq_comm, lintegral_eq_zero_iff] at h
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, ↑↑(↑(condKernelReal ρ) a) s = 1
  swap
  -- ⊢ Measurable fun b => ↑↑(↑(kernel.prodMkLeft Unit (condKernelReal ρ)) ((), b)) …
  · simp_rw [kernel.prodMkLeft_apply']
    -- ⊢ Measurable fun b => ↑↑(↑(condKernelReal ρ) b) {c | (b, c) ∈ {x | x.snd ∈ sᶜ}}
    simp only [mem_compl_iff, mem_setOf_eq]
    -- ⊢ Measurable fun b => ↑↑(↑(condKernelReal ρ) b) {c | ¬c ∈ s}
    exact kernel.measurable_coe _ hs.compl
    -- 🎉 no goals
  rw [kernel.const_apply] at h
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, ↑↑(↑(condKernelReal ρ) a) s = 1
  simp only [mem_compl_iff, mem_setOf_eq, kernel.prodMkLeft_apply'] at h
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, ↑↑(↑(condKernelReal ρ) a) s = 1
  filter_upwards [h] with a ha
  -- ⊢ ↑↑(↑(condKernelReal ρ) a) s = 1
  change condKernelReal ρ a sᶜ = 0 at ha
  -- ⊢ ↑↑(↑(condKernelReal ρ) a) s = 1
  rwa [prob_compl_eq_zero_iff hs] at ha
  -- 🎉 no goals
#align probability_theory.ae_cond_kernel_real_eq_one ProbabilityTheory.ae_condKernelReal_eq_one

end Real

section Polish

/-! ### Disintegration of measures on Polish Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize the disintegration
property on `ℝ` to all these spaces. -/


variable {Ω : Type*} [TopologicalSpace Ω] [PolishSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [Nonempty Ω] (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]

/-- Existence of a conditional kernel. Use the definition `condKernel` to get that kernel. -/
theorem exists_cond_kernel (γ : Type*) [MeasurableSpace γ] :
    ∃ (η : kernel α Ω) (_h : IsMarkovKernel η), kernel.const γ ρ =
      kernel.compProd (kernel.const γ ρ.fst) (kernel.prodMkLeft γ η) := by
  obtain ⟨f, hf⟩ := exists_measurableEmbedding_real Ω
  -- ⊢ ∃ η _h, kernel.const γ ρ = kernel.const γ (Measure.fst ρ) ⊗ₖ kernel.prodMkLe …
  let ρ' : Measure (α × ℝ) := ρ.map (Prod.map id f)
  -- ⊢ ∃ η _h, kernel.const γ ρ = kernel.const γ (Measure.fst ρ) ⊗ₖ kernel.prodMkLe …
  -- The general idea is to define `η = kernel.comapRight (condKernelReal ρ') hf`. There is
  -- however an issue: that `η` may not be a Markov kernel since its value is only a
  -- probability distribution almost everywhere with respect to `ρ.fst`, not everywhere.
  -- We modify it to obtain a Markov kernel which is almost everywhere equal.
  let ρ_set := (toMeasurable ρ.fst {a | condKernelReal ρ' a (range f) = 1}ᶜ)ᶜ
  -- ⊢ ∃ η _h, kernel.const γ ρ = kernel.const γ (Measure.fst ρ) ⊗ₖ kernel.prodMkLe …
  have hm : MeasurableSet ρ_set := (measurableSet_toMeasurable _ _).compl
  -- ⊢ ∃ η _h, kernel.const γ ρ = kernel.const γ (Measure.fst ρ) ⊗ₖ kernel.prodMkLe …
  have h_eq_one_of_mem : ∀ a ∈ ρ_set, condKernelReal ρ' a (range f) = 1 := by
    intro a ha
    rw [mem_compl_iff] at ha
    have h_ss := subset_toMeasurable ρ.fst {a : α | condKernelReal ρ' a (range f) = 1}ᶜ
    suffices ha' : a ∉ {a : α | condKernelReal ρ' a (range f) = 1}ᶜ
    · rwa [not_mem_compl_iff] at ha'
    exact not_mem_subset h_ss ha
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : α → α) f) :=
    MeasurableEmbedding.id.prod_mk hf
  have h_fst : ρ'.fst = ρ.fst := by
    ext1 u hu
    rw [Measure.fst_apply hu, Measure.fst_apply hu,
      Measure.map_apply h_prod_embed.measurable (measurable_fst hu)]
    rfl
  have h_ae : ∀ᵐ a ∂ρ.fst, a ∈ ρ_set := by
    rw [ae_iff]
    simp only [not_mem_compl_iff, setOf_mem_eq, measure_toMeasurable]
    change ρ.fst {a : α | a ∉ {a' : α | condKernelReal ρ' a' (range f) = 1}} = 0
    rw [← ae_iff, ← h_fst]
    refine' ae_condKernelReal_eq_one ρ' hf.measurableSet_range _
    rw [Measure.map_apply h_prod_embed.measurable]
    swap; · exact measurable_snd hf.measurableSet_range.compl
    convert measure_empty (α := α × Ω)
    ext1 x
    simp only [mem_compl_iff, mem_range, preimage_setOf_eq, Prod_map, mem_setOf_eq,
      mem_empty_iff_false, iff_false_iff, Classical.not_not, exists_apply_eq_apply]
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ range f := range_nonempty _
  let η' :=
    kernel.piecewise hm (condKernelReal ρ') (kernel.deterministic (fun _ => x₀) measurable_const)
  -- We show that `kernel.comapRight η' hf` is a suitable Markov kernel.
  refine' ⟨kernel.comapRight η' hf, _, _⟩
  · refine' kernel.IsMarkovKernel.comapRight _ _ fun a => _
    rw [kernel.piecewise_apply']
    split_ifs with h_mem
    · exact h_eq_one_of_mem _ h_mem
    · rw [kernel.deterministic_apply' _ _ hf.measurableSet_range, Set.indicator_apply, if_pos hx₀]
  have : kernel.const γ ρ = kernel.comapRight (kernel.const γ ρ') h_prod_embed := by
    ext c t ht : 2
    rw [kernel.const_apply, kernel.comapRight_apply' _ _ _ ht, kernel.const_apply,
      Measure.map_apply h_prod_embed.measurable (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [id.def, mem_preimage, Prod.map_mk, mem_image, Prod.mk.inj_iff, Prod.exists]
    refine' ⟨fun h => ⟨x.1, x.2, h, rfl, rfl⟩, _⟩
    rintro ⟨a, b, h_mem, rfl, hf_eq⟩
    rwa [hf.injective hf_eq] at h_mem
  rw [this, kernel.const_eq_compProd_real _ ρ']
  ext c t ht : 2
  rw [kernel.comapRight_apply' _ _ _ ht,
    kernel.compProd_apply _ _ _ (h_prod_embed.measurableSet_image.mpr ht), kernel.const_apply,
    h_fst, kernel.compProd_apply _ _ _ ht, kernel.const_apply]
  refine' lintegral_congr_ae _
  filter_upwards [h_ae] with a ha
  rw [kernel.prodMkLeft_apply', kernel.prodMkLeft_apply', kernel.comapRight_apply']
  swap
  · exact measurable_prod_mk_left ht
  have h1 : {c : ℝ | (a, c) ∈ Prod.map id f '' t} = f '' {c : Ω | (a, c) ∈ t} := by
    ext1 x
    simp only [Prod_map, id.def, mem_image, Prod.mk.inj_iff, Prod.exists, mem_setOf_eq]
    constructor
    · rintro ⟨a', b, h_mem, rfl, hf_eq⟩
      exact ⟨b, h_mem, hf_eq⟩
    · rintro ⟨b, h_mem, hf_eq⟩
      exact ⟨a, b, h_mem, rfl, hf_eq⟩
  have h2 : condKernelReal ρ' (c, a).snd = η' (c, a).snd := by
    rw [kernel.piecewise_apply, if_pos ha]
  rw [h1, h2]
#align probability_theory.exists_cond_kernel ProbabilityTheory.exists_cond_kernel

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ = ((kernel.const Unit ρ.fst) ⊗ₖ (kernel.prodMkLeft Unit ρ.condKernel)) ()`
(see `ProbabilityTheory.measure_eq_compProd`). -/
noncomputable irreducible_def _root_.MeasureTheory.Measure.condKernel : kernel α Ω :=
  (exists_cond_kernel ρ Unit).choose
#align measure_theory.measure.cond_kernel MeasureTheory.Measure.condKernel

theorem condKernel_def : ρ.condKernel = (exists_cond_kernel ρ Unit).choose := by
  rw [MeasureTheory.Measure.condKernel]
  -- 🎉 no goals
#align probability_theory.cond_kernel_def ProbabilityTheory.condKernel_def

instance : IsMarkovKernel ρ.condKernel := by
  rw [condKernel_def]; exact (exists_cond_kernel ρ Unit).choose_spec.choose
  -- ⊢ IsMarkovKernel (Exists.choose (_ : ∃ η _h, kernel.const Unit ρ = kernel.cons …
                       -- 🎉 no goals

theorem kernel.const_unit_eq_compProd :
    kernel.const Unit ρ = kernel.const Unit ρ.fst ⊗ₖ kernel.prodMkLeft Unit ρ.condKernel := by
  simp_rw [condKernel_def]; exact (exists_cond_kernel ρ Unit).choose_spec.choose_spec
  -- ⊢ const Unit ρ = const Unit (Measure.fst ρ) ⊗ₖ prodMkLeft Unit (Exists.choose  …
                            -- 🎉 no goals
#align probability_theory.kernel.const_unit_eq_comp_prod ProbabilityTheory.kernel.const_unit_eq_compProd

/-- **Disintegration** of finite product measures on `α × Ω`, where `Ω` is Polish Borel. Such a
measure can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`ProbabilityTheory.condKernel ρ`. -/
theorem measure_eq_compProd :
    ρ = (kernel.const Unit ρ.fst ⊗ₖ kernel.prodMkLeft Unit ρ.condKernel) () := by
  rw [← kernel.const_unit_eq_compProd, kernel.const_apply]
  -- 🎉 no goals
#align probability_theory.measure_eq_comp_prod ProbabilityTheory.measure_eq_compProd

/-- **Disintegration** of constant kernels. A constant kernel on a product space `α × Ω`, where `Ω`
is Polish Borel, can be written as the composition-product of the constant kernel with value `ρ.fst`
(marginal measure over `α`) and a Markov kernel from `α` to `Ω`. We call that Markov kernel
`ProbabilityTheory.condKernel ρ`. -/
theorem kernel.const_eq_compProd (γ : Type*) [MeasurableSpace γ] (ρ : Measure (α × Ω))
    [IsFiniteMeasure ρ] :
    kernel.const γ ρ = kernel.const γ ρ.fst ⊗ₖ kernel.prodMkLeft γ ρ.condKernel := by
  ext a s hs : 2
  -- ⊢ ↑↑(↑(const γ ρ) a) s = ↑↑(↑(const γ (Measure.fst ρ) ⊗ₖ prodMkLeft γ (Measure …
  simpa only [kernel.const_apply, kernel.compProd_apply _ _ _ hs, kernel.prodMkLeft_apply'] using
    kernel.ext_iff'.mp (kernel.const_unit_eq_compProd ρ) () s hs
#align probability_theory.kernel.const_eq_comp_prod ProbabilityTheory.kernel.const_eq_compProd

theorem lintegral_condKernel_mem {s : Set (α × Ω)} (hs : MeasurableSet s) :
    ∫⁻ a, ρ.condKernel a {x | (a, x) ∈ s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ∫⁻ (a : α), ↑↑(↑(Measure.condKernel ρ) a) {x | (a, x) ∈ s} ∂Measure.fst ρ =  …
  simp_rw [kernel.compProd_apply _ _ _ hs, kernel.const_apply, kernel.prodMkLeft_apply]
  -- 🎉 no goals
#align probability_theory.lintegral_cond_kernel_mem ProbabilityTheory.lintegral_condKernel_mem

theorem set_lintegral_condKernel_eq_measure_prod {s : Set α} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) : ∫⁻ a in s, ρ.condKernel a t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) =
      ((kernel.const Unit ρ.fst ⊗ₖ kernel.prodMkLeft Unit ρ.condKernel) ()) (s ×ˢ t) := by
    congr; exact measure_eq_compProd ρ
  rw [this, kernel.compProd_apply _ _ _ (hs.prod ht)]
  -- ⊢ ∫⁻ (a : α) in s, ↑↑(↑(Measure.condKernel ρ) a) t ∂Measure.fst ρ = ∫⁻ (b : α) …
  simp only [prod_mk_mem_set_prod_eq, kernel.lintegral_const, kernel.prodMkLeft_apply]
  -- ⊢ ∫⁻ (a : α) in s, ↑↑(↑(Measure.condKernel ρ) a) t ∂Measure.fst ρ = ∫⁻ (x : α) …
  rw [← lintegral_indicator _ hs]
  -- ⊢ ∫⁻ (a : α), indicator s (fun a => ↑↑(↑(Measure.condKernel ρ) a) t) a ∂Measur …
  congr
  -- ⊢ (fun a => indicator s (fun a => ↑↑(↑(Measure.condKernel ρ) a) t) a) = fun x  …
  ext1 x
  -- ⊢ indicator s (fun a => ↑↑(↑(Measure.condKernel ρ) a) t) x = ↑↑(↑(Measure.cond …
  classical
  rw [indicator_apply]
  split_ifs with hx
  · simp only [hx, if_true, true_and_iff, setOf_mem_eq]
  · simp only [hx, if_false, false_and_iff, setOf_false, measure_empty]
#align probability_theory.set_lintegral_cond_kernel_eq_measure_prod ProbabilityTheory.set_lintegral_condKernel_eq_measure_prod

theorem lintegral_condKernel {f : α × Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ∫⁻ (a : α), ∫⁻ (ω : Ω), f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fst ρ = …
  rw [kernel.lintegral_compProd _ _ _ hf, kernel.const_apply]
  -- ⊢ ∫⁻ (a : α), ∫⁻ (ω : Ω), f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fst ρ = …
  simp_rw [kernel.prodMkLeft_apply]
  -- 🎉 no goals
#align probability_theory.lintegral_cond_kernel ProbabilityTheory.lintegral_condKernel

theorem set_lintegral_condKernel {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ a in s, ∫⁻ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ∫⁻ (a : α) in s, ∫⁻ (ω : Ω) in t, f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measu …
  rw [← kernel.restrict_apply _ (hs.prod ht), ← kernel.compProd_restrict hs ht,
    kernel.lintegral_compProd _ _ _ hf, kernel.restrict_apply]
  conv_rhs => enter [2, b, 1]; rw [kernel.restrict_apply _ ht]
  -- 🎉 no goals
#align probability_theory.set_lintegral_cond_kernel ProbabilityTheory.set_lintegral_condKernel

theorem set_lintegral_condKernel_univ_right {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ∫⁻ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in s ×ˢ univ, f x ∂ρ := by
  rw [← set_lintegral_condKernel ρ hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]
  -- ⊢ ∫⁻ (a : α) in s, ∫⁻ (ω : Ω), f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fs …
                                                              -- 🎉 no goals
#align probability_theory.set_lintegral_cond_kernel_univ_right ProbabilityTheory.set_lintegral_condKernel_univ_right

theorem set_lintegral_condKernel_univ_left {f : α × Ω → ℝ≥0∞} (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ a, ∫⁻ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫⁻ x in univ ×ˢ t, f x ∂ρ := by
  rw [← set_lintegral_condKernel ρ hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]
  -- ⊢ ∫⁻ (a : α), ∫⁻ (ω : Ω) in t, f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fs …
                                                              -- 🎉 no goals
#align probability_theory.set_lintegral_cond_kernel_univ_left ProbabilityTheory.set_lintegral_condKernel_univ_left

section IntegralCondKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel {ρ : Measure (α × Ω)}
    [IsFiniteMeasure ρ] {f : α × Ω → E} (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst := by
  rw [measure_eq_compProd ρ] at hf
  -- ⊢ AEStronglyMeasurable (fun x => ∫ (y : Ω), f (x, y) ∂↑(Measure.condKernel ρ)  …
  exact AEStronglyMeasurable.integral_kernel_compProd hf
  -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.integral_cond_kernel MeasureTheory.AEStronglyMeasurable.integral_condKernel

theorem integral_condKernel {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    (hf : Integrable f ρ) : ∫ a, ∫ x, f (a, x) ∂ρ.condKernel a ∂ρ.fst = ∫ ω, f ω ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ∫ (a : α), ∫ (x : Ω), f (a, x) ∂↑(Measure.condKernel ρ) a ∂Measure.fst ρ = ∫ …
  have hf': Integrable f ((kernel.const Unit ρ.fst ⊗ₖ kernel.prodMkLeft Unit ρ.condKernel) ()) := by
    rwa [measure_eq_compProd ρ] at hf
  rw [integral_compProd hf', kernel.const_apply]
  -- ⊢ ∫ (a : α), ∫ (x : Ω), f (a, x) ∂↑(Measure.condKernel ρ) a ∂Measure.fst ρ = ∫ …
  simp_rw [kernel.prodMkLeft_apply]
  -- 🎉 no goals
#align probability_theory.integral_cond_kernel ProbabilityTheory.integral_condKernel

theorem set_integral_condKernel {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {s : Set α} (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ a in s, ∫ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ∫ (a : α) in s, ∫ (ω : Ω) in t, f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure …
  rw [set_integral_compProd hs ht]
  -- ⊢ ∫ (a : α) in s, ∫ (ω : Ω) in t, f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure …
  · simp_rw [kernel.prodMkLeft_apply, kernel.const_apply]
    -- 🎉 no goals
  · rwa [measure_eq_compProd ρ] at hf
    -- 🎉 no goals
#align probability_theory.set_integral_cond_kernel ProbabilityTheory.set_integral_condKernel

theorem set_integral_condKernel_univ_right {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {s : Set α} (hs : MeasurableSet s) (hf : IntegrableOn f (s ×ˢ univ) ρ) :
    ∫ a in s, ∫ ω, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in s ×ˢ univ, f x ∂ρ := by
  rw [← set_integral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]
  -- ⊢ ∫ (a : α) in s, ∫ (ω : Ω), f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fst  …
                                                           -- 🎉 no goals
#align probability_theory.set_integral_cond_kernel_univ_right ProbabilityTheory.set_integral_condKernel_univ_right

theorem set_integral_condKernel_univ_left {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ] {f : α × Ω → E}
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (univ ×ˢ t) ρ) :
    ∫ a, ∫ ω in t, f (a, ω) ∂ρ.condKernel a ∂ρ.fst = ∫ x in univ ×ˢ t, f x ∂ρ := by
  rw [← set_integral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]
  -- ⊢ ∫ (a : α), ∫ (ω : Ω) in t, f (a, ω) ∂↑(Measure.condKernel ρ) a ∂Measure.fst  …
                                                           -- 🎉 no goals
#align probability_theory.set_integral_cond_kernel_univ_left ProbabilityTheory.set_integral_condKernel_univ_left

end IntegralCondKernel

end Polish

end ProbabilityTheory

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/


open ProbabilityTheory

variable {α Ω E F : Type*} {mα : MeasurableSpace α} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [BorelSpace Ω] [PolishSpace Ω] [Nonempty Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω → F}
    (hf : AEStronglyMeasurable f ρ) :
    (∀ᵐ a ∂ρ.fst, Integrable (fun ω => f (a, ω)) (ρ.condKernel a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔ Integrable f ρ := by
  rw [measure_eq_compProd ρ] at hf
  -- ⊢ ((∀ᵐ (a : α) ∂Measure.fst ρ, Integrable fun ω => f (a, ω)) ∧ Integrable fun  …
  conv_rhs => rw [measure_eq_compProd ρ]
  -- ⊢ ((∀ᵐ (a : α) ∂Measure.fst ρ, Integrable fun ω => f (a, ω)) ∧ Integrable fun  …
  rw [integrable_compProd_iff hf]
  -- ⊢ ((∀ᵐ (a : α) ∂Measure.fst ρ, Integrable fun ω => f (a, ω)) ∧ Integrable fun  …
  simp_rw [kernel.prodMkLeft_apply, kernel.const_apply]
  -- 🎉 no goals
#align measure_theory.ae_strongly_measurable.ae_integrable_cond_kernel_iff MeasureTheory.AEStronglyMeasurable.ae_integrable_condKernel_iff

theorem Integrable.condKernel_ae {f : α × Ω → F} (hf_int : Integrable f ρ) :
    ∀ᵐ a ∂ρ.fst, Integrable (fun ω => f (a, ω)) (ρ.condKernel a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, Integrable fun ω => f (a, ω)
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, Integrable fun ω => f (a, ω)
  exact hf_int.1
  -- 🎉 no goals
#align measure_theory.integrable.cond_kernel_ae MeasureTheory.Integrable.condKernel_ae

theorem Integrable.integral_norm_condKernel {f : α × Ω → F} (hf_int : Integrable f ρ) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ρ.condKernel x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  -- ⊢ Integrable fun x => ∫ (y : Ω), ‖f (x, y)‖ ∂↑(Measure.condKernel ρ) x
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  -- ⊢ Integrable fun x => ∫ (y : Ω), ‖f (x, y)‖ ∂↑(Measure.condKernel ρ) x
  exact hf_int.2
  -- 🎉 no goals
#align measure_theory.integrable.integral_norm_cond_kernel MeasureTheory.Integrable.integral_norm_condKernel

theorem Integrable.norm_integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂ρ.condKernel x‖) ρ.fst := by
  refine' hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm _
  -- ⊢ ∀ᵐ (a : α) ∂Measure.fst ρ, ‖‖∫ (y : Ω), f (a, y) ∂↑(Measure.condKernel ρ) a‖ …
  refine' eventually_of_forall fun x => _
  -- ⊢ ‖‖∫ (y : Ω), f (x, y) ∂↑(Measure.condKernel ρ) x‖‖ ≤ ‖∫ (y : Ω), ‖f (x, y)‖  …
  rw [norm_norm]
  -- ⊢ ‖∫ (y : Ω), f (x, y) ∂↑(Measure.condKernel ρ) x‖ ≤ ‖∫ (y : Ω), ‖f (x, y)‖ ∂↑ …
  refine' (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg _).symm
  -- ⊢ 0 ≤ ∫ (a : Ω), ‖f (x, a)‖ ∂↑(Measure.condKernel ρ) x
  exact integral_nonneg_of_ae (eventually_of_forall fun y => norm_nonneg _)
  -- 🎉 no goals
#align measure_theory.integrable.norm_integral_cond_kernel MeasureTheory.Integrable.norm_integral_condKernel

theorem Integrable.integral_condKernel {f : α × Ω → E} (hf_int : Integrable f ρ) :
    Integrable (fun x => ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst :=
  (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel
#align measure_theory.integrable.integral_cond_kernel MeasureTheory.Integrable.integral_condKernel

end MeasureTheory
