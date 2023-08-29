/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Basic

#align_import probability.kernel.basic from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → MeasureTheory.Measure β`, where the measurable space instance on `measure β` is the one defined
in `MeasureTheory.Measure.instMeasurableSpace`. That is, a kernel `κ` verifies that for all
measurable sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `ProbabilityTheory.kernel α β`: kernels from `α` to `β`, defined as the `AddSubmonoid` of the
  measurable functions in `α → Measure β`.
* `ProbabilityTheory.IsMarkovKernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
  if for all `a : α`, `k a` is a probability measure.
* `ProbabilityTheory.IsFiniteKernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires a
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `ProbabilityTheory.IsSFiniteKernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

Particular kernels:
* `ProbabilityTheory.kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a)`

## Main statements

* `ProbabilityTheory.kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/


open MeasureTheory

open scoped MeasureTheory ENNReal NNReal BigOperators

namespace ProbabilityTheory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by
`MeasureTheory.Measure.instMeasurableSpace`. A map `κ : α → MeasureTheory.Measure β` is measurable
iff `∀ s : Set β, MeasurableSet s → Measurable (fun a ↦ κ a s)`. -/
noncomputable def kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    AddSubmonoid (α → Measure β) where
  carrier := Measurable
  zero_mem' := measurable_zero
  add_mem' hf hg := Measurable.add hf hg
#align probability_theory.kernel ProbabilityTheory.kernel

-- Porting note: using `FunLike` instead of `CoeFun` to use `FunLike.coe`
instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    FunLike (kernel α β) α fun _ => Measure β where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace kernel

@[simp]
theorem coeFn_zero : ⇑(0 : kernel α β) = 0 :=
  rfl
#align probability_theory.kernel.coe_fn_zero ProbabilityTheory.kernel.coeFn_zero

@[simp]
theorem coeFn_add (κ η : kernel α β) : ⇑(κ + η) = κ + η :=
  rfl
#align probability_theory.kernel.coe_fn_add ProbabilityTheory.kernel.coeFn_add

/-- Coercion to a function as an additive monoid homomorphism. -/
def coeAddHom (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    kernel α β →+ α → Measure β :=
  AddSubmonoid.subtype _
#align probability_theory.kernel.coe_add_hom ProbabilityTheory.kernel.coeAddHom

@[simp]
theorem zero_apply (a : α) : (0 : kernel α β) a = 0 :=
  rfl
#align probability_theory.kernel.zero_apply ProbabilityTheory.kernel.zero_apply

@[simp]
theorem coe_finset_sum (I : Finset ι) (κ : ι → kernel α β) : ⇑(∑ i in I, κ i) = ∑ i in I, ⇑(κ i) :=
  (coeAddHom α β).map_sum _ _
#align probability_theory.kernel.coe_finset_sum ProbabilityTheory.kernel.coe_finset_sum

theorem finset_sum_apply (I : Finset ι) (κ : ι → kernel α β) (a : α) :
    (∑ i in I, κ i) a = ∑ i in I, κ i a := by rw [coe_finset_sum, Finset.sum_apply]
                                              -- 🎉 no goals
#align probability_theory.kernel.finset_sum_apply ProbabilityTheory.kernel.finset_sum_apply

theorem finset_sum_apply' (I : Finset ι) (κ : ι → kernel α β) (a : α) (s : Set β) :
    (∑ i in I, κ i) a s = ∑ i in I, κ i a s := by rw [finset_sum_apply, Measure.finset_sum_apply]
                                                  -- 🎉 no goals
#align probability_theory.kernel.finset_sum_apply' ProbabilityTheory.kernel.finset_sum_apply'

end kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class IsMarkovKernel (κ : kernel α β) : Prop where
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)
#align probability_theory.is_markov_kernel ProbabilityTheory.IsMarkovKernel

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class IsFiniteKernel (κ : kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C
#align probability_theory.is_finite_kernel ProbabilityTheory.IsFiniteKernel

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`ProbabilityTheory.IsFiniteKernel.bound_lt_top κ`) and
for all `a : α` and `s : Set β`, `κ a s ≤ C` (`ProbabilityTheory.kernel.measure_le_bound κ a s`).

Porting note: TODO: does it make sense to make `ProbabilityTheory.IsFiniteKernel.bound` the least
possible bound? Should it be an `NNReal` number? -/
noncomputable def IsFiniteKernel.bound (κ : kernel α β) [h : IsFiniteKernel κ] : ℝ≥0∞ :=
  h.exists_univ_le.choose
#align probability_theory.is_finite_kernel.bound ProbabilityTheory.IsFiniteKernel.bound

theorem IsFiniteKernel.bound_lt_top (κ : kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ < ∞ :=
  h.exists_univ_le.choose_spec.1
#align probability_theory.is_finite_kernel.bound_lt_top ProbabilityTheory.IsFiniteKernel.bound_lt_top

theorem IsFiniteKernel.bound_ne_top (κ : kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel.bound κ ≠ ∞ :=
  (IsFiniteKernel.bound_lt_top κ).ne
#align probability_theory.is_finite_kernel.bound_ne_top ProbabilityTheory.IsFiniteKernel.bound_ne_top

theorem kernel.measure_le_bound (κ : kernel α β) [h : IsFiniteKernel κ] (a : α) (s : Set β) :
    κ a s ≤ IsFiniteKernel.bound κ :=
  (measure_mono (Set.subset_univ s)).trans (h.exists_univ_le.choose_spec.2 a)
#align probability_theory.kernel.measure_le_bound ProbabilityTheory.kernel.measure_le_bound

instance isFiniteKernel_zero (α β : Type*) {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    IsFiniteKernel (0 : kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun _ => by
      simp only [kernel.zero_apply, Measure.coe_zero, Pi.zero_apply, le_zero_iff]⟩⟩
      -- 🎉 no goals
#align probability_theory.is_finite_kernel_zero ProbabilityTheory.isFiniteKernel_zero

instance IsFiniteKernel.add (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine ⟨⟨IsFiniteKernel.bound κ + IsFiniteKernel.bound η,
    ENNReal.add_lt_top.mpr ⟨IsFiniteKernel.bound_lt_top κ, IsFiniteKernel.bound_lt_top η⟩,
    fun a => ?_⟩⟩
  exact add_le_add (kernel.measure_le_bound _ _ _) (kernel.measure_le_bound _ _ _)
  -- 🎉 no goals
#align probability_theory.is_finite_kernel.add ProbabilityTheory.IsFiniteKernel.add

variable {κ : kernel α β}

instance IsMarkovKernel.is_probability_measure' [IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a
#align probability_theory.is_markov_kernel.is_probability_measure' ProbabilityTheory.IsMarkovKernel.is_probability_measure'

instance IsFiniteKernel.isFiniteMeasure [IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(kernel.measure_le_bound κ a Set.univ).trans_lt (IsFiniteKernel.bound_lt_top κ)⟩
#align probability_theory.is_finite_kernel.is_finite_measure ProbabilityTheory.IsFiniteKernel.isFiniteMeasure

instance (priority := 100) IsMarkovKernel.isFiniteKernel [IsMarkovKernel κ] :
    IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, fun _ => prob_le_one⟩⟩
#align probability_theory.is_markov_kernel.is_finite_kernel ProbabilityTheory.IsMarkovKernel.isFiniteKernel

namespace kernel

@[ext]
theorem ext {η : kernel α β} (h : ∀ a, κ a = η a) : κ = η := FunLike.ext _ _ h
#align probability_theory.kernel.ext ProbabilityTheory.kernel.ext

theorem ext_iff {η : kernel α β} : κ = η ↔ ∀ a, κ a = η a := FunLike.ext_iff
#align probability_theory.kernel.ext_iff ProbabilityTheory.kernel.ext_iff

theorem ext_iff' {η : kernel α β} :
    κ = η ↔ ∀ a s, MeasurableSet s → κ a s = η a s := by
  simp_rw [ext_iff, Measure.ext_iff]
  -- 🎉 no goals
#align probability_theory.kernel.ext_iff' ProbabilityTheory.kernel.ext_iff'

theorem ext_fun {η : kernel α β} (h : ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext a s hs
  -- ⊢ ↑↑(↑κ a) s = ↑↑(↑η a) s
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  -- ⊢ ↑↑(↑κ a) s = ↑↑(↑η a) s
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  -- ⊢ ↑↑(↑κ a) s = ↑↑(↑η a) s
  rw [h]
  -- 🎉 no goals
#align probability_theory.kernel.ext_fun ProbabilityTheory.kernel.ext_fun

theorem ext_fun_iff {η : kernel α β} :
    κ = η ↔ ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f _ => by rw [h], ext_fun⟩
                     -- 🎉 no goals
#align probability_theory.kernel.ext_fun_iff ProbabilityTheory.kernel.ext_fun_iff

protected theorem measurable (κ : kernel α β) : Measurable κ :=
  κ.prop
#align probability_theory.kernel.measurable ProbabilityTheory.kernel.measurable

protected theorem measurable_coe (κ : kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp (kernel.measurable κ)
#align probability_theory.kernel.measurable_coe ProbabilityTheory.kernel.measurable_coe

lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x s).toReal) μ := by
  refine' Integrable.mono' (integrable_const (IsFiniteKernel.bound κ).toReal)
    ((kernel.measurable_coe κ hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ <| fun x => _)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (IsFiniteKernel.bound_ne_top _)]
  exact kernel.measure_le_bound _ _ _
  -- 🎉 no goals

lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x s).toReal) μ :=
  IsFiniteKernel.integrable μ κ hs

section Sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable def sum [Countable ι] (κ : ι → kernel α β) : kernel α β where
  val a := Measure.sum fun n => κ n a
  property := by
    refine' Measure.measurable_of_measurable_coe _ fun s hs => _
    -- ⊢ Measurable fun b => ↑↑(Measure.sum fun n => ↑(κ n) b) s
    simp_rw [Measure.sum_apply _ hs]
    -- ⊢ Measurable fun b => ∑' (i : ι), ↑↑(↑(κ i) b) s
    exact Measurable.ennreal_tsum fun n => kernel.measurable_coe (κ n) hs
    -- 🎉 no goals
#align probability_theory.kernel.sum ProbabilityTheory.kernel.sum

theorem sum_apply [Countable ι] (κ : ι → kernel α β) (a : α) :
    kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl
#align probability_theory.kernel.sum_apply ProbabilityTheory.kernel.sum_apply

theorem sum_apply' [Countable ι] (κ : ι → kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, Measure.sum_apply _ hs]
                                           -- 🎉 no goals
#align probability_theory.kernel.sum_apply' ProbabilityTheory.kernel.sum_apply'

@[simp]
theorem sum_zero [Countable ι] : (kernel.sum fun _ : ι => (0 : kernel α β)) = 0 := by
  ext a s hs
  -- ⊢ ↑↑(↑(kernel.sum fun x => 0) a) s = ↑↑(↑0 a) s
  rw [sum_apply' _ a hs]
  -- ⊢ ∑' (n : ι), ↑↑(↑0 a) s = ↑↑(↑0 a) s
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]
  -- 🎉 no goals
#align probability_theory.kernel.sum_zero ProbabilityTheory.kernel.sum_zero

theorem sum_comm [Countable ι] (κ : ι → ι → kernel α β) :
    (kernel.sum fun n => kernel.sum (κ n)) = kernel.sum fun m => kernel.sum fun n => κ n m := by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]
  -- ⊢ ↑↑(↑(kernel.sum fun n => kernel.sum (κ n)) a) s = ↑↑(↑(kernel.sum fun m => k …
           -- ⊢ ↑↑(Measure.sum fun n => Measure.sum fun n_1 => ↑(κ n n_1) a) s = ↑↑(Measure. …
                                -- 🎉 no goals
#align probability_theory.kernel.sum_comm ProbabilityTheory.kernel.sum_comm

@[simp]
theorem sum_fintype [Fintype ι] (κ : ι → kernel α β) : kernel.sum κ = ∑ i, κ i := by
  ext a s hs
  -- ⊢ ↑↑(↑(kernel.sum κ) a) s = ↑↑(↑(∑ i : ι, κ i) a) s
  simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype]
  -- 🎉 no goals
#align probability_theory.kernel.sum_fintype ProbabilityTheory.kernel.sum_fintype

theorem sum_add [Countable ι] (κ η : ι → kernel α β) :
    (kernel.sum fun n => κ n + η n) = kernel.sum κ + kernel.sum η := by
  ext a s hs
  -- ⊢ ↑↑(↑(kernel.sum fun n => κ n + η n) a) s = ↑↑(↑(kernel.sum κ + kernel.sum η) …
  simp only [coeFn_add, Pi.add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, tsum_add ENNReal.summable ENNReal.summable]
#align probability_theory.kernel.sum_add ProbabilityTheory.kernel.sum_add

end Sum

section SFinite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class _root_.ProbabilityTheory.IsSFiniteKernel (κ : kernel α β) : Prop where
  tsum_finite : ∃ κs : ℕ → kernel α β, (∀ n, IsFiniteKernel (κs n)) ∧ κ = kernel.sum κs
#align probability_theory.is_s_finite_kernel ProbabilityTheory.IsSFiniteKernel

instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by simp only; split_ifs; exact h; infer_instance, by
                                                 -- ⊢ IsFiniteKernel (if n = 0 then κ else 0)
                                                            -- ⊢ IsFiniteKernel κ
                                                                       -- ⊢ IsFiniteKernel 0
                                                                                -- 🎉 no goals
      ext a s hs
      -- ⊢ ↑↑(↑κ a) s = ↑↑(↑(kernel.sum fun n => if n = 0 then κ else 0) a) s
      rw [kernel.sum_apply' _ _ hs]
      -- ⊢ ↑↑(↑κ a) s = ∑' (n : ℕ), ↑↑(↑(if n = 0 then κ else 0) a) s
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 := by
        ext1 i; split_ifs <;> rfl
      rw [this, tsum_ite_eq]⟩⟩
      -- 🎉 no goals
#align probability_theory.kernel.is_finite_kernel.is_s_finite_kernel ProbabilityTheory.kernel.IsFiniteKernel.isSFiniteKernel

/-- A sequence of finite kernels such that `κ = ProbabilityTheory.kernel.sum (seq κ)`. See
`ProbabilityTheory.kernel.isFiniteKernel_seq` and `ProbabilityTheory.kernel.kernel_sum_seq`. -/
noncomputable def seq (κ : kernel α β) [h : IsSFiniteKernel κ] : ℕ → kernel α β :=
  h.tsum_finite.choose
#align probability_theory.kernel.seq ProbabilityTheory.kernel.seq

theorem kernel_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] : kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm
#align probability_theory.kernel.kernel_sum_seq ProbabilityTheory.kernel.kernel_sum_seq

theorem measure_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← kernel.sum_apply, kernel_sum_seq κ]
                                                 -- 🎉 no goals
#align probability_theory.kernel.measure_sum_seq ProbabilityTheory.kernel.measure_sum_seq

instance isFiniteKernel_seq (κ : kernel α β) [h : IsSFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n
#align probability_theory.kernel.is_finite_kernel_seq ProbabilityTheory.kernel.isFiniteKernel_seq

instance IsSFiniteKernel.add (κ η : kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) := by
  refine' ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, _⟩⟩
  -- ⊢ κ + η = kernel.sum fun n => seq κ n + seq η n
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η]
  -- 🎉 no goals
#align probability_theory.kernel.is_s_finite_kernel.add ProbabilityTheory.kernel.IsSFiniteKernel.add

theorem IsSFiniteKernel.finset_sum {κs : ι → kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i in I, κs i) := by
  classical
  induction' I using Finset.induction with i I hi_nmem_I h_ind h
  · rw [Finset.sum_empty]; infer_instance
  · rw [Finset.sum_insert hi_nmem_I]
    haveI : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x : ι in I, κs x) :=
      h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
    exact IsSFiniteKernel.add _ _
#align probability_theory.kernel.is_s_finite_kernel.finset_sum ProbabilityTheory.kernel.IsSFiniteKernel.finset_sum

theorem isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι → kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (kernel.sum κs) := by
  let e : ℕ ≃ ι × ℕ := (Denumerable.eqv (ι × ℕ)).symm
  -- ⊢ IsSFiniteKernel (kernel.sum κs)
  refine' ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, _⟩⟩
  -- ⊢ kernel.sum κs = kernel.sum fun n => seq (κs (↑e n).fst) (↑e n).snd
  have hκ_eq : kernel.sum κs = kernel.sum fun n => kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  -- ⊢ ↑↑(↑(kernel.sum κs) a) s = ↑↑(↑(kernel.sum fun n => seq (κs (↑e n).fst) (↑e  …
  rw [hκ_eq]
  -- ⊢ ↑↑(↑(kernel.sum fun n => kernel.sum (seq (κs n))) a) s = ↑↑(↑(kernel.sum fun …
  simp_rw [kernel.sum_apply' _ _ hs]
  -- ⊢ ∑' (n : ι) (n_1 : ℕ), ↑↑(↑(seq (κs n) n_1) a) s = ∑' (n : ℕ), ↑↑(↑(seq (κs ( …
  change (∑' i, ∑' m, seq (κs i) m a s) = ∑' n, (fun im : ι × ℕ => seq (κs im.fst) im.snd a s) (e n)
  -- ⊢ ∑' (i : ι) (m : ℕ), ↑↑(↑(seq (κs i) m) a) s = ∑' (n : ℕ), (fun im => ↑↑(↑(se …
  rw [e.tsum_eq (fun im : ι × ℕ => seq (κs im.fst) im.snd a s),
    tsum_prod' ENNReal.summable fun _ => ENNReal.summable]
#align probability_theory.kernel.is_s_finite_kernel_sum_of_denumerable ProbabilityTheory.kernel.isSFiniteKernel_sum_of_denumerable

theorem isSFiniteKernel_sum [Countable ι] {κs : ι → kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (kernel.sum κs) := by
  cases fintypeOrInfinite ι
  -- ⊢ IsSFiniteKernel (kernel.sum κs)
  · rw [sum_fintype]
    -- ⊢ IsSFiniteKernel (∑ i : ι, κs i)
    exact IsSFiniteKernel.finset_sum Finset.univ fun i _ => hκs i
    -- 🎉 no goals
  cases nonempty_denumerable ι
  -- ⊢ IsSFiniteKernel (kernel.sum κs)
  exact isSFiniteKernel_sum_of_denumerable hκs
  -- 🎉 no goals
#align probability_theory.kernel.is_s_finite_kernel_sum ProbabilityTheory.kernel.isSFiniteKernel_sum

end SFinite

section Deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
noncomputable def deterministic (f : α → β) (hf : Measurable f) : kernel α β where
  val a := Measure.dirac (f a)
  property := by
    refine' Measure.measurable_of_measurable_coe _ fun s hs => _
    -- ⊢ Measurable fun b => ↑↑(Measure.dirac (f b)) s
    simp_rw [Measure.dirac_apply' _ hs]
    -- ⊢ Measurable fun b => Set.indicator s 1 (f b)
    exact measurable_one.indicator (hf hs)
    -- 🎉 no goals
#align probability_theory.kernel.deterministic ProbabilityTheory.kernel.deterministic

theorem deterministic_apply {f : α → β} (hf : Measurable f) (a : α) :
    deterministic f hf a = Measure.dirac (f a) :=
  rfl
#align probability_theory.kernel.deterministic_apply ProbabilityTheory.kernel.deterministic_apply

theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  -- ⊢ ↑↑(↑{ val := fun a => Measure.dirac (f a), property := (_ : Measurable fun a …
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  -- ⊢ ↑↑(Measure.dirac (f a)) s = Set.indicator s 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]
  -- 🎉 no goals
#align probability_theory.kernel.deterministic_apply' ProbabilityTheory.kernel.deterministic_apply'

instance isMarkovKernel_deterministic {f : α → β} (hf : Measurable f) :
    IsMarkovKernel (deterministic f hf) :=
  ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩
               -- ⊢ IsProbabilityMeasure (Measure.dirac (f a))
                                            -- 🎉 no goals
#align probability_theory.kernel.is_markov_kernel_deterministic ProbabilityTheory.kernel.isMarkovKernel_deterministic

theorem lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : ∫⁻ x, f x ∂kernel.deterministic g hg a = f (g a) := by
  rw [kernel.deterministic_apply, lintegral_dirac' _ hf]
  -- 🎉 no goals
#align probability_theory.kernel.lintegral_deterministic' ProbabilityTheory.kernel.lintegral_deterministic'

@[simp]
theorem lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫⁻ x, f x ∂kernel.deterministic g hg a = f (g a) := by
  rw [kernel.deterministic_apply, lintegral_dirac (g a) f]
  -- 🎉 no goals
#align probability_theory.kernel.lintegral_deterministic ProbabilityTheory.kernel.lintegral_deterministic

theorem set_lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂kernel.deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_lintegral_dirac' hf hs]
  -- 🎉 no goals
#align probability_theory.kernel.set_lintegral_deterministic' ProbabilityTheory.kernel.set_lintegral_deterministic'

@[simp]
theorem set_lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂kernel.deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_lintegral_dirac f s]
  -- 🎉 no goals
#align probability_theory.kernel.set_lintegral_deterministic ProbabilityTheory.kernel.set_lintegral_deterministic

theorem integral_deterministic' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) : ∫ x, f x ∂kernel.deterministic g hg a = f (g a) := by
  rw [kernel.deterministic_apply, integral_dirac' _ _ hf]
  -- 🎉 no goals
#align probability_theory.kernel.integral_deterministic' ProbabilityTheory.kernel.integral_deterministic'

@[simp]
theorem integral_deterministic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫ x, f x ∂kernel.deterministic g hg a = f (g a) := by
  rw [kernel.deterministic_apply, integral_dirac _ (g a)]
  -- 🎉 no goals
#align probability_theory.kernel.integral_deterministic ProbabilityTheory.kernel.integral_deterministic

theorem set_integral_deterministic' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂kernel.deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_integral_dirac' hf _ hs]
  -- 🎉 no goals
#align probability_theory.kernel.set_integral_deterministic' ProbabilityTheory.kernel.set_integral_deterministic'

@[simp]
theorem set_integral_deterministic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂kernel.deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_integral_dirac f _ s]
  -- 🎉 no goals
#align probability_theory.kernel.set_integral_deterministic ProbabilityTheory.kernel.set_integral_deterministic

end Deterministic

section Const

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    kernel α β where
  val _ := μβ
  property := measurable_const
#align probability_theory.kernel.const ProbabilityTheory.kernel.const

theorem const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ :=
  rfl
#align probability_theory.kernel.const_apply ProbabilityTheory.kernel.const_apply

instance isFiniteKernel_const {μβ : Measure β} [IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩
#align probability_theory.kernel.is_finite_kernel_const ProbabilityTheory.kernel.isFiniteKernel_const

instance isMarkovKernel_const {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun _ => hμβ⟩
#align probability_theory.kernel.is_markov_kernel_const ProbabilityTheory.kernel.isMarkovKernel_const

@[simp]
theorem lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} :
    ∫⁻ x, f x ∂kernel.const α μ a = ∫⁻ x, f x ∂μ := by rw [kernel.const_apply]
                                                       -- 🎉 no goals
#align probability_theory.kernel.lintegral_const ProbabilityTheory.kernel.lintegral_const

@[simp]
theorem set_lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} {s : Set β} :
    ∫⁻ x in s, f x ∂kernel.const α μ a = ∫⁻ x in s, f x ∂μ := by rw [kernel.const_apply]
                                                                 -- 🎉 no goals
#align probability_theory.kernel.set_lintegral_const ProbabilityTheory.kernel.set_lintegral_const

@[simp]
theorem integral_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {μ : Measure β} {a : α} : ∫ x, f x ∂kernel.const α μ a = ∫ x, f x ∂μ := by
  rw [kernel.const_apply]
  -- 🎉 no goals
#align probability_theory.kernel.integral_const ProbabilityTheory.kernel.integral_const

@[simp]
theorem set_integral_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {μ : Measure β} {a : α} {s : Set β} :
    ∫ x in s, f x ∂kernel.const α μ a = ∫ x in s, f x ∂μ := by rw [kernel.const_apply]
                                                               -- 🎉 no goals
#align probability_theory.kernel.set_integral_const ProbabilityTheory.kernel.set_integral_const

end Const

/-- In a countable space with measurable singletons, every function `α → MeasureTheory.Measure β`
defines a kernel. -/
def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) : kernel α β where
  val := f
  property := measurable_of_countable f
#align probability_theory.kernel.of_fun_of_countable ProbabilityTheory.kernel.ofFunOfCountable

section Restrict

variable {s t : Set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
protected noncomputable def restrict (κ : kernel α β) (hs : MeasurableSet s) : kernel α β where
  val a := (κ a).restrict s
  property := by
    refine' Measure.measurable_of_measurable_coe _ fun t ht => _
    -- ⊢ Measurable fun b => ↑↑(Measure.restrict (↑κ b) s) t
    simp_rw [Measure.restrict_apply ht]
    -- ⊢ Measurable fun b => ↑↑(↑κ b) (t ∩ s)
    exact kernel.measurable_coe κ (ht.inter hs)
    -- 🎉 no goals
#align probability_theory.kernel.restrict ProbabilityTheory.kernel.restrict

theorem restrict_apply (κ : kernel α β) (hs : MeasurableSet s) (a : α) :
    kernel.restrict κ hs a = (κ a).restrict s :=
  rfl
#align probability_theory.kernel.restrict_apply ProbabilityTheory.kernel.restrict_apply

theorem restrict_apply' (κ : kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    kernel.restrict κ hs a t = (κ a) (t ∩ s) := by
  rw [restrict_apply κ hs a, Measure.restrict_apply ht]
  -- 🎉 no goals
#align probability_theory.kernel.restrict_apply' ProbabilityTheory.kernel.restrict_apply'

@[simp]
theorem restrict_univ : kernel.restrict κ MeasurableSet.univ = κ := by
  ext1 a
  -- ⊢ ↑(kernel.restrict κ (_ : MeasurableSet Set.univ)) a = ↑κ a
  rw [kernel.restrict_apply, Measure.restrict_univ]
  -- 🎉 no goals
#align probability_theory.kernel.restrict_univ ProbabilityTheory.kernel.restrict_univ

@[simp]
theorem lintegral_restrict (κ : kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞) :
    ∫⁻ b, f b ∂kernel.restrict κ hs a = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]
                                                                  -- 🎉 no goals
#align probability_theory.kernel.lintegral_restrict ProbabilityTheory.kernel.lintegral_restrict

@[simp]
theorem set_lintegral_restrict (κ : kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞)
    (t : Set β) : ∫⁻ b in t, f b ∂kernel.restrict κ hs a = ∫⁻ b in t ∩ s, f b ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]
  -- 🎉 no goals
#align probability_theory.kernel.set_lintegral_restrict ProbabilityTheory.kernel.set_lintegral_restrict

@[simp]
theorem set_integral_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {a : α} (hs : MeasurableSet s) (t : Set β) :
    ∫ x in t, f x ∂kernel.restrict κ hs a = ∫ x in t ∩ s, f x ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]
  -- 🎉 no goals
#align probability_theory.kernel.set_integral_restrict ProbabilityTheory.kernel.set_integral_restrict

instance IsFiniteKernel.restrict (κ : kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (kernel.restrict κ hs) := by
  refine' ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => _⟩⟩
  -- ⊢ ↑↑(↑(kernel.restrict κ hs) a) Set.univ ≤ IsFiniteKernel.bound κ
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  -- ⊢ ↑↑(↑κ a) (Set.univ ∩ s) ≤ IsFiniteKernel.bound κ
  exact measure_le_bound κ a _
  -- 🎉 no goals
#align probability_theory.kernel.is_finite_kernel.restrict ProbabilityTheory.kernel.IsFiniteKernel.restrict

instance IsSFiniteKernel.restrict (κ : kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (kernel.restrict κ hs) := by
  refine' ⟨⟨fun n => kernel.restrict (seq κ n) hs, inferInstance, _⟩⟩
  -- ⊢ kernel.restrict κ hs = kernel.sum fun n => kernel.restrict (seq κ n) hs
  ext1 a
  -- ⊢ ↑(kernel.restrict κ hs) a = ↑(kernel.sum fun n => kernel.restrict (seq κ n)  …
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]
  -- 🎉 no goals
#align probability_theory.kernel.is_s_finite_kernel.restrict ProbabilityTheory.kernel.IsSFiniteKernel.restrict

end Restrict

section ComapRight

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : γ → β}

/-- Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for a measurable set
`t : Set β`, `ProbabilityTheory.kernel.comapRight κ hf a t = κ a (f '' t)`. -/
noncomputable def comapRight (κ : kernel α β) (hf : MeasurableEmbedding f) : kernel α γ where
  val a := (κ a).comap f
  property := by
    refine' Measure.measurable_measure.mpr fun t ht => _
    -- ⊢ Measurable fun b => ↑↑(Measure.comap f (↑κ b)) t
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' ↦ hf.measurableSet_image.mpr hs'
    rw [this]
    -- ⊢ Measurable fun a => ↑↑(↑κ a) (f '' t)
    exact kernel.measurable_coe _ (hf.measurableSet_image.mpr ht)
    -- 🎉 no goals
#align probability_theory.kernel.comap_right ProbabilityTheory.kernel.comapRight

theorem comapRight_apply (κ : kernel α β) (hf : MeasurableEmbedding f) (a : α) :
    comapRight κ hf a = Measure.comap f (κ a) :=
  rfl
#align probability_theory.kernel.comap_right_apply ProbabilityTheory.kernel.comapRight_apply

theorem comapRight_apply' (κ : kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
    (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t) := by
  rw [comapRight_apply,
    Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]
#align probability_theory.kernel.comap_right_apply' ProbabilityTheory.kernel.comapRight_apply'

theorem IsMarkovKernel.comapRight (κ : kernel α β) (hf : MeasurableEmbedding f)
    (hκ : ∀ a, κ a (Set.range f) = 1) : IsMarkovKernel (comapRight κ hf) := by
  refine' ⟨fun a => ⟨_⟩⟩
  -- ⊢ ↑↑(↑(kernel.comapRight κ hf) a) Set.univ = 1
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  -- ⊢ ↑↑(↑κ a) (f '' Set.univ) = 1
  simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  -- ⊢ ↑↑(↑κ a) (Set.range f) = 1
  exact hκ a
  -- 🎉 no goals
#align probability_theory.kernel.is_markov_kernel.comap_right ProbabilityTheory.kernel.IsMarkovKernel.comapRight

instance IsFiniteKernel.comapRight (κ : kernel α β) [IsFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsFiniteKernel (comapRight κ hf) := by
  refine' ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => _⟩⟩
  -- ⊢ ↑↑(↑(kernel.comapRight κ hf) a) Set.univ ≤ IsFiniteKernel.bound κ
  rw [comapRight_apply' κ hf a .univ]
  -- ⊢ ↑↑(↑κ a) (f '' Set.univ) ≤ IsFiniteKernel.bound κ
  exact measure_le_bound κ a _
  -- 🎉 no goals
#align probability_theory.kernel.is_finite_kernel.comap_right ProbabilityTheory.kernel.IsFiniteKernel.comapRight

protected instance IsSFiniteKernel.comapRight (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsSFiniteKernel (comapRight κ hf) := by
  refine' ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, _⟩⟩
  -- ⊢ comapRight κ hf = kernel.sum fun n => comapRight (seq κ n) hf
  ext1 a
  -- ⊢ ↑(comapRight κ hf) a = ↑(kernel.sum fun n => comapRight (seq κ n) hf) a
  rw [sum_apply]
  -- ⊢ ↑(comapRight κ hf) a = Measure.sum fun n => ↑(comapRight (seq κ n) hf) a
  simp_rw [comapRight_apply _ hf]
  -- ⊢ Measure.comap f (↑κ a) = Measure.sum fun n => Measure.comap f (↑(seq κ n) a)
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht,
      Measure.sum_apply _ ht, Measure.sum_apply _ (hf.measurableSet_image.mpr ht)]
    congr with n : 1
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht]
  rw [this, measure_sum_seq]
  -- 🎉 no goals
#align probability_theory.kernel.is_s_finite_kernel.comap_right ProbabilityTheory.kernel.IsSFiniteKernel.comapRight

end ComapRight

section Piecewise

variable {η : kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

/-- `ProbabilityTheory.kernel.piecewise hs κ η` is the kernel equal to `κ` on the measurable set `s`
and to `η` on its complement. -/
def piecewise (hs : MeasurableSet s) (κ η : kernel α β) : kernel α β where
  val a := if a ∈ s then κ a else η a
  property := Measurable.piecewise hs (kernel.measurable _) (kernel.measurable _)
#align probability_theory.kernel.piecewise ProbabilityTheory.kernel.piecewise

theorem piecewise_apply (a : α) : piecewise hs κ η a = if a ∈ s then κ a else η a :=
  rfl
#align probability_theory.kernel.piecewise_apply ProbabilityTheory.kernel.piecewise_apply

theorem piecewise_apply' (a : α) (t : Set β) :
    piecewise hs κ η a t = if a ∈ s then κ a t else η a t := by
  rw [piecewise_apply]; split_ifs <;> rfl
  -- ⊢ ↑↑(if a ∈ s then ↑κ a else ↑η a) t = if a ∈ s then ↑↑(↑κ a) t else ↑↑(↑η a) t
                        -- ⊢ ↑↑(↑κ a) t = ↑↑(↑κ a) t
                                      -- 🎉 no goals
                                      -- 🎉 no goals
#align probability_theory.kernel.piecewise_apply' ProbabilityTheory.kernel.piecewise_apply'

instance IsMarkovKernel.piecewise [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (piecewise hs κ η) := by
  refine' ⟨fun a => ⟨_⟩⟩
  -- ⊢ ↑↑(↑(kernel.piecewise hs κ η) a) Set.univ = 1
  rw [piecewise_apply', measure_univ, measure_univ, ite_self]
  -- 🎉 no goals
#align probability_theory.kernel.is_markov_kernel.piecewise ProbabilityTheory.kernel.IsMarkovKernel.piecewise

instance IsFiniteKernel.piecewise [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (piecewise hs κ η) := by
  refine' ⟨⟨max (IsFiniteKernel.bound κ) (IsFiniteKernel.bound η), _, fun a => _⟩⟩
  -- ⊢ max (IsFiniteKernel.bound κ) (IsFiniteKernel.bound η) < ⊤
  · exact max_lt (IsFiniteKernel.bound_lt_top κ) (IsFiniteKernel.bound_lt_top η)
    -- 🎉 no goals
  rw [piecewise_apply']
  -- ⊢ (if a ∈ s then ↑↑(↑κ a) Set.univ else ↑↑(↑η a) Set.univ) ≤ max (IsFiniteKern …
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))
  -- 🎉 no goals
#align probability_theory.kernel.is_finite_kernel.piecewise ProbabilityTheory.kernel.IsFiniteKernel.piecewise

protected instance IsSFiniteKernel.piecewise [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (piecewise hs κ η) := by
  refine' ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, _⟩⟩
  -- ⊢ piecewise hs κ η = kernel.sum fun n => piecewise hs (seq κ n) (seq η n)
  ext1 a
  -- ⊢ ↑(piecewise hs κ η) a = ↑(kernel.sum fun n => piecewise hs (seq κ n) (seq η  …
  simp_rw [sum_apply, kernel.piecewise_apply]
  -- ⊢ (if a ∈ s then ↑κ a else ↑η a) = Measure.sum fun n => if a ∈ s then ↑(seq κ  …
  split_ifs <;> exact (measure_sum_seq _ a).symm
  -- ⊢ ↑κ a = Measure.sum fun n => ↑(seq κ n) a
                -- 🎉 no goals
                -- 🎉 no goals
#align probability_theory.kernel.is_s_finite_kernel.piecewise ProbabilityTheory.kernel.IsSFiniteKernel.piecewise

theorem lintegral_piecewise (a : α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
  -- ⊢ (∫⁻ (b : β), g b ∂if a ∈ s then ↑κ a else ↑η a) = if a ∈ s then ∫⁻ (b : β),  …
                             -- ⊢ ∫⁻ (b : β), g b ∂↑κ a = ∫⁻ (b : β), g b ∂↑κ a
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align probability_theory.kernel.lintegral_piecewise ProbabilityTheory.kernel.lintegral_piecewise

theorem set_lintegral_piecewise (a : α) (g : β → ℝ≥0∞) (t : Set β) :
    ∫⁻ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g b ∂η a :=
  by simp_rw [piecewise_apply]; split_ifs <;> rfl
     -- ⊢ (∫⁻ (b : β) in t, g b ∂if a ∈ s then ↑κ a else ↑η a) = if a ∈ s then ∫⁻ (b : …
                                -- ⊢ ∫⁻ (b : β) in t, g b ∂↑κ a = ∫⁻ (b : β) in t, g b ∂↑κ a
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align probability_theory.kernel.set_lintegral_piecewise ProbabilityTheory.kernel.set_lintegral_piecewise

theorem integral_piecewise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : α) (g : β → E) :
    ∫ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
  -- ⊢ (∫ (b : β), g b ∂if a ∈ s then ↑κ a else ↑η a) = if a ∈ s then ∫ (b : β), g  …
                             -- ⊢ ∫ (b : β), g b ∂↑κ a = ∫ (b : β), g b ∂↑κ a
                                           -- 🎉 no goals
                                           -- 🎉 no goals
#align probability_theory.kernel.integral_piecewise ProbabilityTheory.kernel.integral_piecewise

theorem set_integral_piecewise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : α) (g : β → E) (t : Set β) :
    ∫ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a :=
  by simp_rw [piecewise_apply]; split_ifs <;> rfl
     -- ⊢ (∫ (b : β) in t, g b ∂if a ∈ s then ↑κ a else ↑η a) = if a ∈ s then ∫ (b : β …
                                -- ⊢ ∫ (b : β) in t, g b ∂↑κ a = ∫ (b : β) in t, g b ∂↑κ a
                                              -- 🎉 no goals
                                              -- 🎉 no goals
#align probability_theory.kernel.set_integral_piecewise ProbabilityTheory.kernel.set_integral_piecewise

end Piecewise

end kernel

end ProbabilityTheory
