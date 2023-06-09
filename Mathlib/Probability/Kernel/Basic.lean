/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne

! This file was ported from Lean 3 source module probability.kernel.basic
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Constructions.Prod.Basic

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → measure β`, where the measurable space instance on `measure β` is the one defined in
`measure_theory.measure.measurable_space`. That is, a kernel `κ` verifies that for all measurable
sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `probability_theory.kernel α β`: kernels from `α` to `β`, defined as the `add_submonoid` of the
  measurable functions in `α → measure β`.
* `probability_theory.is_markov_kernel κ`: a kernel from `α` to `β` is said to be a Markov kernel
  if for all `a : α`, `k a` is a probability measure.
* `probability_theory.is_finite_kernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires an
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `probability_theory.is_s_finite_kernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

Particular kernels:
* `probability_theory.kernel.deterministic (f : α → β) (hf : measurable f)`:
  kernel `a ↦ measure.dirac (f a)`.
* `probability_theory.kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `probability_theory.kernel.restrict κ (hs : measurable_set s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂(κ a)`

## Main statements

* `probability_theory.kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/


open MeasureTheory

open scoped MeasureTheory ENNReal NNReal BigOperators

namespace ProbabilityTheory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → measure β`. The measurable space structure on `measure β` is given by
`measure_theory.measure.measurable_space`. A map `κ : α → measure β` is measurable iff
`∀ s : set β, measurable_set s → measurable (λ a, κ a s)`. -/
def kernel (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] :
    AddSubmonoid (α → Measure β) where
  carrier := Measurable
  zero_mem' := measurable_zero
  add_mem' hf hg := Measurable.add hf hg
#align probability_theory.kernel ProbabilityTheory.kernel

instance {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] :
    CoeFun (kernel α β) fun _ => α → Measure β :=
  ⟨fun κ => κ.val⟩

variable {α β ι : Type _} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

@[simp]
theorem coeFn_zero : ⇑(0 : kernel α β) = 0 :=
  rfl
#align probability_theory.kernel.coe_fn_zero ProbabilityTheory.kernel.coeFn_zero

@[simp]
theorem coeFn_add (κ η : kernel α β) : ⇑(κ + η) = κ + η :=
  rfl
#align probability_theory.kernel.coe_fn_add ProbabilityTheory.kernel.coeFn_add

omit mα mβ

/-- Coercion to a function as an additive monoid homomorphism. -/
def coeAddHom (α β : Type _) [MeasurableSpace α] [MeasurableSpace β] :
    kernel α β →+ α → Measure β :=
  ⟨coeFn, coeFn_zero, coeFn_add⟩
#align probability_theory.kernel.coe_add_hom ProbabilityTheory.kernel.coeAddHom

include mα mβ

@[simp]
theorem zero_apply (a : α) : (0 : kernel α β) a = 0 :=
  rfl
#align probability_theory.kernel.zero_apply ProbabilityTheory.kernel.zero_apply

@[simp]
theorem coe_finset_sum (I : Finset ι) (κ : ι → kernel α β) : ⇑(∑ i in I, κ i) = ∑ i in I, κ i :=
  (coeAddHom α β).map_sum _ _
#align probability_theory.kernel.coe_finset_sum ProbabilityTheory.kernel.coe_finset_sum

theorem finset_sum_apply (I : Finset ι) (κ : ι → kernel α β) (a : α) :
    (∑ i in I, κ i) a = ∑ i in I, κ i a := by rw [coe_finset_sum, Finset.sum_apply]
#align probability_theory.kernel.finset_sum_apply ProbabilityTheory.kernel.finset_sum_apply

theorem finset_sum_apply' (I : Finset ι) (κ : ι → kernel α β) (a : α) (s : Set β) :
    (∑ i in I, κ i) a s = ∑ i in I, κ i a s := by rw [finset_sum_apply, measure.finset_sum_apply]
#align probability_theory.kernel.finset_sum_apply' ProbabilityTheory.kernel.finset_sum_apply'

end Kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class IsMarkovKernel (κ : kernel α β) : Prop where
  IsProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)
#align probability_theory.is_markov_kernel ProbabilityTheory.IsMarkovKernel

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class IsFiniteKernel (κ : kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C
#align probability_theory.is_finite_kernel ProbabilityTheory.IsFiniteKernel

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`is_finite_kernel.bound_lt_top κ`) and for all
`a : α` and `s : set β`, `κ a s ≤ C` (`measure_le_bound κ a s`). -/
noncomputable def IsFiniteKernel.bound (κ : kernel α β) [h : IsFiniteKernel κ] : ℝ≥0∞ :=
  h.exists_univ_le.some
#align probability_theory.is_finite_kernel.bound ProbabilityTheory.IsFiniteKernel.bound

theorem IsFiniteKernel.bound_lt_top (κ : kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ < ∞ :=
  h.exists_univ_le.choose_spec.1
#align probability_theory.is_finite_kernel.bound_lt_top ProbabilityTheory.IsFiniteKernel.bound_lt_top

theorem IsFiniteKernel.bound_ne_top (κ : kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ ≠ ∞ :=
  (IsFiniteKernel.bound_lt_top κ).Ne
#align probability_theory.is_finite_kernel.bound_ne_top ProbabilityTheory.IsFiniteKernel.bound_ne_top

theorem kernel.measure_le_bound (κ : kernel α β) [h : IsFiniteKernel κ] (a : α) (s : Set β) :
    κ a s ≤ IsFiniteKernel.bound κ :=
  (measure_mono (Set.subset_univ s)).trans (h.exists_univ_le.choose_spec.2 a)
#align probability_theory.kernel.measure_le_bound ProbabilityTheory.kernel.measure_le_bound

instance isFiniteKernel_zero (α β : Type _) {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    IsFiniteKernel (0 : kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun a => by
      simp only [kernel.zero_apply, measure.coe_zero, Pi.zero_apply, le_zero_iff]⟩⟩
#align probability_theory.is_finite_kernel_zero ProbabilityTheory.isFiniteKernel_zero

instance IsFiniteKernel.add (κ η : kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine'
    ⟨⟨is_finite_kernel.bound κ + is_finite_kernel.bound η,
        ennreal.add_lt_top.mpr ⟨is_finite_kernel.bound_lt_top κ, is_finite_kernel.bound_lt_top η⟩,
        fun a => _⟩⟩
  simp_rw [kernel.coe_fn_add, Pi.add_apply, measure.coe_add, Pi.add_apply]
  exact add_le_add (kernel.measure_le_bound _ _ _) (kernel.measure_le_bound _ _ _)
#align probability_theory.is_finite_kernel.add ProbabilityTheory.IsFiniteKernel.add

variable {κ : kernel α β}

instance IsMarkovKernel.is_probability_measure' [h : IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a
#align probability_theory.is_markov_kernel.is_probability_measure' ProbabilityTheory.IsMarkovKernel.is_probability_measure'

instance IsFiniteKernel.isFiniteMeasure [h : IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(kernel.measure_le_bound κ a Set.univ).trans_lt (IsFiniteKernel.bound_lt_top κ)⟩
#align probability_theory.is_finite_kernel.is_finite_measure ProbabilityTheory.IsFiniteKernel.isFiniteMeasure

instance (priority := 100) IsMarkovKernel.isFiniteKernel [h : IsMarkovKernel κ] :
    IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, fun a => prob_le_one⟩⟩
#align probability_theory.is_markov_kernel.is_finite_kernel ProbabilityTheory.IsMarkovKernel.isFiniteKernel

namespace Kernel

@[ext]
theorem ext {η : kernel α β} (h : ∀ a, κ a = η a) : κ = η := by ext1; ext1 a; exact h a
#align probability_theory.kernel.ext ProbabilityTheory.kernel.ext

theorem ext_iff {η : kernel α β} : κ = η ↔ ∀ a, κ a = η a :=
  ⟨fun h a => by rw [h], ext⟩
#align probability_theory.kernel.ext_iff ProbabilityTheory.kernel.ext_iff

theorem ext_iff' {η : kernel α β} :
    κ = η ↔ ∀ (a) (s : Set β) (hs : MeasurableSet s), κ a s = η a s := by
  simp_rw [ext_iff, measure.ext_iff]
#align probability_theory.kernel.ext_iff' ProbabilityTheory.kernel.ext_iff'

theorem ext_fun {η : kernel α β} (h : ∀ a f, Measurable f → (∫⁻ b, f b ∂κ a) = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext (a s hs)
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h 
  rw [h]
#align probability_theory.kernel.ext_fun ProbabilityTheory.kernel.ext_fun

theorem ext_fun_iff {η : kernel α β} :
    κ = η ↔ ∀ a f, Measurable f → (∫⁻ b, f b ∂κ a) = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f hf => by rw [h], ext_fun⟩
#align probability_theory.kernel.ext_fun_iff ProbabilityTheory.kernel.ext_fun_iff

protected theorem measurable (κ : kernel α β) : Measurable κ :=
  κ.Prop
#align probability_theory.kernel.measurable ProbabilityTheory.kernel.measurable

protected theorem measurable_coe (κ : kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp (kernel.measurable κ)
#align probability_theory.kernel.measurable_coe ProbabilityTheory.kernel.measurable_coe

section Sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable def sum [Countable ι] (κ : ι → kernel α β) : kernel α β where
  val a := Measure.sum fun n => κ n a
  property := by
    refine' measure.measurable_of_measurable_coe _ fun s hs => _
    simp_rw [measure.sum_apply _ hs]
    exact Measurable.ennreal_tsum fun n => kernel.measurable_coe (κ n) hs
#align probability_theory.kernel.sum ProbabilityTheory.kernel.sum

theorem sum_apply [Countable ι] (κ : ι → kernel α β) (a : α) :
    kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl
#align probability_theory.kernel.sum_apply ProbabilityTheory.kernel.sum_apply

theorem sum_apply' [Countable ι] (κ : ι → kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, measure.sum_apply _ hs]
#align probability_theory.kernel.sum_apply' ProbabilityTheory.kernel.sum_apply'

@[simp]
theorem sum_zero [Countable ι] : (kernel.sum fun i : ι => (0 : kernel α β)) = 0 := by
  ext (a s hs) : 2
  rw [sum_apply' _ a hs]
  simp only [zero_apply, measure.coe_zero, Pi.zero_apply, tsum_zero]
#align probability_theory.kernel.sum_zero ProbabilityTheory.kernel.sum_zero

theorem sum_comm [Countable ι] (κ : ι → ι → kernel α β) :
    (kernel.sum fun n => kernel.sum (κ n)) = kernel.sum fun m => kernel.sum fun n => κ n m := by
  ext (a s hs); simp_rw [sum_apply]; rw [measure.sum_comm]
#align probability_theory.kernel.sum_comm ProbabilityTheory.kernel.sum_comm

@[simp]
theorem sum_fintype [Fintype ι] (κ : ι → kernel α β) : kernel.sum κ = ∑ i, κ i := by ext (a s hs);
  simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype]
#align probability_theory.kernel.sum_fintype ProbabilityTheory.kernel.sum_fintype

theorem sum_add [Countable ι] (κ η : ι → kernel α β) :
    (kernel.sum fun n => κ n + η n) = kernel.sum κ + kernel.sum η := by
  ext (a s hs)
  simp only [coe_fn_add, Pi.add_apply, sum_apply, measure.sum_apply _ hs, Pi.add_apply,
    measure.coe_add, tsum_add ENNReal.summable ENNReal.summable]
#align probability_theory.kernel.sum_add ProbabilityTheory.kernel.sum_add

end Sum

section SFinite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class ProbabilityTheory.IsSFiniteKernel (κ : kernel α β) : Prop where
  tsum_finite : ∃ κs : ℕ → kernel α β, (∀ n, IsFiniteKernel (κs n)) ∧ κ = kernel.sum κs
#align probability_theory.is_s_finite_kernel ProbabilityTheory.IsSFiniteKernel

instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by split_ifs; exact h; infer_instance, by
      ext (a s hs)
      rw [kernel.sum_apply' _ _ hs]
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 := by ext1 i;
        split_ifs <;> rfl
      rw [this, tsum_ite_eq]⟩⟩
#align probability_theory.kernel.is_finite_kernel.is_s_finite_kernel ProbabilityTheory.kernel.IsFiniteKernel.isSFiniteKernel

/-- A sequence of finite kernels such that `κ = kernel.sum (seq κ)`. See `is_finite_kernel_seq`
and `kernel_sum_seq`. -/
noncomputable def seq (κ : kernel α β) [h : IsSFiniteKernel κ] : ℕ → kernel α β :=
  h.tsum_finite.some
#align probability_theory.kernel.seq ProbabilityTheory.kernel.seq

theorem kernel_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] : kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm
#align probability_theory.kernel.kernel_sum_seq ProbabilityTheory.kernel.kernel_sum_seq

theorem measure_sum_seq (κ : kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← kernel.sum_apply, kernel_sum_seq κ]
#align probability_theory.kernel.measure_sum_seq ProbabilityTheory.kernel.measure_sum_seq

instance isFiniteKernel_seq (κ : kernel α β) [h : IsSFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n
#align probability_theory.kernel.is_finite_kernel_seq ProbabilityTheory.kernel.isFiniteKernel_seq

instance IsSFiniteKernel.add (κ η : kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) := by
  refine' ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, _⟩⟩
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η]
#align probability_theory.kernel.is_s_finite_kernel.add ProbabilityTheory.kernel.IsSFiniteKernel.add

theorem IsSFiniteKernel.finset_sum {κs : ι → kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i in I, κs i) := by
  classical
  induction' I using Finset.induction with i I hi_nmem_I h_ind h
  · rw [Finset.sum_empty]; infer_instance
  · rw [Finset.sum_insert hi_nmem_I]
    haveI : is_s_finite_kernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : is_s_finite_kernel (∑ x : ι in I, κs x) :=
      h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
    exact is_s_finite_kernel.add _ _
#align probability_theory.kernel.is_s_finite_kernel.finset_sum ProbabilityTheory.kernel.IsSFiniteKernel.finset_sum

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i m) -/
theorem isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι → kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (kernel.sum κs) := by
  let e : ℕ ≃ ι × ℕ := Denumerable.equiv₂ ℕ (ι × ℕ)
  refine' ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, _⟩⟩
  have hκ_eq : kernel.sum κs = kernel.sum fun n => kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext (a s hs) : 2
  rw [hκ_eq]
  simp_rw [kernel.sum_apply' _ _ hs]
  change (∑' (i) (m), seq (κs i) m a s) = ∑' n, (fun im : ι × ℕ => seq (κs im.fst) im.snd a s) (e n)
  rw [e.tsum_eq]
  · rw [tsum_prod' ENNReal.summable fun _ => ENNReal.summable]
  · infer_instance
#align probability_theory.kernel.is_s_finite_kernel_sum_of_denumerable ProbabilityTheory.kernel.isSFiniteKernel_sum_of_denumerable

theorem isSFiniteKernel_sum [Countable ι] {κs : ι → kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (kernel.sum κs) := by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact is_s_finite_kernel.finset_sum Finset.univ fun i _ => hκs i
  haveI : Encodable ι := Encodable.ofCountable ι
  haveI : Denumerable ι := Denumerable.ofEncodableOfInfinite ι
  exact is_s_finite_kernel_sum_of_denumerable hκs
#align probability_theory.kernel.is_s_finite_kernel_sum ProbabilityTheory.kernel.isSFiniteKernel_sum

end SFinite

section Deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
noncomputable def deterministic (f : α → β) (hf : Measurable f) : kernel α β where
  val a := Measure.dirac (f a)
  property := by
    refine' measure.measurable_of_measurable_coe _ fun s hs => _
    simp_rw [measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)
#align probability_theory.kernel.deterministic ProbabilityTheory.kernel.deterministic

theorem deterministic_apply {f : α → β} (hf : Measurable f) (a : α) :
    deterministic f hf a = Measure.dirac (f a) :=
  rfl
#align probability_theory.kernel.deterministic_apply ProbabilityTheory.kernel.deterministic_apply

theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  change measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [measure.dirac_apply' _ hs]
#align probability_theory.kernel.deterministic_apply' ProbabilityTheory.kernel.deterministic_apply'

instance isMarkovKernel_deterministic {f : α → β} (hf : Measurable f) :
    IsMarkovKernel (deterministic f hf) :=
  ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩
#align probability_theory.kernel.is_markov_kernel_deterministic ProbabilityTheory.kernel.isMarkovKernel_deterministic

theorem lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : (∫⁻ x, f x ∂kernel.deterministic g hg a) = f (g a) := by
  rw [kernel.deterministic_apply, lintegral_dirac' _ hf]
#align probability_theory.kernel.lintegral_deterministic' ProbabilityTheory.kernel.lintegral_deterministic'

@[simp]
theorem lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : (∫⁻ x, f x ∂kernel.deterministic g hg a) = f (g a) := by
  rw [kernel.deterministic_apply, lintegral_dirac (g a) f]
#align probability_theory.kernel.lintegral_deterministic ProbabilityTheory.kernel.lintegral_deterministic

theorem set_lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    (∫⁻ x in s, f x ∂kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_lintegral_dirac' hf hs]
#align probability_theory.kernel.set_lintegral_deterministic' ProbabilityTheory.kernel.set_lintegral_deterministic'

@[simp]
theorem set_lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    (∫⁻ x in s, f x ∂kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_lintegral_dirac f s]
#align probability_theory.kernel.set_lintegral_deterministic ProbabilityTheory.kernel.set_lintegral_deterministic

theorem integral_deterministic' {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) : (∫ x, f x ∂kernel.deterministic g hg a) = f (g a) := by
  rw [kernel.deterministic_apply, integral_dirac' _ _ hf]
#align probability_theory.kernel.integral_deterministic' ProbabilityTheory.kernel.integral_deterministic'

@[simp]
theorem integral_deterministic {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : (∫ x, f x ∂kernel.deterministic g hg a) = f (g a) := by
  rw [kernel.deterministic_apply, integral_dirac _ (g a)]
#align probability_theory.kernel.integral_deterministic ProbabilityTheory.kernel.integral_deterministic

theorem set_integral_deterministic' {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    (∫ x in s, f x ∂kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_integral_dirac' hf _ hs]
#align probability_theory.kernel.set_integral_deterministic' ProbabilityTheory.kernel.set_integral_deterministic'

@[simp]
theorem set_integral_deterministic {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    (∫ x in s, f x ∂kernel.deterministic g hg a) = if g a ∈ s then f (g a) else 0 := by
  rw [kernel.deterministic_apply, set_integral_dirac f _ s]
#align probability_theory.kernel.set_integral_deterministic ProbabilityTheory.kernel.set_integral_deterministic

end Deterministic

section Const

omit mα mβ

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type _) {β : Type _} [MeasurableSpace α] {mβ : MeasurableSpace β} (μβ : Measure β) :
    kernel α β where
  val _ := μβ
  property := Measure.measurable_of_measurable_coe _ fun s hs => measurable_const
#align probability_theory.kernel.const ProbabilityTheory.kernel.const

include mα mβ

theorem const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ :=
  rfl
#align probability_theory.kernel.const_apply ProbabilityTheory.kernel.const_apply

instance isFiniteKernel_const {μβ : Measure β} [hμβ : IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun a => le_rfl⟩⟩
#align probability_theory.kernel.is_finite_kernel_const ProbabilityTheory.kernel.isFiniteKernel_const

instance isMarkovKernel_const {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun a => hμβ⟩
#align probability_theory.kernel.is_markov_kernel_const ProbabilityTheory.kernel.isMarkovKernel_const

@[simp]
theorem lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} :
    (∫⁻ x, f x ∂kernel.const α μ a) = ∫⁻ x, f x ∂μ := by rw [kernel.const_apply]
#align probability_theory.kernel.lintegral_const ProbabilityTheory.kernel.lintegral_const

@[simp]
theorem set_lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} {s : Set β} :
    (∫⁻ x in s, f x ∂kernel.const α μ a) = ∫⁻ x in s, f x ∂μ := by rw [kernel.const_apply]
#align probability_theory.kernel.set_lintegral_const ProbabilityTheory.kernel.set_lintegral_const

@[simp]
theorem integral_const {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : β → E} {μ : Measure β} {a : α} : (∫ x, f x ∂kernel.const α μ a) = ∫ x, f x ∂μ := by
  rw [kernel.const_apply]
#align probability_theory.kernel.integral_const ProbabilityTheory.kernel.integral_const

@[simp]
theorem set_integral_const {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : β → E} {μ : Measure β} {a : α} {s : Set β} :
    (∫ x in s, f x ∂kernel.const α μ a) = ∫ x in s, f x ∂μ := by rw [kernel.const_apply]
#align probability_theory.kernel.set_integral_const ProbabilityTheory.kernel.set_integral_const

end Const

omit mα

/-- In a countable space with measurable singletons, every function `α → measure β` defines a
kernel. -/
def ofFunOfCountable [MeasurableSpace α] {mβ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) : kernel α β where
  val := f
  property := measurable_of_countable f
#align probability_theory.kernel.of_fun_of_countable ProbabilityTheory.kernel.ofFunOfCountable

include mα

section Restrict

variable {s t : Set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
protected noncomputable def restrict (κ : kernel α β) (hs : MeasurableSet s) : kernel α β where
  val a := (κ a).restrict s
  property := by
    refine' measure.measurable_of_measurable_coe _ fun t ht => _
    simp_rw [measure.restrict_apply ht]
    exact kernel.measurable_coe κ (ht.inter hs)
#align probability_theory.kernel.restrict ProbabilityTheory.kernel.restrict

theorem restrict_apply (κ : kernel α β) (hs : MeasurableSet s) (a : α) :
    kernel.restrict κ hs a = (κ a).restrict s :=
  rfl
#align probability_theory.kernel.restrict_apply ProbabilityTheory.kernel.restrict_apply

theorem restrict_apply' (κ : kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    kernel.restrict κ hs a t = (κ a) (t ∩ s) := by
  rw [restrict_apply κ hs a, measure.restrict_apply ht]
#align probability_theory.kernel.restrict_apply' ProbabilityTheory.kernel.restrict_apply'

@[simp]
theorem restrict_univ : kernel.restrict κ MeasurableSet.univ = κ := by ext1 a;
  rw [kernel.restrict_apply, measure.restrict_univ]
#align probability_theory.kernel.restrict_univ ProbabilityTheory.kernel.restrict_univ

@[simp]
theorem lintegral_restrict (κ : kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞) :
    (∫⁻ b, f b ∂kernel.restrict κ hs a) = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]
#align probability_theory.kernel.lintegral_restrict ProbabilityTheory.kernel.lintegral_restrict

@[simp]
theorem set_lintegral_restrict (κ : kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞)
    (t : Set β) : (∫⁻ b in t, f b ∂kernel.restrict κ hs a) = ∫⁻ b in t ∩ s, f b ∂κ a := by
  rw [restrict_apply, measure.restrict_restrict' hs]
#align probability_theory.kernel.set_lintegral_restrict ProbabilityTheory.kernel.set_lintegral_restrict

@[simp]
theorem set_integral_restrict {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {a : α} (hs : MeasurableSet s) (t : Set β) :
    (∫ x in t, f x ∂kernel.restrict κ hs a) = ∫ x in t ∩ s, f x ∂κ a := by
  rw [restrict_apply, measure.restrict_restrict' hs]
#align probability_theory.kernel.set_integral_restrict ProbabilityTheory.kernel.set_integral_restrict

instance IsFiniteKernel.restrict (κ : kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (kernel.restrict κ hs) := by
  refine' ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, fun a => _⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _
#align probability_theory.kernel.is_finite_kernel.restrict ProbabilityTheory.kernel.IsFiniteKernel.restrict

instance IsSFiniteKernel.restrict (κ : kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (kernel.restrict κ hs) := by
  refine' ⟨⟨fun n => kernel.restrict (seq κ n) hs, inferInstance, _⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]
#align probability_theory.kernel.is_s_finite_kernel.restrict ProbabilityTheory.kernel.IsSFiniteKernel.restrict

end Restrict

section ComapRight

variable {γ : Type _} {mγ : MeasurableSpace γ} {f : γ → β}

include mγ

/-- Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for a measurable set
`t : set β`, `comap_right κ hf a t = κ a (f '' t)`. -/
noncomputable def comapRight (κ : kernel α β) (hf : MeasurableEmbedding f) : kernel α γ where
  val a := (κ a).comap f
  property := by
    refine' measure.measurable_measure.mpr fun t ht => _
    have : (fun a => measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [measure.comap_apply _ hf.injective (fun s' hs' => _) _ ht]
      exact hf.measurable_set_image.mpr hs'
    rw [this]
    exact kernel.measurable_coe _ (hf.measurable_set_image.mpr ht)
#align probability_theory.kernel.comap_right ProbabilityTheory.kernel.comapRight

theorem comapRight_apply (κ : kernel α β) (hf : MeasurableEmbedding f) (a : α) :
    comapRight κ hf a = Measure.comap f (κ a) :=
  rfl
#align probability_theory.kernel.comap_right_apply ProbabilityTheory.kernel.comapRight_apply

theorem comapRight_apply' (κ : kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
    (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t) := by
  rw [comap_right_apply,
    measure.comap_apply _ hf.injective (fun s => hf.measurable_set_image.mpr) _ ht]
#align probability_theory.kernel.comap_right_apply' ProbabilityTheory.kernel.comapRight_apply'

theorem IsMarkovKernel.comapRight (κ : kernel α β) (hf : MeasurableEmbedding f)
    (hκ : ∀ a, κ a (Set.range f) = 1) : IsMarkovKernel (comapRight κ hf) := by
  refine' ⟨fun a => ⟨_⟩⟩
  rw [comap_right_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  exact hκ a
#align probability_theory.kernel.is_markov_kernel.comap_right ProbabilityTheory.kernel.IsMarkovKernel.comapRight

instance IsFiniteKernel.comapRight (κ : kernel α β) [IsFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsFiniteKernel (comapRight κ hf) := by
  refine' ⟨⟨is_finite_kernel.bound κ, is_finite_kernel.bound_lt_top κ, fun a => _⟩⟩
  rw [comap_right_apply' κ hf a MeasurableSet.univ]
  exact measure_le_bound κ a _
#align probability_theory.kernel.is_finite_kernel.comap_right ProbabilityTheory.kernel.IsFiniteKernel.comapRight

instance IsSFiniteKernel.comapRight (κ : kernel α β) [IsSFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsSFiniteKernel (comapRight κ hf) := by
  refine' ⟨⟨fun n => comap_right (seq κ n) hf, inferInstance, _⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comap_right_apply _ hf]
  have :
    (measure.sum fun n => measure.comap f (seq κ n a)) =
      measure.comap f (measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [measure.comap_apply _ hf.injective (fun s' => hf.measurable_set_image.mpr) _ ht,
      measure.sum_apply _ ht, measure.sum_apply _ (hf.measurable_set_image.mpr ht)]
    congr with n : 1
    rw [measure.comap_apply _ hf.injective (fun s' => hf.measurable_set_image.mpr) _ ht]
  rw [this, measure_sum_seq]
#align probability_theory.kernel.is_s_finite_kernel.comap_right ProbabilityTheory.kernel.IsSFiniteKernel.comapRight

end ComapRight

section Piecewise

variable {η : kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

/-- `piecewise hs κ η` is the kernel equal to `κ` on the measurable set `s` and to `η` on its
complement. -/
def piecewise (hs : MeasurableSet s) (κ η : kernel α β) : kernel α β where
  val a := if a ∈ s then κ a else η a
  property := Measurable.piecewise hs (kernel.measurable _) (kernel.measurable _)
#align probability_theory.kernel.piecewise ProbabilityTheory.kernel.piecewise

theorem piecewise_apply (a : α) : piecewise hs κ η a = if a ∈ s then κ a else η a :=
  rfl
#align probability_theory.kernel.piecewise_apply ProbabilityTheory.kernel.piecewise_apply

theorem piecewise_apply' (a : α) (t : Set β) :
    piecewise hs κ η a t = if a ∈ s then κ a t else η a t := by rw [piecewise_apply];
  split_ifs <;> rfl
#align probability_theory.kernel.piecewise_apply' ProbabilityTheory.kernel.piecewise_apply'

instance IsMarkovKernel.piecewise [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (piecewise hs κ η) := by refine' ⟨fun a => ⟨_⟩⟩;
  rw [piecewise_apply', measure_univ, measure_univ, if_t_t]
#align probability_theory.kernel.is_markov_kernel.piecewise ProbabilityTheory.kernel.IsMarkovKernel.piecewise

instance IsFiniteKernel.piecewise [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (piecewise hs κ η) := by
  refine' ⟨⟨max (is_finite_kernel.bound κ) (is_finite_kernel.bound η), _, fun a => _⟩⟩
  · exact max_lt (is_finite_kernel.bound_lt_top κ) (is_finite_kernel.bound_lt_top η)
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))
#align probability_theory.kernel.is_finite_kernel.piecewise ProbabilityTheory.kernel.IsFiniteKernel.piecewise

instance IsSFiniteKernel.piecewise [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (piecewise hs κ η) := by
  refine' ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, _⟩⟩
  ext1 a
  simp_rw [sum_apply, kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm
#align probability_theory.kernel.is_s_finite_kernel.piecewise ProbabilityTheory.kernel.IsSFiniteKernel.piecewise

theorem lintegral_piecewise (a : α) (g : β → ℝ≥0∞) :
    (∫⁻ b, g b ∂piecewise hs κ η a) = if a ∈ s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
#align probability_theory.kernel.lintegral_piecewise ProbabilityTheory.kernel.lintegral_piecewise

theorem set_lintegral_piecewise (a : α) (g : β → ℝ≥0∞) (t : Set β) :
    (∫⁻ b in t, g b ∂piecewise hs κ η a) =
      if a ∈ s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g b ∂η a :=
  by simp_rw [piecewise_apply]; split_ifs <;> rfl
#align probability_theory.kernel.set_lintegral_piecewise ProbabilityTheory.kernel.set_lintegral_piecewise

theorem integral_piecewise {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (a : α) (g : β → E) :
    (∫ b, g b ∂piecewise hs κ η a) = if a ∈ s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl
#align probability_theory.kernel.integral_piecewise ProbabilityTheory.kernel.integral_piecewise

theorem set_integral_piecewise {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a : α) (g : β → E) (t : Set β) :
    (∫ b in t, g b ∂piecewise hs κ η a) =
      if a ∈ s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a :=
  by simp_rw [piecewise_apply]; split_ifs <;> rfl
#align probability_theory.kernel.set_integral_piecewise ProbabilityTheory.kernel.set_integral_piecewise

end Piecewise

end Kernel

end ProbabilityTheory

