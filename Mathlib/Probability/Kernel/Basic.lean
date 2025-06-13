/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Defs

/-!
# Basic kernels

This file contains basic results about kernels in general and definitions of some particular
kernels.

## Main definitions

* `ProbabilityTheory.Kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.Kernel.id`: the identity kernel, deterministic kernel for
  the identity function.
* `ProbabilityTheory.Kernel.copy α`: the deterministic kernel that maps `x : α` to
  the Dirac measure at `(x, x) : α × α`.
* `ProbabilityTheory.Kernel.discard α`: the Markov kernel to the type `Unit`.
* `ProbabilityTheory.Kernel.swap α β`: the deterministic kernel that maps `(x, y)` to
  the Dirac measure at `(y, x)`.
* `ProbabilityTheory.Kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.Kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(κ.restrict hs a) = ∫⁻ b in s, f b ∂(κ a)`
* `ProbabilityTheory.Kernel.comapRight`: Kernel with value `(κ a).comap f`,
  for a measurable embedding `f`. That is, for a measurable set `t : Set β`,
  `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`
* `ProbabilityTheory.Kernel.piecewise (hs : MeasurableSet s) κ η`: the kernel equal to `κ`
  on the measurable set `s` and to `η` on its complement.

## Main statements

-/

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Kernel α β}

namespace Kernel

section Deterministic

/-- Kernel which to `a` associates the dirac measure at `f a`. This is a Markov kernel. -/
noncomputable def deterministic (f : α → β) (hf : Measurable f) : Kernel α β where
  toFun a := Measure.dirac (f a)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.dirac_apply' _ hs]
    exact measurable_one.indicator (hf hs)

theorem deterministic_apply {f : α → β} (hf : Measurable f) (a : α) :
    deterministic f hf a = Measure.dirac (f a) :=
  rfl

theorem deterministic_apply' {f : α → β} (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) : deterministic f hf a s = s.indicator (fun _ => 1) (f a) := by
  rw [deterministic]
  change Measure.dirac (f a) s = s.indicator 1 (f a)
  simp_rw [Measure.dirac_apply' _ hs]

/-- Because of the measurability field in `Kernel.deterministic`, `rw [h]` will not rewrite
`deterministic f hf` to `deterministic g ⋯`. Instead one can do `rw [deterministic_congr h]`. -/
theorem deterministic_congr {f g : α → β} {hf : Measurable f} (h : f = g) :
    deterministic f hf = deterministic g (h ▸ hf) := by
  conv_lhs => enter [1]; rw [h]

instance isMarkovKernel_deterministic {f : α → β} (hf : Measurable f) :
    IsMarkovKernel (deterministic f hf) :=
  ⟨fun a => by rw [deterministic_apply hf]; infer_instance⟩

theorem lintegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, lintegral_dirac' _ hf]

@[simp]
theorem lintegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫⁻ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, lintegral_dirac (g a) f]

theorem setLIntegral_deterministic' {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setLIntegral_dirac' hf hs]

@[simp]
theorem setLIntegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setLIntegral_dirac f s]

end Deterministic

section Id

/-- The identity kernel, that maps `x : α` to the Dirac measure at `x`. -/
protected noncomputable
def id : Kernel α α := Kernel.deterministic id measurable_id

instance : IsMarkovKernel (Kernel.id : Kernel α α) := by rw [Kernel.id]; infer_instance

lemma id_apply (a : α) : Kernel.id a = Measure.dirac a := by
  rw [Kernel.id, deterministic_apply, id_def]

lemma lintegral_id' {f : α → ℝ≥0∞} (hf : Measurable f) (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply, lintegral_dirac' _ hf]

lemma lintegral_id [MeasurableSingletonClass α] {f : α → ℝ≥0∞} (a : α) :
    ∫⁻ a, f a ∂(@Kernel.id α mα a) = f a := by
  rw [id_apply, lintegral_dirac]

end Id

section Copy

/-- The deterministic kernel that maps `x : α` to the Dirac measure at `(x, x) : α × α`. -/
noncomputable
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) :=
  Kernel.deterministic (fun x ↦ (x, x)) (measurable_id.prod measurable_id)

instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance

lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by simp [copy, deterministic_apply]

end Copy

section Discard

/-- The Markov kernel to the `Unit` type. -/
noncomputable
def discard (α : Type*) [MeasurableSpace α] : Kernel α Unit :=
  Kernel.deterministic (fun _ ↦ ()) measurable_const

instance : IsMarkovKernel (discard α) := by rw [discard]; infer_instance

@[simp]
lemma discard_apply (a : α) : discard α a = Measure.dirac () := deterministic_apply _ _

end Discard

section Swap

/-- The deterministic kernel that maps `(x, y)` to the Dirac measure at `(y, x)`. -/
noncomputable
def swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap

instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

/-- See `swap_apply'` for a fully applied version of this lemma. -/
lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap, deterministic_apply]

/-- See `swap_apply` for a partially applied version of this lemma. -/
lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply, Measure.dirac_apply' _ hs]

end Swap

section Const

/-- Constant kernel, which always returns the same measure. -/
def const (α : Type*) {β : Type*} [MeasurableSpace α] {_ : MeasurableSpace β} (μβ : Measure β) :
    Kernel α β where
  toFun _ := μβ
  measurable' := measurable_const

@[simp]
theorem const_apply (μβ : Measure β) (a : α) : const α μβ a = μβ :=
  rfl

@[simp]
lemma const_zero : const α (0 : Measure β) = 0 := by
  ext x s _; simp [const_apply]

lemma const_add (β : Type*) [MeasurableSpace β] (μ ν : Measure α) :
    const β (μ + ν) = const β μ + const β ν := by ext; simp

lemma sum_const [Countable ι] (μ : ι → Measure β) :
    Kernel.sum (fun n ↦ const α (μ n)) = const α (Measure.sum μ) := rfl

instance const.instIsFiniteKernel {μβ : Measure β} [IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩

instance const.instIsSFiniteKernel {μβ : Measure β} [SFinite μβ] :
    IsSFiniteKernel (const α μβ) :=
  ⟨fun n ↦ const α (sfiniteSeq μβ n), fun n ↦ inferInstance, by rw [sum_const, sum_sfiniteSeq]⟩

instance const.instIsMarkovKernel {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun _ => hμβ⟩

instance const.instIsZeroOrMarkovKernel {μβ : Measure β} [hμβ : IsZeroOrProbabilityMeasure μβ] :
    IsZeroOrMarkovKernel (const α μβ) := by
  rcases eq_zero_or_isProbabilityMeasure μβ with rfl | h
  · simp only [const_zero]
    infer_instance
  · infer_instance

lemma isSFiniteKernel_const [Nonempty α] {μβ : Measure β} :
    IsSFiniteKernel (const α μβ) ↔ SFinite μβ :=
  ⟨fun h ↦ h.sFinite (Classical.arbitrary α), fun _ ↦ inferInstance⟩

@[simp]
theorem lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} :
    ∫⁻ x, f x ∂const α μ a = ∫⁻ x, f x ∂μ := by rw [const_apply]

@[simp]
theorem setLIntegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} {s : Set β} :
    ∫⁻ x in s, f x ∂const α μ a = ∫⁻ x in s, f x ∂μ := by rw [const_apply]

end Const

/-- In a countable space with measurable singletons, every function `α → MeasureTheory.Measure β`
defines a kernel. -/
def ofFunOfCountable [MeasurableSpace α] {_ : MeasurableSpace β} [Countable α]
    [MeasurableSingletonClass α] (f : α → Measure β) : Kernel α β where
  toFun := f
  measurable' := measurable_of_countable f

section Restrict

variable {s t : Set β}

/-- Kernel given by the restriction of the measures in the image of a kernel to a set. -/
protected noncomputable def restrict (κ : Kernel α β) (hs : MeasurableSet s) : Kernel α β where
  toFun a := (κ a).restrict s
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    simp_rw [Measure.restrict_apply ht]
    exact Kernel.measurable_coe κ (ht.inter hs)

theorem restrict_apply (κ : Kernel α β) (hs : MeasurableSet s) (a : α) :
    κ.restrict hs a = (κ a).restrict s :=
  rfl

theorem restrict_apply' (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (ht : MeasurableSet t) :
    κ.restrict hs a t = (κ a) (t ∩ s) := by
  rw [restrict_apply κ hs a, Measure.restrict_apply ht]

@[simp]
theorem restrict_univ : κ.restrict MeasurableSet.univ = κ := by
  ext1 a
  rw [Kernel.restrict_apply, Measure.restrict_univ]

@[simp]
theorem lintegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞) :
    ∫⁻ b, f b ∂κ.restrict hs a = ∫⁻ b in s, f b ∂κ a := by rw [restrict_apply]

@[simp]
theorem setLIntegral_restrict (κ : Kernel α β) (hs : MeasurableSet s) (a : α) (f : β → ℝ≥0∞)
    (t : Set β) : ∫⁻ b in t, f b ∂κ.restrict hs a = ∫⁻ b in t ∩ s, f b ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]


instance IsFiniteKernel.restrict (κ : Kernel α β) [IsFiniteKernel κ] (hs : MeasurableSet s) :
    IsFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  rw [restrict_apply' κ hs a MeasurableSet.univ]
  exact measure_le_bound κ a _

instance IsSFiniteKernel.restrict (κ : Kernel α β) [IsSFiniteKernel κ] (hs : MeasurableSet s) :
    IsSFiniteKernel (κ.restrict hs) := by
  refine ⟨⟨fun n => Kernel.restrict (seq κ n) hs, inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, restrict_apply, ← Measure.restrict_sum _ hs, ← sum_apply, kernel_sum_seq]

end Restrict

section ComapRight

variable {γ : Type*} {mγ : MeasurableSpace γ} {f : γ → β}

/-- Kernel with value `(κ a).comap f`, for a measurable embedding `f`. That is, for a measurable set
`t : Set β`, `ProbabilityTheory.Kernel.comapRight κ hf a t = κ a (f '' t)`. -/
noncomputable def comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f) : Kernel α γ where
  toFun a := (κ a).comap f
  measurable' := by
    refine Measure.measurable_measure.mpr fun t ht => ?_
    have : (fun a => Measure.comap f (κ a) t) = fun a => κ a (f '' t) := by
      ext1 a
      rw [Measure.comap_apply _ hf.injective _ _ ht]
      exact fun s' hs' ↦ hf.measurableSet_image.mpr hs'
    rw [this]
    exact Kernel.measurable_coe _ (hf.measurableSet_image.mpr ht)

theorem comapRight_apply (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) :
    comapRight κ hf a = Measure.comap f (κ a) :=
  rfl

theorem comapRight_apply' (κ : Kernel α β) (hf : MeasurableEmbedding f) (a : α) {t : Set γ}
    (ht : MeasurableSet t) : comapRight κ hf a t = κ a (f '' t) := by
  rw [comapRight_apply,
    Measure.comap_apply _ hf.injective (fun s => hf.measurableSet_image.mpr) _ ht]

@[simp]
lemma comapRight_id (κ : Kernel α β) : comapRight κ MeasurableEmbedding.id = κ := by
  ext _ _ hs; rw [comapRight_apply' _ _ _ hs]; simp

theorem IsMarkovKernel.comapRight (κ : Kernel α β) (hf : MeasurableEmbedding f)
    (hκ : ∀ a, κ a (Set.range f) = 1) : IsMarkovKernel (comapRight κ hf) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [comapRight_apply' κ hf a MeasurableSet.univ]
  simp only [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq]
  exact hκ a

instance IsFiniteKernel.comapRight (κ : Kernel α β) [IsFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨IsFiniteKernel.bound κ, IsFiniteKernel.bound_lt_top κ, fun a => ?_⟩⟩
  rw [comapRight_apply' κ hf a .univ]
  exact measure_le_bound κ a _

protected instance IsSFiniteKernel.comapRight (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : MeasurableEmbedding f) : IsSFiniteKernel (comapRight κ hf) := by
  refine ⟨⟨fun n => comapRight (seq κ n) hf, inferInstance, ?_⟩⟩
  ext1 a
  rw [sum_apply]
  simp_rw [comapRight_apply _ hf]
  have :
    (Measure.sum fun n => Measure.comap f (seq κ n a)) =
      Measure.comap f (Measure.sum fun n => seq κ n a) := by
    ext1 t ht
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht,
      Measure.sum_apply _ ht, Measure.sum_apply _ (hf.measurableSet_image.mpr ht)]
    congr with n : 1
    rw [Measure.comap_apply _ hf.injective (fun s' => hf.measurableSet_image.mpr) _ ht]
  rw [this, measure_sum_seq]

end ComapRight

section Piecewise

variable {η : Kernel α β} {s : Set α} {hs : MeasurableSet s} [DecidablePred (· ∈ s)]

/-- `ProbabilityTheory.Kernel.piecewise hs κ η` is the kernel equal to `κ` on the measurable set `s`
and to `η` on its complement. -/
def piecewise (hs : MeasurableSet s) (κ η : Kernel α β) : Kernel α β where
  toFun a := if a ∈ s then κ a else η a
  measurable' := κ.measurable.piecewise hs η.measurable

theorem piecewise_apply (a : α) : piecewise hs κ η a = if a ∈ s then κ a else η a :=
  rfl

theorem piecewise_apply' (a : α) (t : Set β) :
    piecewise hs κ η a t = if a ∈ s then κ a t else η a t := by
  rw [piecewise_apply]; split_ifs <;> rfl

instance IsMarkovKernel.piecewise [IsMarkovKernel κ] [IsMarkovKernel η] :
    IsMarkovKernel (piecewise hs κ η) := by
  refine ⟨fun a => ⟨?_⟩⟩
  rw [piecewise_apply', measure_univ, measure_univ, ite_self]

instance IsFiniteKernel.piecewise [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨max (IsFiniteKernel.bound κ) (IsFiniteKernel.bound η), ?_, fun a => ?_⟩⟩
  · exact max_lt (IsFiniteKernel.bound_lt_top κ) (IsFiniteKernel.bound_lt_top η)
  rw [piecewise_apply']
  exact (ite_le_sup _ _ _).trans (sup_le_sup (measure_le_bound _ _ _) (measure_le_bound _ _ _))

protected instance IsSFiniteKernel.piecewise [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (piecewise hs κ η) := by
  refine ⟨⟨fun n => piecewise hs (seq κ n) (seq η n), inferInstance, ?_⟩⟩
  ext1 a
  simp_rw [sum_apply, Kernel.piecewise_apply]
  split_ifs <;> exact (measure_sum_seq _ a).symm

theorem lintegral_piecewise (a : α) (g : β → ℝ≥0∞) :
    ∫⁻ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫⁻ b, g b ∂κ a else ∫⁻ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

theorem setLIntegral_piecewise (a : α) (g : β → ℝ≥0∞) (t : Set β) :
    ∫⁻ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫⁻ b in t, g b ∂κ a else ∫⁻ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

end Piecewise

lemma exists_ae_eq_isMarkovKernel {μ : Measure α}
    (h : ∀ᵐ a ∂μ, IsProbabilityMeasure (κ a)) (h' : μ ≠ 0) :
    ∃ (η : Kernel α β), (κ =ᵐ[μ] η) ∧ IsMarkovKernel η := by
  classical
  obtain ⟨s, s_meas, μs, hs⟩ : ∃ s, MeasurableSet s ∧ μ s = 0
      ∧ ∀ a ∉ s, IsProbabilityMeasure (κ a) := by
    refine ⟨toMeasurable μ {a | ¬ IsProbabilityMeasure (κ a)}, measurableSet_toMeasurable _ _,
      by simpa [measure_toMeasurable] using h, ?_⟩
    intro a ha
    contrapose! ha
    exact subset_toMeasurable _ _ ha
  obtain ⟨a, ha⟩ : sᶜ.Nonempty := by
    contrapose! h'; simpa [μs, h'] using measure_univ_le_add_compl s (μ := μ)
  refine ⟨Kernel.piecewise s_meas (Kernel.const _ (κ a)) κ, ?_, ?_⟩
  · filter_upwards [measure_zero_iff_ae_notMem.1 μs] with b hb
    simp [hb, piecewise]
  · refine ⟨fun b ↦ ?_⟩
    by_cases hb : b ∈ s
    · simpa [hb, piecewise] using hs _ ha
    · simpa [hb, piecewise] using hs _ hb

end Kernel
end ProbabilityTheory
