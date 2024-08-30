/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Markov Kernels

A kernel from a measurable space `α` to another measurable space `β` is a measurable map
`α → MeasureTheory.Measure β`, where the measurable space instance on `measure β` is the one defined
in `MeasureTheory.Measure.instMeasurableSpace`. That is, a kernel `κ` verifies that for all
measurable sets `s` of `β`, `a ↦ κ a s` is measurable.

## Main definitions

Classes of kernels:
* `ProbabilityTheory.Kernel α β`: kernels from `α` to `β`.
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
* `ProbabilityTheory.Kernel.deterministic (f : α → β) (hf : Measurable f)`:
  kernel `a ↦ Measure.dirac (f a)`.
* `ProbabilityTheory.Kernel.const α (μβ : measure β)`: constant kernel `a ↦ μβ`.
* `ProbabilityTheory.Kernel.restrict κ (hs : MeasurableSet s)`: kernel for which the image of
  `a : α` is `(κ a).restrict s`.
  Integral: `∫⁻ b, f b ∂(κ.restrict hs a) = ∫⁻ b in s, f b ∂(κ a)`

## Main statements

* `ProbabilityTheory.Kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/


open MeasureTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory

/-- A kernel from a measurable space `α` to another measurable space `β` is a measurable function
`κ : α → Measure β`. The measurable space structure on `MeasureTheory.Measure β` is given by
`MeasureTheory.Measure.instMeasurableSpace`. A map `κ : α → MeasureTheory.Measure β` is measurable
iff `∀ s : Set β, MeasurableSet s → Measurable (fun a ↦ κ a s)`. -/
structure Kernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] where
  /-- The underlying function of a kernel.

  Do not use this function directly. Instead use the coercion coming from the `DFunLike`
  instance. -/
  toFun : α → Measure β
  /-- A kernel is a measurable map.

  Do not use this lemma directly. Use `Kernel.measurable` instead. -/
  measurable' : Measurable toFun

@[deprecated (since := "2024-07-22")] alias kernel := Kernel

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Kernel[" mα "]" α:arg β:arg => @Kernel α β mα _

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain and codomain. -/
scoped notation "Kernel[" mα ", " mβ "]" α:arg β:arg => @Kernel α β mα mβ

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

instance instFunLike : FunLike (Kernel α β) α (Measure β) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

lemma measurable (κ : Kernel α β) : Measurable κ := κ.measurable'
@[simp, norm_cast] lemma coe_mk (f : α → Measure β) (hf) : mk f hf = f := rfl

initialize_simps_projections Kernel (toFun → apply)

instance instZero : Zero (Kernel α β) where zero := ⟨0, measurable_zero⟩
noncomputable instance instAdd : Add (Kernel α β) where add κ η := ⟨κ + η, κ.2.add η.2⟩
noncomputable instance instSMulNat : SMul ℕ (Kernel α β) where
  smul n κ := ⟨n • κ, (measurable_const (a := n)).smul κ.2⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : Kernel α β) = 0 := rfl
@[simp, norm_cast] lemma coe_add (κ η : Kernel α β) : ⇑(κ + η) = κ + η := rfl
@[simp, norm_cast] lemma coe_nsmul (n : ℕ) (κ : Kernel α β) : ⇑(n • κ) = n • κ := rfl

@[simp] lemma zero_apply (a : α) : (0 : Kernel α β) a = 0 := rfl
@[simp] lemma add_apply (κ η : Kernel α β) (a : α) : (κ + η) a = κ a + η a := rfl
@[simp] lemma nsmul_apply (n : ℕ) (κ : Kernel α β) (a : α) : (n • κ) a = n • κ a := rfl

noncomputable instance instAddCommMonoid : AddCommMonoid (Kernel α β) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add (by intros; rfl)

instance instPartialOrder : PartialOrder (Kernel α β) := .lift _ DFunLike.coe_injective

instance instCovariantAddLE {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    CovariantClass (Kernel α β) (Kernel α β) (· + ·) (· ≤ ·) :=
  ⟨fun _ _ _ hμ a ↦ add_le_add_left (hμ a) _⟩

noncomputable
instance instOrderBot {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    OrderBot (Kernel α β) where
  bot := 0
  bot_le κ a := by simp only [coe_zero, Pi.zero_apply, Measure.zero_le]

/-- Coercion to a function as an additive monoid homomorphism. -/
def coeAddHom (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    Kernel α β →+ α → Measure β where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coe_finset_sum (I : Finset ι) (κ : ι → Kernel α β) : ⇑(∑ i ∈ I, κ i) = ∑ i ∈ I, ⇑(κ i) :=
  map_sum (coeAddHom α β) _ _

theorem finset_sum_apply (I : Finset ι) (κ : ι → Kernel α β) (a : α) :
    (∑ i ∈ I, κ i) a = ∑ i ∈ I, κ i a := by rw [coe_finset_sum, Finset.sum_apply]

theorem finset_sum_apply' (I : Finset ι) (κ : ι → Kernel α β) (a : α) (s : Set β) :
    (∑ i ∈ I, κ i) a s = ∑ i ∈ I, κ i a s := by rw [finset_sum_apply, Measure.finset_sum_apply]

end Kernel

/-- A kernel is a Markov kernel if every measure in its image is a probability measure. -/
class IsMarkovKernel (κ : Kernel α β) : Prop where
  isProbabilityMeasure : ∀ a, IsProbabilityMeasure (κ a)

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class IsFiniteKernel (κ : Kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C

/-- A constant `C : ℝ≥0∞` such that `C < ∞` (`ProbabilityTheory.IsFiniteKernel.bound_lt_top κ`) and
for all `a : α` and `s : Set β`, `κ a s ≤ C` (`ProbabilityTheory.Kernel.measure_le_bound κ a s`).

Porting note (#11215): TODO: does it make sense to
-- make `ProbabilityTheory.IsFiniteKernel.bound` the least possible bound?
-- Should it be an `NNReal` number? -/
noncomputable def IsFiniteKernel.bound (κ : Kernel α β) [h : IsFiniteKernel κ] : ℝ≥0∞ :=
  h.exists_univ_le.choose

theorem IsFiniteKernel.bound_lt_top (κ : Kernel α β) [h : IsFiniteKernel κ] :
    IsFiniteKernel.bound κ < ∞ :=
  h.exists_univ_le.choose_spec.1

theorem IsFiniteKernel.bound_ne_top (κ : Kernel α β) [IsFiniteKernel κ] :
    IsFiniteKernel.bound κ ≠ ∞ :=
  (IsFiniteKernel.bound_lt_top κ).ne

theorem Kernel.measure_le_bound (κ : Kernel α β) [h : IsFiniteKernel κ] (a : α) (s : Set β) :
    κ a s ≤ IsFiniteKernel.bound κ :=
  (measure_mono (Set.subset_univ s)).trans (h.exists_univ_le.choose_spec.2 a)

instance isFiniteKernel_zero (α β : Type*) {mα : MeasurableSpace α} {mβ : MeasurableSpace β} :
    IsFiniteKernel (0 : Kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun _ => by
      simp only [Kernel.zero_apply, Measure.coe_zero, Pi.zero_apply, le_zero_iff]⟩⟩

instance IsFiniteKernel.add (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine ⟨⟨IsFiniteKernel.bound κ + IsFiniteKernel.bound η,
    ENNReal.add_lt_top.mpr ⟨IsFiniteKernel.bound_lt_top κ, IsFiniteKernel.bound_lt_top η⟩,
    fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)

lemma isFiniteKernel_of_le {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ ≤ ν) :
    IsFiniteKernel κ := by
  refine ⟨hν.bound, hν.bound_lt_top, fun a ↦ (hκν _ _).trans (Kernel.measure_le_bound ν a Set.univ)⟩

variable {κ : Kernel α β}

instance IsMarkovKernel.is_probability_measure' [IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a

instance IsFiniteKernel.isFiniteMeasure [IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(Kernel.measure_le_bound κ a Set.univ).trans_lt (IsFiniteKernel.bound_lt_top κ)⟩

instance (priority := 100) IsMarkovKernel.isFiniteKernel [IsMarkovKernel κ] :
    IsFiniteKernel κ :=
  ⟨⟨1, ENNReal.one_lt_top, fun _ => prob_le_one⟩⟩

namespace Kernel

@[ext]
theorem ext {η : Kernel α β} (h : ∀ a, κ a = η a) : κ = η := DFunLike.ext _ _ h

theorem ext_iff' {η : Kernel α β} :
    κ = η ↔ ∀ a s, MeasurableSet s → κ a s = η a s := by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]

theorem ext_fun {η : Kernel α β} (h : ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]

theorem ext_fun_iff {η : Kernel α β} :
    κ = η ↔ ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f _ => by rw [h], ext_fun⟩

protected theorem measurable_coe (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp κ.measurable

lemma apply_congr_of_mem_measurableAtom (κ : Kernel α β) {y' y : α} (hy' : y' ∈ measurableAtom y) :
    κ y' = κ y := by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl

lemma IsFiniteKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsFiniteKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x s).toReal) μ := by
  refine Integrable.mono' (integrable_const (IsFiniteKernel.bound κ).toReal)
    ((κ.measurable_coe hs).ennreal_toReal.aestronglyMeasurable)
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (IsFiniteKernel.bound_ne_top _)]
  exact Kernel.measure_le_bound _ _ _

lemma IsMarkovKernel.integrable (μ : Measure α) [IsFiniteMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun x => (κ x s).toReal) μ :=
  IsFiniteKernel.integrable μ κ hs

lemma integral_congr_ae₂ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : α → β → E}
    {μ : Measure α} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with _ ha
  apply integral_congr_ae
  filter_upwards [ha] with _ hb using hb

section Sum

/-- Sum of an indexed family of kernels. -/
protected noncomputable def sum [Countable ι] (κ : ι → Kernel α β) : Kernel α β where
  toFun a := Measure.sum fun n => κ n a
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sum_apply _ hs]
    exact Measurable.ennreal_tsum fun n => Kernel.measurable_coe (κ n) hs

theorem sum_apply [Countable ι] (κ : ι → Kernel α β) (a : α) :
    Kernel.sum κ a = Measure.sum fun n => κ n a :=
  rfl

theorem sum_apply' [Countable ι] (κ : ι → Kernel α β) (a : α) {s : Set β} (hs : MeasurableSet s) :
    Kernel.sum κ a s = ∑' n, κ n a s := by rw [sum_apply κ a, Measure.sum_apply _ hs]

@[simp]
theorem sum_zero [Countable ι] : (Kernel.sum fun _ : ι => (0 : Kernel α β)) = 0 := by
  ext a s hs
  rw [sum_apply' _ a hs]
  simp only [zero_apply, Measure.coe_zero, Pi.zero_apply, tsum_zero]

theorem sum_comm [Countable ι] (κ : ι → ι → Kernel α β) :
    (Kernel.sum fun n => Kernel.sum (κ n)) = Kernel.sum fun m => Kernel.sum fun n => κ n m := by
  ext a s; simp_rw [sum_apply]; rw [Measure.sum_comm]

@[simp]
theorem sum_fintype [Fintype ι] (κ : ι → Kernel α β) : Kernel.sum κ = ∑ i, κ i := by
  ext a s hs
  simp only [sum_apply' κ a hs, finset_sum_apply' _ κ a s, tsum_fintype]

theorem sum_add [Countable ι] (κ η : ι → Kernel α β) :
    (Kernel.sum fun n => κ n + η n) = Kernel.sum κ + Kernel.sum η := by
  ext a s hs
  simp only [coe_add, Pi.add_apply, sum_apply, Measure.sum_apply _ hs, Pi.add_apply,
    Measure.coe_add, tsum_add ENNReal.summable ENNReal.summable]

end Sum

section SFinite

/-- A kernel is s-finite if it can be written as the sum of countably many finite kernels. -/
class _root_.ProbabilityTheory.IsSFiniteKernel (κ : Kernel α β) : Prop where
  tsum_finite : ∃ κs : ℕ → Kernel α β, (∀ n, IsFiniteKernel (κs n)) ∧ κ = Kernel.sum κs

instance (priority := 100) IsFiniteKernel.isSFiniteKernel [h : IsFiniteKernel κ] :
    IsSFiniteKernel κ :=
  ⟨⟨fun n => if n = 0 then κ else 0, fun n => by
      simp only; split_ifs
      · exact h
      · infer_instance, by
      ext a s hs
      rw [Kernel.sum_apply' _ _ hs]
      have : (fun i => ((ite (i = 0) κ 0) a) s) = fun i => ite (i = 0) (κ a s) 0 := by
        ext1 i; split_ifs <;> rfl
      rw [this, tsum_ite_eq]⟩⟩

/-- A sequence of finite kernels such that `κ = ProbabilityTheory.Kernel.sum (seq κ)`. See
`ProbabilityTheory.Kernel.isFiniteKernel_seq` and `ProbabilityTheory.Kernel.kernel_sum_seq`. -/
noncomputable def seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : ℕ → Kernel α β :=
  h.tsum_finite.choose

theorem kernel_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] : Kernel.sum (seq κ) = κ :=
  h.tsum_finite.choose_spec.2.symm

theorem measure_sum_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (a : α) :
    (Measure.sum fun n => seq κ n a) = κ a := by rw [← Kernel.sum_apply, kernel_sum_seq κ]

instance isFiniteKernel_seq (κ : Kernel α β) [h : IsSFiniteKernel κ] (n : ℕ) :
    IsFiniteKernel (Kernel.seq κ n) :=
  h.tsum_finite.choose_spec.1 n

instance _root_.ProbabilityTheory.IsSFiniteKernel.sFinite [IsSFiniteKernel κ] (a : α) :
    SFinite (κ a) :=
  ⟨⟨fun n ↦ seq κ n a, inferInstance, (measure_sum_seq κ a).symm⟩⟩

instance IsSFiniteKernel.add (κ η : Kernel α β) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    IsSFiniteKernel (κ + η) := by
  refine ⟨⟨fun n => seq κ n + seq η n, fun n => inferInstance, ?_⟩⟩
  rw [sum_add, kernel_sum_seq κ, kernel_sum_seq η]

theorem IsSFiniteKernel.finset_sum {κs : ι → Kernel α β} (I : Finset ι)
    (h : ∀ i ∈ I, IsSFiniteKernel (κs i)) : IsSFiniteKernel (∑ i ∈ I, κs i) := by
  classical
  induction' I using Finset.induction with i I hi_nmem_I h_ind h
  · rw [Finset.sum_empty]; infer_instance
  · rw [Finset.sum_insert hi_nmem_I]
    haveI : IsSFiniteKernel (κs i) := h i (Finset.mem_insert_self _ _)
    have : IsSFiniteKernel (∑ x ∈ I, κs x) :=
      h_ind fun i hiI => h i (Finset.mem_insert_of_mem hiI)
    exact IsSFiniteKernel.add _ _

theorem isSFiniteKernel_sum_of_denumerable [Denumerable ι] {κs : ι → Kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel.sum κs) := by
  let e : ℕ ≃ ι × ℕ := (Denumerable.eqv (ι × ℕ)).symm
  refine ⟨⟨fun n => seq (κs (e n).1) (e n).2, inferInstance, ?_⟩⟩
  have hκ_eq : Kernel.sum κs = Kernel.sum fun n => Kernel.sum (seq (κs n)) := by
    simp_rw [kernel_sum_seq]
  ext a s hs
  rw [hκ_eq]
  simp_rw [Kernel.sum_apply' _ _ hs]
  change (∑' i, ∑' m, seq (κs i) m a s) = ∑' n, (fun im : ι × ℕ => seq (κs im.fst) im.snd a s) (e n)
  rw [e.tsum_eq (fun im : ι × ℕ => seq (κs im.fst) im.snd a s),
    tsum_prod' ENNReal.summable fun _ => ENNReal.summable]

theorem isSFiniteKernel_sum [Countable ι] {κs : ι → Kernel α β}
    (hκs : ∀ n, IsSFiniteKernel (κs n)) : IsSFiniteKernel (Kernel.sum κs) := by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finset_sum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

end SFinite

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

@[deprecated (since := "2024-06-29")]
alias set_lintegral_deterministic' := setLIntegral_deterministic'

@[simp]
theorem setLIntegral_deterministic {f : β → ℝ≥0∞} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫⁻ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setLIntegral_dirac f s]

@[deprecated (since := "2024-06-29")]
alias set_lintegral_deterministic := setLIntegral_deterministic

theorem integral_deterministic' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) : ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac' _ _ hf]

@[simp]
theorem integral_deterministic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] : ∫ x, f x ∂deterministic g hg a = f (g a) := by
  rw [deterministic_apply, integral_dirac _ (g a)]

theorem setIntegral_deterministic' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    (hf : StronglyMeasurable f) {s : Set β} (hs : MeasurableSet s) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac' hf _ hs]

@[deprecated (since := "2024-04-17")]
alias set_integral_deterministic' := setIntegral_deterministic'

@[simp]
theorem setIntegral_deterministic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : β → E} {g : α → β} {a : α} (hg : Measurable g)
    [MeasurableSingletonClass β] (s : Set β) [Decidable (g a ∈ s)] :
    ∫ x in s, f x ∂deterministic g hg a = if g a ∈ s then f (g a) else 0 := by
  rw [deterministic_apply, setIntegral_dirac f _ s]

@[deprecated (since := "2024-04-17")]
alias set_integral_deterministic := setIntegral_deterministic

end Deterministic

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
    Kernel.sum (fun n ↦ const α (μ n)) = const α (Measure.sum μ) := by
  ext x s hs
  rw [const_apply, Measure.sum_apply _ hs, Kernel.sum_apply' _ _ hs]
  simp only [const_apply]

instance const.instIsFiniteKernel {μβ : Measure β} [IsFiniteMeasure μβ] :
    IsFiniteKernel (const α μβ) :=
  ⟨⟨μβ Set.univ, measure_lt_top _ _, fun _ => le_rfl⟩⟩

instance const.instIsSFiniteKernel {μβ : Measure β} [SFinite μβ] :
    IsSFiniteKernel (const α μβ) :=
  ⟨fun n ↦ const α (sFiniteSeq μβ n), fun n ↦ inferInstance, by rw [sum_const, sum_sFiniteSeq]⟩

instance const.instIsMarkovKernel {μβ : Measure β} [hμβ : IsProbabilityMeasure μβ] :
    IsMarkovKernel (const α μβ) :=
  ⟨fun _ => hμβ⟩

lemma isSFiniteKernel_const [Nonempty α] {μβ : Measure β} :
    IsSFiniteKernel (const α μβ) ↔ SFinite μβ :=
  ⟨fun h ↦ h.sFinite (Classical.arbitrary α), fun _ ↦ inferInstance⟩

@[simp]
theorem lintegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} :
    ∫⁻ x, f x ∂const α μ a = ∫⁻ x, f x ∂μ := by rw [const_apply]

@[simp]
theorem setLIntegral_const {f : β → ℝ≥0∞} {μ : Measure β} {a : α} {s : Set β} :
    ∫⁻ x in s, f x ∂const α μ a = ∫⁻ x in s, f x ∂μ := by rw [const_apply]

@[deprecated (since := "2024-06-29")]
alias set_lintegral_const := setLIntegral_const

@[simp]
theorem integral_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {μ : Measure β} {a : α} : ∫ x, f x ∂const α μ a = ∫ x, f x ∂μ := by
  rw [const_apply]

@[simp]
theorem setIntegral_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {μ : Measure β} {a : α} {s : Set β} :
    ∫ x in s, f x ∂const α μ a = ∫ x in s, f x ∂μ := by rw [const_apply]

@[deprecated (since := "2024-04-17")]
alias set_integral_const := setIntegral_const

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

@[deprecated (since := "2024-06-29")]
alias set_lintegral_restrict := setLIntegral_restrict

@[simp]
theorem setIntegral_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {a : α} (hs : MeasurableSet s) (t : Set β) :
    ∫ x in t, f x ∂κ.restrict hs a = ∫ x in t ∩ s, f x ∂κ a := by
  rw [restrict_apply, Measure.restrict_restrict' hs]

@[deprecated (since := "2024-04-17")]
alias set_integral_restrict := setIntegral_restrict

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

@[deprecated (since := "2024-06-29")]
alias set_lintegral_piecewise := setLIntegral_piecewise

theorem integral_piecewise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : α) (g : β → E) :
    ∫ b, g b ∂piecewise hs κ η a = if a ∈ s then ∫ b, g b ∂κ a else ∫ b, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

theorem setIntegral_piecewise {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : α) (g : β → E) (t : Set β) :
    ∫ b in t, g b ∂piecewise hs κ η a =
      if a ∈ s then ∫ b in t, g b ∂κ a else ∫ b in t, g b ∂η a := by
  simp_rw [piecewise_apply]; split_ifs <;> rfl

@[deprecated (since := "2024-04-17")]
alias set_integral_piecewise := setIntegral_piecewise

end Piecewise
end Kernel
end ProbabilityTheory
