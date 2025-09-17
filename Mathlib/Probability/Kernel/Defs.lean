/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
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
* `ProbabilityTheory.IsZeroOrMarkovKernel κ`: a kernel from `α` to `β` which is zero or
  a Markov kernel.
* `ProbabilityTheory.IsFiniteKernel κ`: a kernel from `α` to `β` is said to be finite if there
  exists `C : ℝ≥0∞` such that `C < ∞` and for all `a : α`, `κ a univ ≤ C`. This implies in
  particular that all measures in the image of `κ` are finite, but is stronger since it requires a
  uniform bound. This stronger condition is necessary to ensure that the composition of two finite
  kernels is finite.
* `ProbabilityTheory.IsSFiniteKernel κ`: a kernel is called s-finite if it is a countable
  sum of finite kernels.

## Main statements

* `ProbabilityTheory.Kernel.ext_fun`: if `∫⁻ b, f b ∂(κ a) = ∫⁻ b, f b ∂(η a)` for all measurable
  functions `f` and all `a`, then the two kernels `κ` and `η` are equal.

-/

assert_not_exists MeasureTheory.integral

open MeasureTheory

open scoped ENNReal

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

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Kernel[" mα "] " α:arg β:arg => @Kernel α β mα _

/-- Notation for `Kernel` with respect to a non-standard σ-algebra in the domain and codomain. -/
scoped notation "Kernel[" mα ", " mβ "] " α:arg β:arg => @Kernel α β mα mβ

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

instance instFunLike : FunLike (Kernel α β) α (Measure β) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr

@[fun_prop]
lemma measurable (κ : Kernel α β) : Measurable κ := κ.measurable'

lemma aemeasurable (κ : Kernel α β) {μ : Measure α} : AEMeasurable κ μ := κ.measurable.aemeasurable

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

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    AddLeftMono (Kernel α β) :=
  ⟨fun _ _ _ hμ a ↦ add_le_add_left (hμ a) _⟩

noncomputable
instance instOrderBot {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    OrderBot (Kernel α β) where
  bot := 0
  bot_le κ a := by simp only [coe_zero, Pi.zero_apply, Measure.zero_le]

/-- Coercion to a function as an additive monoid homomorphism. -/
noncomputable def coeAddHom (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] :
    Kernel α β →+ α → Measure β where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] (κ : Kernel α β) :
    coeAddHom α β κ = ⇑κ := rfl

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

/-- A class for kernels which are zero or a Markov kernel. -/
class IsZeroOrMarkovKernel (κ : Kernel α β) : Prop where
  eq_zero_or_isMarkovKernel' : κ = 0 ∨ IsMarkovKernel κ

/-- A kernel is finite if every measure in its image is finite, with a uniform bound. -/
class IsFiniteKernel (κ : Kernel α β) : Prop where
  exists_univ_le : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ a, κ a Set.univ ≤ C

theorem eq_zero_or_isMarkovKernel
    (κ : Kernel α β) [h : IsZeroOrMarkovKernel κ] :
    κ = 0 ∨ IsMarkovKernel κ :=
  h.eq_zero_or_isMarkovKernel'

/-- A constant `C : ℝ≥0∞` such that `C < ∞` for a finite kernel
(`ProbabilityTheory.IsFiniteKernel.bound_lt_top κ`) and for all `a : α` and `s : Set β`,
`κ a s ≤ C` (`ProbabilityTheory.Kernel.measure_le_bound κ a s`). -/
noncomputable def Kernel.bound (κ : Kernel α β) : ℝ≥0∞ :=
  ⨆ a, κ a Set.univ

@[deprecated (since := "2025-09-13")] alias IsFiniteKernel.bound := Kernel.bound

namespace Kernel

theorem bound_lt_top (κ : Kernel α β) [h : IsFiniteKernel κ] : κ.bound < ∞ := by
  obtain ⟨C, hC, hle⟩ := h.exists_univ_le
  refine lt_of_le_of_lt ?_ hC
  simp [bound, hle]

@[deprecated (since := "2025-09-13")] alias _root_.ProbabilityTheory.IsFiniteKernel.bound_lt_top :=
  bound_lt_top

theorem bound_ne_top (κ : Kernel α β) [IsFiniteKernel κ] :
    κ.bound ≠ ∞ := κ.bound_lt_top.ne

@[deprecated (since := "2025-09-13")] alias _root_.ProbabilityTheory.IsFiniteKernel.bound_ne_top :=
  bound_ne_top

theorem measure_le_bound (κ : Kernel α β) (a : α) (s : Set β) :
    κ a s ≤ κ.bound :=
  (measure_mono (Set.subset_univ s)).trans <| le_iSup (f := fun a ↦ κ a .univ) a

@[simp]
lemma bound_eq_zero_of_isEmpty [IsEmpty α] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound]

@[deprecated (since := "2025-09-13")] alias
  _root_.ProbabilityTheory.IsFiniteKernel.bound_eq_zero_of_isEmpty := bound_eq_zero_of_isEmpty

@[simp]
lemma bound_eq_zero_of_isEmpty' [IsEmpty β] (κ : Kernel α β) :
    κ.bound = 0 := by simp [bound, Subsingleton.elim _ (0 : Measure β)]

@[deprecated (since := "2025-09-13")] alias
  _root_.ProbabilityTheory.IsFiniteKernel.bound_eq_zero_of_isEmpty' := bound_eq_zero_of_isEmpty'

@[simp]
lemma bound_zero : bound (0 : Kernel α β) = 0 := by
  simp [bound]

@[deprecated (since := "2025-09-13")] alias
  _root_.ProbabilityTheory.IsFiniteKernel.bound_zero := bound_zero

end Kernel

instance isFiniteKernel_zero (α β : Type*) {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    IsFiniteKernel (0 : Kernel α β) :=
  ⟨⟨0, ENNReal.coe_lt_top, fun _ => by
      simp only [Kernel.zero_apply, Measure.coe_zero, Pi.zero_apply, le_zero_iff]⟩⟩

instance IsFiniteKernel.add (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    IsFiniteKernel (κ + η) := by
  refine ⟨⟨κ.bound + η.bound, ENNReal.add_lt_top.mpr ⟨κ.bound_lt_top, η.bound_lt_top⟩, fun a => ?_⟩⟩
  exact add_le_add (Kernel.measure_le_bound _ _ _) (Kernel.measure_le_bound _ _ _)

lemma isFiniteKernel_of_le {κ ν : Kernel α β} [hν : IsFiniteKernel ν] (hκν : κ ≤ ν) :
    IsFiniteKernel κ :=
  ⟨ν.bound, ν.bound_lt_top, fun a ↦ (hκν _ _).trans (ν.measure_le_bound a Set.univ)⟩

variable {κ η : Kernel α β}

instance IsMarkovKernel.is_probability_measure' [IsMarkovKernel κ] (a : α) :
    IsProbabilityMeasure (κ a) :=
  IsMarkovKernel.isProbabilityMeasure a

instance : IsZeroOrMarkovKernel (0 : Kernel α β) := ⟨Or.inl rfl⟩

instance (priority := 100) IsMarkovKernel.IsZeroOrMarkovKernel [h : IsMarkovKernel κ] :
    IsZeroOrMarkovKernel κ := ⟨Or.inr h⟩

instance (priority := 100) IsZeroOrMarkovKernel.isZeroOrProbabilityMeasure
    [IsZeroOrMarkovKernel κ] (a : α) : IsZeroOrProbabilityMeasure (κ a) := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | h'
  · simp only [Kernel.zero_apply]
    infer_instance
  · infer_instance

instance IsFiniteKernel.isFiniteMeasure [IsFiniteKernel κ] (a : α) : IsFiniteMeasure (κ a) :=
  ⟨(κ.measure_le_bound a Set.univ).trans_lt κ.bound_lt_top⟩

instance (priority := 100) IsZeroOrMarkovKernel.isFiniteKernel [h : IsZeroOrMarkovKernel κ] :
    IsFiniteKernel κ := by
  rcases eq_zero_or_isMarkovKernel κ with rfl | _h'
  · infer_instance
  · exact ⟨⟨1, ENNReal.one_lt_top, fun _ => prob_le_one⟩⟩

namespace Kernel

@[simp]
lemma bound_eq_one [Nonempty α] (κ : Kernel α β) [IsMarkovKernel κ] :
    κ.bound = 1 := by simp [bound]

@[deprecated (since := "2025-09-13")] alias _root_.ProbabilityTheory.IsMarkovKernel.bound_eq_one :=
  bound_eq_one

@[simp]
lemma bound_le_one (κ : Kernel α β) [IsZeroOrMarkovKernel κ] :
    κ.bound ≤ 1 := by
  rcases isEmpty_or_nonempty α
  · simp
  · rcases eq_zero_or_isMarkovKernel κ with rfl | _ <;> simp

@[deprecated (since := "2025-09-13")] alias
  _root_.ProbabilityTheory.IsZeroOrMarkovKernel.bound_le_one := bound_le_one

@[ext]
theorem ext (h : ∀ a, κ a = η a) : κ = η := DFunLike.ext _ _ h

theorem ext_iff' : κ = η ↔ ∀ a s, MeasurableSet s → κ a s = η a s := by
  simp_rw [Kernel.ext_iff, Measure.ext_iff]

theorem ext_fun (h : ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a) :
    κ = η := by
  ext a s hs
  specialize h a (s.indicator fun _ => 1) (Measurable.indicator measurable_const hs)
  simp_rw [lintegral_indicator_const hs, one_mul] at h
  rw [h]

theorem ext_fun_iff : κ = η ↔ ∀ a f, Measurable f → ∫⁻ b, f b ∂κ a = ∫⁻ b, f b ∂η a :=
  ⟨fun h a f _ => by rw [h], ext_fun⟩

section IsEmptyNonempty

instance [IsEmpty β] : Subsingleton (Kernel α β) where
  allEq κ η := by ext a s; simp [Set.eq_empty_of_isEmpty s]

instance [IsEmpty α] (κ : Kernel α β) : IsMarkovKernel κ where
  isProbabilityMeasure := by simp

instance [IsEmpty β] (κ : Kernel α β) : IsZeroOrMarkovKernel κ where
  eq_zero_or_isMarkovKernel' := by
    left
    ext a s
    simp [Set.eq_empty_of_isEmpty s]

lemma not_isMarkovKernel_zero [Nonempty α] : ¬ IsMarkovKernel (0 : Kernel α β) := by
  by_contra h
  let x : α := Nonempty.some inferInstance
  have h1 : (0 : Measure β) .univ = 1 := (h.isProbabilityMeasure x).measure_univ
  simp at h1

end IsEmptyNonempty

protected theorem measurable_coe (κ : Kernel α β) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => κ a s :=
  (Measure.measurable_coe hs).comp κ.measurable

lemma apply_congr_of_mem_measurableAtom (κ : Kernel α β) {y' y : α} (hy' : y' ∈ measurableAtom y) :
    κ y' = κ y := by
  ext s hs
  exact mem_of_mem_measurableAtom hy' (κ.measurable_coe hs (measurableSet_singleton (κ y s))) rfl

@[nontriviality]
lemma eq_zero_of_isEmpty_left (κ : Kernel α β) [h : IsEmpty α] : κ = 0 := by
  ext a
  exact h.elim a

@[nontriviality]
lemma eq_zero_of_isEmpty_right (κ : Kernel α β) [IsEmpty β] : κ = 0 := by
  ext a
  simp [Measure.eq_zero_of_isEmpty (κ a)]

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
    Measure.coe_add, ENNReal.summable.tsum_add ENNReal.summable]

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
  induction I using Finset.induction with
  | empty => rw [Finset.sum_empty]; infer_instance
  | insert i I hi_notMem_I h_ind =>
    rw [Finset.sum_insert hi_notMem_I]
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
    ENNReal.summable.tsum_prod' fun _ => ENNReal.summable]

instance isSFiniteKernel_sum [Countable ι] {κs : ι → Kernel α β}
    [hκs : ∀ n, IsSFiniteKernel (κs n)] : IsSFiniteKernel (Kernel.sum κs) := by
  cases fintypeOrInfinite ι
  · rw [sum_fintype]
    exact IsSFiniteKernel.finset_sum Finset.univ fun i _ => hκs i
  cases nonempty_denumerable ι
  exact isSFiniteKernel_sum_of_denumerable hκs

end SFinite
end Kernel
end ProbabilityTheory
