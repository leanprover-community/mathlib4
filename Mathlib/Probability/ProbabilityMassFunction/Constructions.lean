/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Control.ULiftable

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `PMF` constructions for common probability distributions.

`map` and `seq` allow pushing a `PMF α` along a function `f : α → β` (or distribution of
functions `f : PMF (α → β)`) to get a `PMF β`.

`ofFinset` and `ofFintype` simplify the construction of a `PMF α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `PMF α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `PMF` and re-normalize the new distribution.

`bernoulli` represents the Bernoulli distribution on `Bool`.

-/

@[expose] public section

universe u v

namespace PMF

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal Finset MeasureTheory

section Map

/-- The functorial action of a function on a `PMF`. -/
@[deprecated Measure.map (since := "2026-08-17")]
def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)

variable (f : α → β) --(p : PMF α) (b : β)

@[deprecated "Use Measure.deterministic_comp_eq_map." (since := "2026-08-17")]
theorem monad_map_eq_map {α β : Type u} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

open scoped Classical in
@[deprecated Measure.map_apply (since := "2026-08-17")]
theorem map_apply (p : PMF α) (b : β) : (map f p) b = ∑' a, if b = f a then p a else 0 := by
  simp [map, bind_apply, pure_apply]

@[deprecated Measure.map_apply (since := "2026-08-17")]
theorem support_map (p : PMF α) : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b, support_bind, support_pure]

@[deprecated Measure.map_apply (since := "2026-08-17")]
theorem mem_support_map_iff (p : PMF α) (b : β) :
    b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp [support_map]

@[deprecated "Use Measure.deterministic_comp_eq_map." (since := "2026-08-17")]
theorem bind_pure_comp (p : PMF α) : bind p (pure ∘ f) = map f p := rfl

@[deprecated Measure.map_id (since := "2026-08-17")]
theorem map_id (p : PMF α) : map id p = p :=
  bind_pure _

@[deprecated Measure.map_map (since := "2026-08-17")]
theorem map_comp (p : PMF α) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by
    simp [map, Function.comp_def, bind_bind, pure_bind]

@[deprecated Measure.map_dirac (since := "2026-08-17")]
theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _

@[deprecated "Use Measure.map_comp." (since := "2026-08-17")]
theorem map_bind (p : PMF α) (q : α → PMF β) (f : β → γ) :
    (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _

@[deprecated "Use Kernel.comp_map." (since := "2026-08-17")]
theorem bind_map (p : PMF α) (f : α → β) (q : β → PMF γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[deprecated Measure.map_const (since := "2026-08-17")]
theorem map_const (p : PMF α) (b : β) : p.map (Function.const α b) = pure b := by
  simp only [map, Function.comp_def, bind_const, Function.const]

section Measure

@[deprecated Measure.map_apply (since := "2026-08-17")]
theorem toOuterMeasure_map_apply (p : PMF α) (s : Set β) :
    (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s), toOuterMeasure_bind_apply,
    toOuterMeasure_pure_apply]
  rfl

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

@[deprecated Measure.map_apply (since := "2026-08-17")]
theorem toMeasure_map_apply (p : PMF α) (s : Set β) (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs,
    toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[deprecated rfl (since := "2026-08-17")]
lemma toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

end Measure

end Map

section Seq

/-- The monadic sequencing operation for `PMF`. -/
@[deprecated "Use Measure.bind and Measure.dirac." (since := "2026-08-18")]
def seq (q : PMF (α → β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)

@[deprecated rfl (since := "2026-08-18")]
theorem monad_seq_eq_seq {α β : Type u} (q : PMF (α → β)) (p : PMF α) : q <*> p = q.seq p := rfl

open scoped Classical in
@[deprecated Measure.bind_apply (since := "2026-08-18")]
theorem seq_apply (q : PMF (α → β)) (p : PMF α) (b : β) :
    (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[deprecated Measure.bind_apply (since := "2026-08-18")]
theorem support_seq (q : PMF (α → β)) (p : PMF α) :
    (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [seq, @eq_comm β b, support_bind, support_pure]

@[deprecated Measure.bind_apply (since := "2026-08-18")]
theorem mem_support_seq_iff (q : PMF (α → β)) (p : PMF α) (b : β) :
    b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by
  simp [support_seq, mem_support_iff]

end Seq

@[deprecated "" (since := "2026-08-18")]
instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

@[deprecated "" (since := "2026-08-18")]
instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

@[deprecated "" (since := "2026-08-18")]
instance : ULiftable PMF.{u} PMF.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`. -/
@[deprecated "Use Finset.sum and Measure.dirac." (since := "2026-08-18")]
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a ∈ s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem support_ofFinset : (ofFinset f s h h').support = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff, ofFinset_apply] using mt (h' a)

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp [support_ofFinset]

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem ofFinset_apply_of_notMem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

section Measure

variable (t : Set α)

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofFinset_apply h h' t)

end Measure

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `PMF`. -/
@[deprecated "Use Finset.sum and Measure.dirac." (since := "2026-08-18")]
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 := Iff.rfl

open scoped Classical in
@[deprecated Measure.map_finset_sum (since := "2026-08-18")]
lemma map_ofFintype [Fintype β] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) (g : α → β) :
    (ofFintype f h).map g = ofFintype (fun b ↦ ∑ a with g a = b, f a)
      (by simpa [Finset.sum_fiberwise_eq_sum_filter univ univ g f]) := by
  refine PMF.ext fun b ↦ ?_
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h ↦ (h <| mem_univ _).elim

section Measure

variable (s : Set α)

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s

@[deprecated Measure.finsetSum_apply (since := "2026-08-18")]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_ofFintype_apply h s)

end Measure

end OfFintype

section normalize

/-- Given an `f` with non-zero and non-infinite sum, get a `PMF` by normalizing `f` by its `tsum`.
-/
@[deprecated ProbabilityTheory.cond (since := "2026-08-18")]
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ := rfl

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff, normalize_apply]

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by
  simp [support_normalize]

end normalize

section Filter

/-- Create new `PMF` by filtering on a set with non-zero measure and normalizing. -/
@[deprecated ProbabilityTheory.cond (since := "2026-08-18")]
def filter (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa [mem_support_iff] using h) (p.tsum_coe_indicator_ne_top s)

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem filter_apply {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) (a : α) :
    (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [filter, normalize_apply]

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem filter_apply_eq_zero_of_notMem {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) {a : α}
    (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem mem_support_filter_iff {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) {a : α} :
    a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem support_filter {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).support = s ∩ p.support :=
  Set.ext fun _ => mem_support_filter_iff _

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem filter_apply_eq_zero_iff {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) (a : α) :
    (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  rw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]

@[deprecated ProbabilityTheory.cond_apply (since := "2026-08-18")]
theorem filter_apply_ne_zero_iff {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support) (a : α) :
    (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
@[deprecated ProbabilityTheory.bernoulliMeasure (since := "2026-04-07")]
def bernoulli (p : ℝ≥0) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0} (h : p ≤ 1) (b : Bool)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply (since := "2026-04-07")]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := by
  simp only [bernoulli, ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ofNNReal)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, ENNReal.coe_sub,
      ENNReal.coe_one, Bool.cond_prop, Set.mem_ofPred_eq, Bool.false_eq_true, ite_false,
      not_iff_not]
    constructor
    · intro h'
      simp only [tsub_eq_zero_iff_le, one_le_coe_iff] at h'
      exact eq_of_le_of_ge h h'
    · intro h'
      simp only [h', ENNReal.coe_one, tsub_self]
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_ofPred_eq, ne_eq,
      ENNReal.coe_eq_zero]

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by
  simp [support_bernoulli]

end bernoulli

end

end PMF
