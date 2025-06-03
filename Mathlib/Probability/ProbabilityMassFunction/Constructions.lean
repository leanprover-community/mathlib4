/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Control.ULiftable

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `PMF` constructions for common probability distributions.

`map` and `seq` allow pushing a `PMF α` along a function `f : α → β` (or distribution of
functions `f : PMF (α → β)`) to get a `PMF β`.

`ofFinset` and `ofFintype` simplify the construction of a `PMF α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `PMF α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `PMF` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `Bool`.

-/

universe u v

namespace PMF

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal Finset MeasureTheory

section Map

/-- The functorial action of a function on a `PMF`. -/
def map (f : α → β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)

variable (f : α → β) (p : PMF α) (b : β)

theorem monad_map_eq_map {α β : Type u} (f : α → β) (p : PMF α) : f <$> p = p.map f := rfl

open scoped Classical in
@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]

@[simp]
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]

theorem mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp

theorem bind_pure_comp : bind p (pure ∘ f) = map f p := rfl

theorem map_id : map id p = p :=
  bind_pure _

theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map, Function.comp_def]

theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _

theorem map_bind (q : α → PMF β) (f : β → γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _

@[simp]
theorem bind_map (p : PMF α) (f : α → β) (q : β → PMF γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, Function.comp_def, bind_const, Function.const]

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  rfl

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

@[simp]
theorem toMeasure_map_apply (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ s hs,
    toMeasure_apply_eq_toOuterMeasure_apply _ (f ⁻¹' s) (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[simp]
lemma toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

end Measure

end Map

section Seq

/-- The monadic sequencing operation for `PMF`. -/
def seq (q : PMF (α → β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)

variable (q : PMF (α → β)) (p : PMF α) (b : β)

theorem monad_seq_eq_seq {α β : Type u} (q : PMF (α → β)) (p : PMF α) : q <*> p = q.seq p := rfl

open scoped Classical in
@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]
theorem support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]

theorem mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by simp

end Seq

instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

/--
This instance allows `do` notation for `PMF` to be used across universes, for instance as
```lean4
example {R : Type u} [Ring R] (x : PMF ℕ) : PMF R := do
  let ⟨n⟩ ← ULiftable.up x
  pure n
```
where `x` is in universe `0`, but the return value is in universe `u`.
-/
instance : ULiftable PMF.{u} PMF.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `PMF`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a ∈ s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a ∈ s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
theorem support_ofFinset : (ofFinset f s h h').support = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp

theorem ofFinset_apply_of_notMem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

@[deprecated (since := "2025-05-23")] alias ofFinset_apply_of_not_mem := ofFinset_apply_of_notMem

section Measure

variable (t : Set α)

@[simp]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t

@[simp]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofFinset_apply h h' t)

end Measure

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `PMF`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl

theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 := Iff.rfl

open scoped Classical in
@[simp]
lemma map_ofFintype [Fintype β] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) (g : α → β) :
    (ofFintype f h).map g = ofFintype (fun b ↦ ∑ a with g a = b, f a)
      (by simpa [Finset.sum_fiberwise_eq_sum_filter univ univ g f]) := by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h ↦ (h <| mem_univ _).elim

section Measure

variable (s : Set α)

@[simp high]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s

@[simp]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ s hs).trans (toOuterMeasure_ofFintype_apply h s)

end Measure

end OfFintype

section normalize

/-- Given an `f` with non-zero and non-infinite sum, get a `PMF` by normalizing `f` by its `tsum`.
-/
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

@[simp]
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ := rfl

@[simp]
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]

theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by simp

end normalize

section Filter

/-- Create new `PMF` by filtering on a set with non-zero measure and normalizing. -/
def filter (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)

variable {p : PMF α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

@[simp]
theorem filter_apply (a : α) :
    (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [filter, normalize_apply]

theorem filter_apply_eq_zero_of_notMem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]

@[deprecated (since := "2025-05-23")]
alias filter_apply_eq_zero_of_not_mem := filter_apply_eq_zero_of_notMem

theorem mem_support_filter_iff {a : α} : a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[simp]
theorem support_filter : (p.filter s h).support = s ∩ p.support :=
  Set.ext fun _ => mem_support_filter_iff _

theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  rw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]

theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]

end Filter

section bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl

@[simp]
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, tsub_eq_zero_iff_le, not_le]
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]

theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp

end bernoulli

end

end PMF
