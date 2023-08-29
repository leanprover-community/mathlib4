/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Probability.ProbabilityMassFunction.Monad

#align_import probability.probability_mass_function.constructions from "leanprover-community/mathlib"@"4ac69b290818724c159de091daa3acd31da0ee6d"

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `Pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `Pmf α` along a function `f : α → β` (or distribution of
functions `f : Pmf (α → β)`) to get a `Pmf β`.

`ofFinset` and `ofFintype` simplify the construction of a `Pmf α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `Pmf α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `Pmf` and re-normalize the new distribution.

`bernoulli` represents the bernoulli distribution on `Bool`.

-/


namespace Pmf

noncomputable section

variable {α β γ : Type*}

open Classical BigOperators NNReal ENNReal

section Map

/-- The functorial action of a function on a `Pmf`. -/
def map (f : α → β) (p : Pmf α) : Pmf β :=
  bind p (pure ∘ f)
#align pmf.map Pmf.map

variable (f : α → β) (p : Pmf α) (b : β)

theorem monad_map_eq_map {α β : Type _} (f : α → β) (p : Pmf α) : f <$> p = p.map f := rfl
#align pmf.monad_map_eq_map Pmf.monad_map_eq_map

@[simp]
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]
                                                                         -- 🎉 no goals
#align pmf.map_apply Pmf.map_apply

@[simp]
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]
                      -- 🎉 no goals
#align pmf.support_map Pmf.support_map

theorem mem_support_map_iff : b ∈ (map f p).support ↔ ∃ a ∈ p.support, f a = b := by simp
                                                                                     -- 🎉 no goals
#align pmf.mem_support_map_iff Pmf.mem_support_map_iff

theorem bind_pure_comp : bind p (pure ∘ f) = map f p := rfl
#align pmf.bind_pure_comp Pmf.bind_pure_comp

theorem map_id : map id p = p :=
  bind_pure _
#align pmf.map_id Pmf.map_id

theorem map_comp (g : β → γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map, Function.comp]
                                                                     -- 🎉 no goals
#align pmf.map_comp Pmf.map_comp

theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _
#align pmf.pure_map Pmf.pure_map

theorem map_bind (q : α → Pmf β) (f : β → γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _
#align pmf.map_bind Pmf.map_bind

@[simp]
theorem bind_map (p : Pmf α) (f : α → β) (q : β → Pmf γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))
#align pmf.bind_map Pmf.bind_map

@[simp]
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, Function.comp, bind_const, Function.const]
  -- 🎉 no goals
#align pmf.map_const Pmf.map_const

section Measure

variable (s : Set β)

@[simp]
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  -- 🎉 no goals
#align pmf.to_outer_measure_map_apply Pmf.toOuterMeasure_map_apply

@[simp]
theorem toMeasure_map_apply [MeasurableSpace α] [MeasurableSpace β] (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ s hs,
    toMeasure_apply_eq_toOuterMeasure_apply _ (f ⁻¹' s) (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s
  -- 🎉 no goals
#align pmf.to_measure_map_apply Pmf.toMeasure_map_apply

end Measure

end Map

section Seq

/-- The monadic sequencing operation for `Pmf`. -/
def seq (q : Pmf (α → β)) (p : Pmf α) : Pmf β :=
  q.bind fun m => p.bind fun a => pure (m a)
#align pmf.seq Pmf.seq

variable (q : Pmf (α → β)) (p : Pmf α) (b : β)

theorem monad_seq_eq_seq {α β : Type _} (q : Pmf (α → β)) (p : Pmf α) : q <*> p = q.seq p := rfl
#align pmf.monad_seq_eq_seq Pmf.monad_seq_eq_seq

@[simp]
theorem seq_apply : (seq q p) b = ∑' (f : α → β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  -- ⊢ (∑' (a : α → β), ↑q a * ∑' (a_1 : α), if b = a a_1 then ↑p a_1 else 0) = ∑'  …
  refine' tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => _)
  -- ⊢ (↑q f * if b = f a then ↑p a else 0) = if b = f a then ↑q f * ↑p a else 0
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0
  -- 🎉 no goals
#align pmf.seq_apply Pmf.seq_apply

@[simp]
theorem support_seq : (seq q p).support = ⋃ f ∈ q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]
                      -- 🎉 no goals
#align pmf.support_seq Pmf.support_seq

theorem mem_support_seq_iff : b ∈ (seq q p).support ↔ ∃ f ∈ q.support, b ∈ f '' p.support := by simp
                                                                                                -- 🎉 no goals
#align pmf.mem_support_seq_iff Pmf.mem_support_seq_iff

end Seq

instance : LawfulFunctor Pmf where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

instance : LawfulMonad Pmf := LawfulMonad.mk'
  (bind_pure_comp := fun f x => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

section OfFinset

/-- Given a finset `s` and a function `f : α → ℝ≥0∞` with sum `1` on `s`,
  such that `f a = 0` for `a ∉ s`, we get a `Pmf`. -/
def ofFinset (f : α → ℝ≥0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
    (h' : ∀ (a) (_ : a ∉ s), f a = 0) : Pmf α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩
#align pmf.of_finset Pmf.ofFinset

variable {f : α → ℝ≥0∞} {s : Finset α} (h : ∑ a in s, f a = 1) (h' : ∀ (a) (_ : a ∉ s), f a = 0)

@[simp]
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl
#align pmf.of_finset_apply Pmf.ofFinset_apply

@[simp]
theorem support_ofFinset : (ofFinset f s h h').support = ↑s ∩ Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)
                      -- 🎉 no goals
#align pmf.support_of_finset Pmf.support_ofFinset

theorem mem_support_ofFinset_iff (a : α) : a ∈ (ofFinset f s h h').support ↔ a ∈ s ∧ f a ≠ 0 := by
  simp
  -- 🎉 no goals
#align pmf.mem_support_of_finset_iff Pmf.mem_support_ofFinset_iff

theorem ofFinset_apply_of_not_mem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha
#align pmf.of_finset_apply_of_not_mem Pmf.ofFinset_apply_of_not_mem

section Measure

variable (t : Set α)

@[simp]
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t
#align pmf.to_outer_measure_of_finset_apply Pmf.toOuterMeasure_ofFinset_apply

@[simp]
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ t ht).trans (toOuterMeasure_ofFinset_apply h h' t)
#align pmf.to_measure_of_finset_apply Pmf.toMeasure_ofFinset_apply

end Measure

end OfFinset

section OfFintype

/-- Given a finite type `α` and a function `f : α → ℝ≥0∞` with sum 1, we get a `Pmf`. -/
def ofFintype [Fintype α] (f : α → ℝ≥0∞) (h : ∑ a, f a = 1) : Pmf α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha
#align pmf.of_fintype Pmf.ofFintype

variable [Fintype α] {f : α → ℝ≥0∞} (h : ∑ a, f a = 1)

@[simp]
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl
#align pmf.of_fintype_apply Pmf.ofFintype_apply

@[simp]
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl
#align pmf.support_of_fintype Pmf.support_ofFintype

theorem mem_support_ofFintype_iff (a : α) : a ∈ (ofFintype f h).support ↔ f a ≠ 0 := Iff.rfl
#align pmf.mem_support_of_fintype_iff Pmf.mem_support_ofFintype_iff

section Measure

variable (s : Set α)

@[simp high]
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s
#align pmf.to_outer_measure_of_fintype_apply Pmf.toOuterMeasure_ofFintype_apply

@[simp]
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ s hs).trans (toOuterMeasure_ofFintype_apply h s)
#align pmf.to_measure_of_fintype_apply Pmf.toMeasure_ofFintype_apply

end Measure

end OfFintype

section normalize

/-- Given an `f` with non-zero and non-infinite sum, get a `Pmf` by normalizing `f` by its `tsum`.
-/
def normalize (f : α → ℝ≥0∞) (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞) : Pmf α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩
#align pmf.normalize Pmf.normalize

variable {f : α → ℝ≥0∞} (hf0 : tsum f ≠ 0) (hf : tsum f ≠ ∞)

@[simp]
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ := rfl
#align pmf.normalize_apply Pmf.normalize_apply

@[simp]
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]
                      -- 🎉 no goals
#align pmf.support_normalize Pmf.support_normalize

theorem mem_support_normalize_iff (a : α) : a ∈ (normalize f hf0 hf).support ↔ f a ≠ 0 := by simp
                                                                                             -- 🎉 no goals
#align pmf.mem_support_normalize_iff Pmf.mem_support_normalize_iff

end normalize

section Filter

/-- Create new `Pmf` by filtering on a set with non-zero measure and normalizing. -/
def filter (p : Pmf α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) : Pmf α :=
  Pmf.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)
                                    -- 🎉 no goals
#align pmf.filter Pmf.filter

variable {p : Pmf α} {s : Set α} (h : ∃ a ∈ s, a ∈ p.support)

@[simp]
theorem filter_apply (a : α) :
    (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [filter, normalize_apply]
  -- 🎉 no goals
#align pmf.filter_apply Pmf.filter_apply

theorem filter_apply_eq_zero_of_not_mem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply, Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]
  -- 🎉 no goals
#align pmf.filter_apply_eq_zero_of_not_mem Pmf.filter_apply_eq_zero_of_not_mem

theorem mem_support_filter_iff {a : α} : a ∈ (p.filter s h).support ↔ a ∈ s ∧ a ∈ p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero
#align pmf.mem_support_filter_iff Pmf.mem_support_filter_iff

@[simp]
theorem support_filter : (p.filter s h).support = s ∩ p.support :=
  Set.ext fun _ => mem_support_filter_iff _
#align pmf.support_filter Pmf.support_filter

theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  erw [apply_eq_zero_iff, support_filter, Set.mem_inter_iff, not_and_or]
  -- 🎉 no goals
#align pmf.filter_apply_eq_zero_iff Pmf.filter_apply_eq_zero_iff

theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a ≠ 0 ↔ a ∈ s ∧ a ∈ p.support := by
  rw [Ne.def, filter_apply_eq_zero_iff, not_or, Classical.not_not, Classical.not_not]
  -- 🎉 no goals
#align pmf.filter_apply_ne_zero_iff Pmf.filter_apply_ne_zero_iff

end Filter

section bernoulli

/-- A `Pmf` which assigns probability `p` to `true` and `1 - p` to `false`. -/
def bernoulli (p : ℝ≥0∞) (h : p ≤ 1) : Pmf Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])
                                            -- 🎉 no goals
#align pmf.bernoulli Pmf.bernoulli

variable {p : ℝ≥0∞} (h : p ≤ 1) (b : Bool)

@[simp]
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := rfl
#align pmf.bernoulli_apply Pmf.bernoulli_apply

@[simp]
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p ≠ 0) (p ≠ 1) } := by
  refine' Set.ext fun b => _
  -- ⊢ b ∈ support (bernoulli p h) ↔ b ∈ {b | bif b then p ≠ 0 else p ≠ 1}
  induction b
  -- ⊢ false ∈ support (bernoulli p h) ↔ false ∈ {b | bif b then p ≠ 0 else p ≠ 1}
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne.def, tsub_eq_zero_iff_le, not_le]
    -- ⊢ p < 1 ↔ false ∈ {b | bif b then ¬p = 0 else ¬p = 1}
    exact ⟨ne_of_lt, lt_of_le_of_ne h⟩
    -- 🎉 no goals
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_setOf_eq]
    -- 🎉 no goals
#align pmf.support_bernoulli Pmf.support_bernoulli

theorem mem_support_bernoulli_iff : b ∈ (bernoulli p h).support ↔ cond b (p ≠ 0) (p ≠ 1) := by simp
                                                                                               -- 🎉 no goals
#align pmf.mem_support_bernoulli_iff Pmf.mem_support_bernoulli_iff

end bernoulli

end

end Pmf
