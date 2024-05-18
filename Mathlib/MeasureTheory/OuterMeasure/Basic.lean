/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Disjointed
import Mathlib.MeasureTheory.OuterMeasure.Defs

#align_import measure_theory.measure.outer_measure from "leanprover-community/mathlib"@"343e80208d29d2d15f8050b929aa50fe4ce71b55"

/-!
# Outer Measures

An outer measure is a function `μ : Set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

## References

<https://en.wikipedia.org/wiki/Outer_measure>

## Tags

outer measure
-/


noncomputable section

open Set Function Filter
open scoped Classical BigOperators NNReal Topology ENNReal

namespace MeasureTheory

namespace OuterMeasure

variable {α β : Type*} {m : OuterMeasure α}

@[simp]
theorem empty' (m : OuterMeasure α) : m ∅ = 0 :=
  m.empty
#align measure_theory.outer_measure.empty' MeasureTheory.OuterMeasure.empty'

@[gcongr]
theorem mono' (m : OuterMeasure α) {s₁ s₂} (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ :=
  m.mono h
#align measure_theory.outer_measure.mono' MeasureTheory.OuterMeasure.mono'

theorem mono_null (m : OuterMeasure α) {s t} (h : s ⊆ t) (ht : m t = 0) : m s = 0 :=
  nonpos_iff_eq_zero.mp <| ht ▸ m.mono' h
#align measure_theory.outer_measure.mono_null MeasureTheory.OuterMeasure.mono_null

theorem pos_of_subset_ne_zero (m : OuterMeasure α) {a b : Set α} (hs : a ⊆ b) (hnz : m a ≠ 0) :
    0 < m b :=
  lt_of_lt_of_le (pos_iff_ne_zero.mpr hnz) (m.mono hs)
#align measure_theory.outer_measure.pos_of_subset_ne_zero MeasureTheory.OuterMeasure.pos_of_subset_ne_zero

protected theorem iUnion (m : OuterMeasure α) {β} [Countable β] (s : β → Set α) :
    m (⋃ i, s i) ≤ ∑' i, m (s i) := by
  refine rel_iSup_tsum m m.empty (· ≤ ·) (fun t ↦ ?_) _
  calc
    m (⋃ i, t i) = m (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ ≤ ∑' i, m (disjointed t i) := m.iUnion_nat _ (disjoint_disjointed _)
    _ ≤ ∑' i, m (t i) := ENNReal.tsum_le_tsum fun _ ↦ m.mono <| disjointed_subset _ _
#align measure_theory.outer_measure.Union MeasureTheory.OuterMeasure.iUnion

theorem biUnion_null_iff (m : OuterMeasure α) {s : Set β} (hs : s.Countable) {t : β → Set α} :
    m (⋃ i ∈ s, t i) = 0 ↔ ∀ i ∈ s, m (t i) = 0 := by
  refine ⟨fun h i hi ↦ m.mono_null (subset_biUnion_of_mem hi) h, fun h ↦ ?_⟩
  have _ := hs.toEncodable
  simpa [h] using m.iUnion fun x : s ↦ t x
#align measure_theory.outer_measure.bUnion_null_iff MeasureTheory.OuterMeasure.biUnion_null_iff

theorem sUnion_null_iff (m : OuterMeasure α) {S : Set (Set α)} (hS : S.Countable) :
    m (⋃₀ S) = 0 ↔ ∀ s ∈ S, m s = 0 := by rw [sUnion_eq_biUnion, m.biUnion_null_iff hS]
#align measure_theory.outer_measure.sUnion_null_iff MeasureTheory.OuterMeasure.sUnion_null_iff

@[simp]
theorem iUnion_null_iff {ι : Sort*} [Countable ι] (m : OuterMeasure α) {s : ι → Set α} :
    m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 := by
  rw [← sUnion_range, m.sUnion_null_iff (countable_range s), forall_mem_range]
#align measure_theory.outer_measure.Union_null_iff MeasureTheory.OuterMeasure.iUnion_null_iff

alias ⟨_, iUnion_null⟩ := iUnion_null_iff
#align measure_theory.outer_measure.Union_null MeasureTheory.OuterMeasure.iUnion_null

@[deprecated] -- Deprecated since 14 January 2024
theorem iUnion_null_iff' (m : OuterMeasure α) {ι : Prop} {s : ι → Set α} :
    m (⋃ i, s i) = 0 ↔ ∀ i, m (s i) = 0 :=
  m.iUnion_null_iff
#align measure_theory.outer_measure.Union_null_iff' MeasureTheory.OuterMeasure.iUnion_null_iff'

protected theorem iUnion_finset (m : OuterMeasure α) (s : β → Set α) (t : Finset β) :
    m (⋃ i ∈ t, s i) ≤ ∑ i in t, m (s i) :=
  rel_iSup_sum m m.empty (· ≤ ·) m.iUnion s t
#align measure_theory.outer_measure.Union_finset MeasureTheory.OuterMeasure.iUnion_finset

protected theorem union (m : OuterMeasure α) (s₁ s₂ : Set α) : m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
  rel_sup_add m m.empty (· ≤ ·) m.iUnion s₁ s₂
#align measure_theory.outer_measure.union MeasureTheory.OuterMeasure.union

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
theorem null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α] (m : OuterMeasure α)
    (s : Set α) (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, m u = 0) : m s = 0 := by
  choose! u hxu hu₀ using hs
  choose t ht using TopologicalSpace.countable_cover_nhdsWithin hxu
  rcases ht with ⟨ts, t_count, ht⟩
  apply m.mono_null ht
  exact (m.biUnion_null_iff t_count).2 fun x hx => hu₀ x (ts hx)
#align measure_theory.outer_measure.null_of_locally_null MeasureTheory.OuterMeasure.null_of_locally_null

/-- If `m s ≠ 0`, then for some point `x ∈ s` and any `t ∈ 𝓝[s] x` we have `0 < m t`. -/
theorem exists_mem_forall_mem_nhds_within_pos [TopologicalSpace α] [SecondCountableTopology α]
    (m : OuterMeasure α) {s : Set α} (hs : m s ≠ 0) : ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < m t := by
  contrapose! hs
  simp only [nonpos_iff_eq_zero] at hs
  exact m.null_of_locally_null s hs
#align measure_theory.outer_measure.exists_mem_forall_mem_nhds_within_pos MeasureTheory.OuterMeasure.exists_mem_forall_mem_nhds_within_pos

/-- If `s : ι → Set α` is a sequence of sets, `S = ⋃ n, s n`, and `m (S \ s n)` tends to zero along
some nontrivial filter (usually `atTop` on `ι = ℕ`), then `m S = ⨆ n, m (s n)`. -/
theorem iUnion_of_tendsto_zero {ι} (m : OuterMeasure α) {s : ι → Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => m ((⋃ n, s n) \ s k)) l (𝓝 0)) : m (⋃ n, s n) = ⨆ n, m (s n) := by
  set S := ⋃ n, s n
  set M := ⨆ n, m (s n)
  have hsS : ∀ {k}, s k ⊆ S := fun {k} => subset_iUnion _ _
  refine' le_antisymm _ (iSup_le fun n => m.mono hsS)
  have A : ∀ k, m S ≤ M + m (S \ s k) := fun k =>
    calc
      m S = m (s k ∪ S \ s k) := by rw [union_diff_self, union_eq_self_of_subset_left hsS]
      _ ≤ m (s k) + m (S \ s k) := m.union _ _
      _ ≤ M + m (S \ s k) := add_le_add_right (le_iSup (m.measureOf ∘ s) k) _
  have B : Tendsto (fun k => M + m (S \ s k)) l (𝓝 (M + 0)) := tendsto_const_nhds.add h0
  rw [add_zero] at B
  exact ge_of_tendsto' B A
#align measure_theory.outer_measure.Union_of_tendsto_zero MeasureTheory.OuterMeasure.iUnion_of_tendsto_zero

/-- If `s : ℕ → Set α` is a monotone sequence of sets such that `∑' k, m (s (k + 1) \ s k) ≠ ∞`,
then `m (⋃ n, s n) = ⨆ n, m (s n)`. -/
theorem iUnion_nat_of_monotone_of_tsum_ne_top (m : OuterMeasure α) {s : ℕ → Set α}
    (h_mono : ∀ n, s n ⊆ s (n + 1)) (h0 : (∑' k, m (s (k + 1) \ s k)) ≠ ∞) :
    m (⋃ n, s n) = ⨆ n, m (s n) := by
  refine' m.iUnion_of_tendsto_zero atTop _
  refine' tendsto_nhds_bot_mono' (ENNReal.tendsto_sum_nat_add _ h0) fun n => _
  refine' (m.mono _).trans (m.iUnion _)
  -- Current goal: `(⋃ k, s k) \ s n ⊆ ⋃ k, s (k + n + 1) \ s (k + n)`
  have h' : Monotone s := @monotone_nat_of_le_succ (Set α) _ _ h_mono
  simp only [diff_subset_iff, iUnion_subset_iff]
  intro i x hx
  have : ∃i, x ∈ s i := by exists i
  rcases Nat.findX this with ⟨j, hj, hlt⟩
  clear hx i
  rcases le_or_lt j n with hjn | hnj
  · exact Or.inl (h' hjn hj)
  have : j - (n + 1) + n + 1 = j := by omega
  refine' Or.inr (mem_iUnion.2 ⟨j - (n + 1), _, hlt _ _⟩)
  · rwa [this]
  · rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, this]
#align measure_theory.outer_measure.Union_nat_of_monotone_of_tsum_ne_top MeasureTheory.OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top

theorem le_inter_add_diff {m : OuterMeasure α} {t : Set α} (s : Set α) :
    m t ≤ m (t ∩ s) + m (t \ s) := by
  convert m.union _ _
  rw [inter_union_diff t s]
#align measure_theory.outer_measure.le_inter_add_diff MeasureTheory.OuterMeasure.le_inter_add_diff

theorem diff_null (m : OuterMeasure α) (s : Set α) {t : Set α} (ht : m t = 0) :
    m (s \ t) = m s := by
  refine' le_antisymm (m.mono <| diff_subset _ _) _
  calc
    m s ≤ m (s ∩ t) + m (s \ t) := le_inter_add_diff _
    _ ≤ m t + m (s \ t) := add_le_add_right (m.mono <| inter_subset_right _ _) _
    _ = m (s \ t) := by rw [ht, zero_add]
#align measure_theory.outer_measure.diff_null MeasureTheory.OuterMeasure.diff_null

theorem union_null (m : OuterMeasure α) {s₁ s₂ : Set α} (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) :
    m (s₁ ∪ s₂) = 0 := by simpa [h₁, h₂] using m.union s₁ s₂
#align measure_theory.outer_measure.union_null MeasureTheory.OuterMeasure.union_null

theorem coe_fn_injective : Injective fun (μ : OuterMeasure α) (s : Set α) => μ s :=
  DFunLike.coe_injective
#align measure_theory.outer_measure.coe_fn_injective MeasureTheory.OuterMeasure.coe_fn_injective

@[ext]
theorem ext {μ₁ μ₂ : OuterMeasure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  coe_fn_injective <| funext h
#align measure_theory.outer_measure.ext MeasureTheory.OuterMeasure.ext

/-- A version of `MeasureTheory.OuterMeasure.ext` that assumes `μ₁ s = μ₂ s` on all *nonempty*
sets `s`, and gets `μ₁ ∅ = μ₂ ∅` from `MeasureTheory.OuterMeasure.empty'`. -/
theorem ext_nonempty {μ₁ μ₂ : OuterMeasure α} (h : ∀ s : Set α, s.Nonempty → μ₁ s = μ₂ s) :
    μ₁ = μ₂ :=
  ext fun s => s.eq_empty_or_nonempty.elim (fun he => by rw [he, empty', empty']) (h s)
#align measure_theory.outer_measure.ext_nonempty MeasureTheory.OuterMeasure.ext_nonempty
