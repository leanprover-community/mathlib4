/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Order.Filter.CountableInter

#align_import measure_theory.measure.measure_space_def from "leanprover-community/mathlib"@"c14c8fcde993801fca8946b0d80131a1a81d1520"

/-!
# Measure spaces

This file defines measure spaces, the almost-everywhere filter and ae_measurable functions.
See `MeasureTheory.MeasureSpace` for their properties and for extended documentation.

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the sum of the measures of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, an outer measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

See the documentation of `MeasureTheory.MeasureSpace` for ways to construct measures and proving
that two measure are equal.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

This file does not import `MeasureTheory.MeasurableSpace.Basic`, but only `MeasurableSpace.Defs`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/


noncomputable section

open scoped Classical
open Set

open Filter hiding map

open Function MeasurableSpace

open scoped Classical
open Topology Filter ENNReal NNReal

variable {α β γ δ : Type*} {ι : Sort*}

namespace MeasureTheory

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure. -/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim ≤ toOuterMeasure
#align measure_theory.measure MeasureTheory.Measure

theorem Measure.toOuterMeasure_injective [MeasurableSpace α] :
    Injective (toOuterMeasure : Measure α → OuterMeasure α)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl
#align measure_theory.measure.to_outer_measure_injective MeasureTheory.Measure.toOuterMeasure_injective

instance Measure.instFunLike [MeasurableSpace α] : FunLike (Measure α) (Set α) ℝ≥0∞ where
  coe μ := μ.toOuterMeasure
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective <| DFunLike.coe_injective h

#noalign measure_theory.measure.has_coe_to_fun

set_option linter.deprecated false in -- Not immediately obvious how to use `measure_empty` here.
instance Measure.instOuterMeasureClass [MeasurableSpace α] : OuterMeasureClass (Measure α) α where
  measure_empty m := m.empty'
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

section

variable [MeasurableSpace α] {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

namespace Measure

theorem trimmed (μ : Measure α) : μ.toOuterMeasure.trim = μ.toOuterMeasure :=
  le_antisymm μ.trim_le μ.1.le_trim

/-! ### General facts about measures -/

/-- Obtain a measure by giving a countably additive function that sends `∅` to `0`. -/
def ofMeasurable (m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞) (m0 : m ∅ MeasurableSet.empty = 0)
    (mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)) :
    Measure α :=
  { toOuterMeasure := inducedOuterMeasure m _ m0
    m_iUnion := fun f hf hd =>
      show inducedOuterMeasure m _ m0 (iUnion f) = ∑' i, inducedOuterMeasure m _ m0 (f i) by
        rw [inducedOuterMeasure_eq m0 mU, mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs ↦ by
      rw [OuterMeasure.trim_eq _ hs, inducedOuterMeasure_eq m0 mU hs] }
#align measure_theory.measure.of_measurable MeasureTheory.Measure.ofMeasurable

theorem ofMeasurable_apply {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
    {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  inducedOuterMeasure_eq m0 mU hs
#align measure_theory.measure.of_measurable_apply MeasureTheory.Measure.ofMeasurable_apply

@[ext]
theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  toOuterMeasure_injective <| by
  rw [← trimmed, OuterMeasure.trim_congr (h _), trimmed]
#align measure_theory.measure.ext MeasureTheory.Measure.ext

theorem ext_iff : μ₁ = μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s = μ₂ s :=
  ⟨by rintro rfl s _hs; rfl, Measure.ext⟩
#align measure_theory.measure.ext_iff MeasureTheory.Measure.ext_iff

theorem ext_iff' : μ₁ = μ₂ ↔ ∀ s, μ₁ s = μ₂ s :=
  ⟨by rintro rfl s; rfl, fun h ↦ Measure.ext (fun s _ ↦ h s)⟩

theorem outerMeasure_le_iff {m : OuterMeasure α} : m ≤ μ.1 ↔ ∀ s, MeasurableSet s → m s ≤ μ s := by
  simpa only [μ.trimmed] using OuterMeasure.le_trim_iff (m₂ := μ.1)

end Measure

@[simp] theorem Measure.coe_toOuterMeasure (μ : Measure α) : ⇑μ.toOuterMeasure = μ := rfl
#align measure_theory.coe_to_outer_measure MeasureTheory.Measure.coe_toOuterMeasure

theorem Measure.toOuterMeasure_apply (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s :=
  rfl
#align measure_theory.to_outer_measure_apply MeasureTheory.Measure.toOuterMeasure_apply

theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by
  rw [μ.trimmed, μ.coe_toOuterMeasure]
#align measure_theory.measure_eq_trim MeasureTheory.measure_eq_trim

theorem measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (_ : s ⊆ t) (_ : MeasurableSet t), μ t := by
  rw [measure_eq_trim, OuterMeasure.trim_eq_iInf, μ.coe_toOuterMeasure]
#align measure_theory.measure_eq_infi MeasureTheory.measure_eq_iInf

/-- A variant of `measure_eq_iInf` which has a single `iInf`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
theorem measure_eq_iInf' (μ : Measure α) (s : Set α) :
    μ s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, μ t := by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]
#align measure_theory.measure_eq_infi' MeasureTheory.measure_eq_iInf'

theorem measure_eq_inducedOuterMeasure :
    μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty s :=
  measure_eq_trim _
#align measure_theory.measure_eq_induced_outer_measure MeasureTheory.measure_eq_inducedOuterMeasure

theorem toOuterMeasure_eq_inducedOuterMeasure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty :=
  μ.trimmed.symm
#align measure_theory.to_outer_measure_eq_induced_outer_measure MeasureTheory.toOuterMeasure_eq_inducedOuterMeasure

theorem measure_eq_extend (hs : MeasurableSet s) :
    μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s := by
  rw [extend_eq]
  exact hs
#align measure_theory.measure_eq_extend MeasureTheory.measure_eq_extend

theorem nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ measure_empty
#align measure_theory.nonempty_of_measure_ne_zero MeasureTheory.nonempty_of_measure_ne_zero

theorem measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
  top_unique <| h₁ ▸ measure_mono h
#align measure_theory.measure_mono_top MeasureTheory.measure_mono_top

@[simp, mono]
theorem measure_le_measure_union_left : μ s ≤ μ (s ∪ t) := μ.mono subset_union_left

@[simp, mono]
theorem measure_le_measure_union_right : μ t ≤ μ (s ∪ t) := μ.mono subset_union_right

/-- For every set there exists a measurable superset of the same measure. -/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [← measure_eq_trim] using μ.toOuterMeasure.exists_measurable_superset_eq_trim s
#align measure_theory.exists_measurable_superset MeasureTheory.exists_measurable_superset

/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
theorem exists_measurable_superset_forall_eq [Countable ι] (μ : ι → Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = μ i s := by
  simpa only [← measure_eq_trim] using
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s
#align measure_theory.exists_measurable_superset_forall_eq MeasureTheory.exists_measurable_superset_forall_eq

theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [Bool.forall_bool.trans and_comm] using
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s
#align measure_theory.exists_measurable_superset₂ MeasureTheory.exists_measurable_superset₂

theorem exists_measurable_superset_of_null (h : μ s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s
#align measure_theory.exists_measurable_superset_of_null MeasureTheory.exists_measurable_superset_of_null

theorem exists_measurable_superset_iff_measure_eq_zero :
    (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩
#align measure_theory.exists_measurable_superset_iff_measure_eq_zero MeasureTheory.exists_measurable_superset_iff_measure_eq_zero

theorem measure_biUnion_lt_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) ≠ ∞) : μ (⋃ i ∈ s, f i) < ∞ := by
  convert (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · apply ENNReal.sum_lt_top; simpa only [Finite.mem_toFinset]
#align measure_theory.measure_bUnion_lt_top MeasureTheory.measure_biUnion_lt_top

@[deprecated measure_iUnion_null_iff (since := "2024-01-14")]
theorem measure_iUnion_null_iff' {ι : Prop} {s : ι → Set α} : μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
  measure_iUnion_null_iff
#align measure_theory.measure_Union_null_iff' MeasureTheory.measure_iUnion_null_iff'

theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
  (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)
#align measure_theory.measure_union_lt_top MeasureTheory.measure_union_lt_top

@[simp]
theorem measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h
#align measure_theory.measure_union_lt_top_iff MeasureTheory.measure_union_lt_top_iff

theorem measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).ne
#align measure_theory.measure_union_ne_top MeasureTheory.measure_union_ne_top

open scoped symmDiff in
theorem measure_symmDiff_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∆ t) ≠ ∞ :=
  ne_top_of_le_ne_top (measure_union_ne_top hs ht) <| measure_mono symmDiff_subset_union

@[simp]
theorem measure_union_eq_top_iff : μ (s ∪ t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
  not_iff_not.1 <| by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]
#align measure_theory.measure_union_eq_top_iff MeasureTheory.measure_union_eq_top_iff

theorem exists_measure_pos_of_not_measure_iUnion_null [Countable ι] {s : ι → Set α}
    (hs : μ (⋃ n, s n) ≠ 0) : ∃ n, 0 < μ (s n) := by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)
#align measure_theory.exists_measure_pos_of_not_measure_Union_null MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null

theorem measure_lt_top_of_subset (hst : t ⊆ s) (hs : μ s ≠ ∞) : μ t < ∞ :=
  lt_of_le_of_lt (μ.mono hst) hs.lt_top

theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) < ∞ :=
  measure_lt_top_of_subset inter_subset_left hs_finite
#align measure_theory.measure_inter_lt_top_of_left_ne_top MeasureTheory.measure_inter_lt_top_of_left_ne_top

theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) < ∞ :=
  measure_lt_top_of_subset inter_subset_right ht_finite
#align measure_theory.measure_inter_lt_top_of_right_ne_top MeasureTheory.measure_inter_lt_top_of_right_ne_top

theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_right h
#align measure_theory.measure_inter_null_of_null_right MeasureTheory.measure_inter_null_of_null_right

theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_left h
#align measure_theory.measure_inter_null_of_null_left MeasureTheory.measure_inter_null_of_null_left

/-! ### The almost everywhere filter -/
section ae

/-- Given a predicate on `β` and `Set α` where both `α` and `β` are measurable spaces, if the
predicate holds for almost every `x : β` and
- `∅ : Set α`
- a family of sets generating the σ-algebra of `α`
Moreover, if for almost every `x : β`, the predicate is closed under complements and countable
disjoint unions, then the predicate holds for almost every `x : β` and all measurable sets of `α`.

This is an AE version of `MeasurableSpace.induction_on_inter` where the condition is dependent
on a measurable space `β`. -/
theorem _root_.MeasurableSpace.ae_induction_on_inter {β} [MeasurableSpace β] {μ : Measure β}
    {C : β → Set α → Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s) (h_empty : ∀ᵐ x ∂μ, C x ∅) (h_basic : ∀ᵐ x ∂μ, ∀ t ∈ s, C x t)
    (h_compl : ∀ᵐ x ∂μ, ∀ t, MeasurableSet t → C x t → C x tᶜ)
    (h_union : ∀ᵐ x ∂μ, ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C x (f i)) → C x (⋃ i, f i)) :
    ∀ᵐ x ∂μ, ∀ ⦃t⦄, MeasurableSet t → C x t := by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter h_eq h_inter hx_empty hx_basic hx_compl hx_union

end ae

/-- A measurable set `t ⊇ s` such that `μ t = μ s`. It even satisfies `μ (t ∩ u) = μ (s ∩ u)` for
any measurable set `u` if `μ s ≠ ∞`, see `measure_toMeasurable_inter`.
(This property holds without the assumption `μ s ≠ ∞` when the space is s-finite -- for example
σ-finite), see `measure_toMeasurable_inter_of_sFinite`).
If `s` is a null measurable set, then
we also have `t =ᵐ[μ] s`, see `NullMeasurableSet.toMeasurable_ae_eq`.
This notion is sometimes called a "measurable hull" in the literature. -/
irreducible_def toMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ t, t ⊇ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s then h.choose else
    if h' : ∃ t, t ⊇ s ∧ MeasurableSet t ∧
      ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then h'.choose
    else (exists_measurable_superset μ s).choose
#align measure_theory.to_measurable MeasureTheory.toMeasurable

theorem subset_toMeasurable (μ : Measure α) (s : Set α) : s ⊆ toMeasurable μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]
#align measure_theory.subset_to_measurable MeasureTheory.subset_toMeasurable

theorem ae_le_toMeasurable : s ≤ᵐ[μ] toMeasurable μ s :=
  HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _)

  --(subset_toMeasurable _ _).EventuallyLE
#align measure_theory.ae_le_to_measurable MeasureTheory.ae_le_toMeasurable

@[simp]
theorem measurableSet_toMeasurable (μ : Measure α) (s : Set α) :
    MeasurableSet (toMeasurable μ s) := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]
#align measure_theory.measurable_set_to_measurable MeasureTheory.measurableSet_toMeasurable

@[simp]
theorem measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2
#align measure_theory.measure_to_measurable MeasureTheory.measure_toMeasurable

/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α
#align measure_theory.measure_space MeasureTheory.MeasureSpace

export MeasureSpace (volume)

/-- `volume` is the canonical measure on `α`. -/
add_decl_doc volume

section MeasureSpace

/-- `∀ᵐ a, p a` means that `p a` for a.e. `a`, i.e. `p` holds true away from a null set.

This is notation for `Filter.Eventually P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "∀ᵐ "(...)", "r:(scoped P =>
  Filter.Eventually P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

/-- `∃ᵐ a, p a` means that `p` holds frequently, i.e. on a set of positive measure,
w.r.t. the volume measure.

This is notation for `Filter.Frequently P (MeasureTheory.ae MeasureSpace.volume)`. -/
notation3 "∃ᵐ "(...)", "r:(scoped P =>
  Filter.Frequently P <| MeasureTheory.ae MeasureTheory.MeasureSpace.volume) => r

/-- The tactic `exact volume`, to be used in optional (`autoParam`) arguments. -/
macro "volume_tac" : tactic =>
  `(tactic| (first | exact MeasureTheory.MeasureSpace.volume))

end MeasureSpace

end

end MeasureTheory

section

open MeasureTheory

/-!
# Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `AEMeasurable f μ`. It's properties are discussed in
`MeasureTheory.MeasureSpace`.
-/


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ ν : Measure α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. -/
def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g
#align ae_measurable AEMeasurable

@[aesop unsafe 30% apply (rule_sets := [Measurable])]
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩
#align measurable.ae_measurable Measurable.aemeasurable

namespace AEMeasurable

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk (f : α → β) (h : AEMeasurable f μ) : α → β :=
  Classical.choose h
#align ae_measurable.mk AEMeasurable.mk

@[measurability]
theorem measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.choose_spec h).1
#align ae_measurable.measurable_mk AEMeasurable.measurable_mk

theorem ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.choose_spec h).2
#align ae_measurable.ae_eq_mk AEMeasurable.ae_eq_mk

theorem congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩
#align ae_measurable.congr AEMeasurable.congr

end AEMeasurable

theorem aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ :=
  ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩
#align ae_measurable_congr aemeasurable_congr

@[simp, measurability]
theorem aemeasurable_const {b : β} : AEMeasurable (fun _a : α => b) μ :=
  measurable_const.aemeasurable
#align ae_measurable_const aemeasurable_const

@[measurability]
theorem aemeasurable_id : AEMeasurable id μ :=
  measurable_id.aemeasurable
#align ae_measurable_id aemeasurable_id

@[measurability]
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.aemeasurable
#align ae_measurable_id' aemeasurable_id'

theorem Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : Measurable g)
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩
#align measurable.comp_ae_measurable Measurable.comp_aemeasurable

@[measurability]
theorem Measurable.comp_aemeasurable' [MeasurableSpace δ] {f : α → δ} {g : δ → β}
    (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (fun x => g (f x)) μ :=
  Measurable.comp_aemeasurable hg hf

end
