/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Induced
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.SymmDiff
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Monotonicity.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Measure spaces

This file defines measure spaces, the almost-everywhere filter and `AEMeasurable` functions.
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
that two measures are equal.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

This file does not import `MeasureTheory.MeasurableSpace.Basic`, but only `MeasurableSpace.Defs`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/

@[expose] public section

assert_not_exists Module.Basis

noncomputable section

open Set Function MeasurableSpace Topology Filter ENNReal NNReal

open Filter hiding map

variable {α β γ δ : Type*} {ι : Sort*}

namespace MeasureTheory

/-- A measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

The measure of a set `s`, denoted `μ s`, is an extended nonnegative real. The real-valued version
is written `μ.real s`.
-/
structure Measure (α : Type*) [MeasurableSpace α] extends OuterMeasure α where
  m_iUnion ⦃f : ℕ → Set α⦄ : (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) →
    toOuterMeasure (⋃ i, f i) = ∑' i, toOuterMeasure (f i)
  trim_le : toOuterMeasure.trim ≤ toOuterMeasure

/-- Notation for `Measure` with respect to a non-standard σ-algebra in the domain. -/
scoped notation "Measure[" mα "] " α:arg => @Measure α mα

theorem Measure.toOuterMeasure_injective [MeasurableSpace α] :
    Injective (toOuterMeasure : Measure α → OuterMeasure α)
  | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

instance Measure.instFunLike [MeasurableSpace α] : FunLike (Measure α) (Set α) ℝ≥0∞ where
  coe μ := μ.toOuterMeasure
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, h => toOuterMeasure_injective <| DFunLike.coe_injective h


instance Measure.instOuterMeasureClass [MeasurableSpace α] : OuterMeasureClass (Measure α) α where
  measure_empty m := measure_empty (μ := m.toOuterMeasure)
  measure_iUnion_nat_le m := m.iUnion_nat
  measure_mono m := m.mono

/-- The real-valued version of a measure. Maps infinite measure sets to zero. Use as `μ.real s`.
The API is developed in `Mathlib/MeasureTheory/Measure/Real.lean`. -/
protected def Measure.real {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) : ℝ :=
  (μ s).toReal

theorem measureReal_def {α : Type*} {m : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ.real s = (μ s).toReal := rfl

alias Measure.real_def := measureReal_def

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
        rw [inducedOuterMeasure_eq m0 mU (MeasurableSet.iUnion hf), mU hf hd]
        congr; funext n; rw [inducedOuterMeasure_eq m0 mU]
    trim_le := le_inducedOuterMeasure.2 fun s hs ↦ by
      rw [OuterMeasure.trim_eq _ hs, inducedOuterMeasure_eq m0 mU hs] }

theorem ofMeasurable_apply {m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}
    {m0 : m ∅ MeasurableSet.empty = 0}
    {mU :
      ∀ ⦃f : ℕ → Set α⦄ (h : ∀ i, MeasurableSet (f i)),
        Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) = ∑' i, m (f i) (h i)}
    (s : Set α) (hs : MeasurableSet s) : ofMeasurable m m0 mU s = m s hs :=
  inducedOuterMeasure_eq m0 mU hs

@[ext]
theorem ext (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  toOuterMeasure_injective <| by
  rw [← trimmed, OuterMeasure.trim_congr (h _), trimmed]

theorem ext_iff' : μ₁ = μ₂ ↔ ∀ s, μ₁ s = μ₂ s :=
  ⟨by rintro rfl s; rfl, fun h ↦ Measure.ext (fun s _ ↦ h s)⟩

theorem outerMeasure_le_iff {m : OuterMeasure α} : m ≤ μ.1 ↔ ∀ s, MeasurableSet s → m s ≤ μ s := by
  simpa only [μ.trimmed] using OuterMeasure.le_trim_iff (m₂ := μ.1)

lemma mono_null ⦃s t : Set α⦄ (h : s ⊆ t) (ht : μ t = 0) : μ s = 0 := measure_mono_null h ht

end Measure

@[simp] theorem Measure.coe_toOuterMeasure (μ : Measure α) : ⇑μ.toOuterMeasure = μ := rfl

theorem Measure.toOuterMeasure_apply (μ : Measure α) (s : Set α) :
    μ.toOuterMeasure s = μ s :=
  rfl

theorem measure_eq_trim (s : Set α) : μ s = μ.toOuterMeasure.trim s := by
  rw [μ.trimmed, μ.coe_toOuterMeasure]

theorem measure_eq_iInf (s : Set α) : μ s = ⨅ (t) (_ : s ⊆ t) (_ : MeasurableSet t), μ t := by
  rw [measure_eq_trim, OuterMeasure.trim_eq_iInf, μ.coe_toOuterMeasure]

/-- A variant of `measure_eq_iInf` which has a single `iInf`. This is useful when applying a
  lemma next that only works for non-empty infima, in which case you can use
  `nonempty_measurable_superset`. -/
theorem measure_eq_iInf' (μ : Measure α) (s : Set α) :
    μ s = ⨅ t : { t // s ⊆ t ∧ MeasurableSet t }, μ t := by
  simp_rw [iInf_subtype, iInf_and, ← measure_eq_iInf]

theorem measure_eq_inducedOuterMeasure :
    μ s = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty s :=
  measure_eq_trim _

theorem toOuterMeasure_eq_inducedOuterMeasure :
    μ.toOuterMeasure = inducedOuterMeasure (fun s _ => μ s) MeasurableSet.empty μ.empty :=
  μ.trimmed.symm

theorem measure_eq_extend (hs : MeasurableSet s) :
    μ s = extend (fun t (_ht : MeasurableSet t) => μ t) s := by
  rw [extend_eq]
  exact hs

theorem nonempty_of_measure_ne_zero (h : μ s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' => h <| h'.symm ▸ measure_empty

theorem measure_mono_top (h : s₁ ⊆ s₂) (h₁ : μ s₁ = ∞) : μ s₂ = ∞ :=
  top_unique <| h₁ ▸ measure_mono h

@[simp, mono]
theorem measure_le_measure_union_left : μ s ≤ μ (s ∪ t) := μ.mono subset_union_left

@[simp, mono]
theorem measure_le_measure_union_right : μ t ≤ μ (s ∪ t) := μ.mono subset_union_right

/-- For every set there exists a measurable superset of the same measure. -/
theorem exists_measurable_superset (μ : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s := by
  simpa only [← measure_eq_trim] using μ.toOuterMeasure.exists_measurable_superset_eq_trim s

/-- For every set `s` and a countable collection of measures `μ i` there exists a measurable
superset `t ⊇ s` such that each measure `μ i` takes the same value on `s` and `t`. -/
theorem exists_measurable_superset_forall_eq [Countable ι] (μ : ι → Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = μ i s := by
  simpa only [← measure_eq_trim] using
    OuterMeasure.exists_measurable_superset_forall_eq_trim (fun i => (μ i).toOuterMeasure) s

theorem exists_measurable_superset₂ (μ ν : Measure α) (s : Set α) :
    ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = μ s ∧ ν t = ν s := by
  simpa only [Bool.forall_bool.trans and_comm] using
    exists_measurable_superset_forall_eq (fun b => cond b μ ν) s

theorem exists_measurable_superset_of_null (h : μ s = 0) : ∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0 :=
  h ▸ exists_measurable_superset μ s

theorem exists_measurable_superset_iff_measure_eq_zero :
    (∃ t, s ⊆ t ∧ MeasurableSet t ∧ μ t = 0) ↔ μ s = 0 :=
  ⟨fun ⟨_t, hst, _, ht⟩ => measure_mono_null hst ht, exists_measurable_superset_of_null⟩

theorem measure_biUnion_lt_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) < ∞) : μ (⋃ i ∈ s, f i) < ∞ := by
  convert (measure_biUnion_finset_le (μ := μ) hs.toFinset f).trans_lt _ using 3
  · ext
    rw [Finite.mem_toFinset]
  · simpa only [ENNReal.sum_lt_top, Finite.mem_toFinset]

@[aesop (rule_sets := [finiteness]) safe apply]
theorem measure_biUnion_ne_top {s : Set β} {f : β → Set α} (hs : s.Finite)
    (hfin : ∀ i ∈ s, μ (f i) ≠ ∞) : μ (⋃ i ∈ s, f i) ≠ ∞ :=
  (measure_biUnion_lt_top hs (fun i hi ↦ Ne.lt_top (hfin i hi ·))).ne

theorem measure_union_lt_top (hs : μ s < ∞) (ht : μ t < ∞) : μ (s ∪ t) < ∞ :=
  (measure_union_le s t).trans_lt (ENNReal.add_lt_top.mpr ⟨hs, ht⟩)

@[simp]
theorem measure_union_lt_top_iff : μ (s ∪ t) < ∞ ↔ μ s < ∞ ∧ μ t < ∞ := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => measure_union_lt_top h.1 h.2⟩
  · exact (measure_mono Set.subset_union_left).trans_lt h
  · exact (measure_mono Set.subset_union_right).trans_lt h

@[aesop (rule_sets := [finiteness]) safe apply]
theorem measure_union_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∪ t) ≠ ∞ :=
  (measure_union_lt_top hs.lt_top ht.lt_top).ne

open scoped symmDiff in
@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
theorem measure_symmDiff_ne_top (hs : μ s ≠ ∞) (ht : μ t ≠ ∞) : μ (s ∆ t) ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) <| measure_mono symmDiff_subset_union

@[simp]
theorem measure_union_eq_top_iff : μ (s ∪ t) = ∞ ↔ μ s = ∞ ∨ μ t = ∞ :=
  not_iff_not.1 <| by simp only [← lt_top_iff_ne_top, ← Ne.eq_def, not_or, measure_union_lt_top_iff]

theorem exists_measure_pos_of_not_measure_iUnion_null [Countable ι] {s : ι → Set α}
    (hs : μ (⋃ n, s n) ≠ 0) : ∃ n, 0 < μ (s n) := by
  contrapose! hs
  exact measure_iUnion_null fun n => nonpos_iff_eq_zero.1 (hs n)

theorem measure_lt_top_of_subset (hst : t ⊆ s) (hs : μ s ≠ ∞) : μ t < ∞ :=
  lt_of_le_of_lt (μ.mono hst) hs.lt_top

theorem measure_ne_top_of_subset (h : t ⊆ s) (ht : μ s ≠ ∞) : μ t ≠ ∞ :=
  (measure_lt_top_of_subset h ht).ne

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem measure_inter_ne_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) ≠ ∞ :=
  measure_ne_top_of_subset inter_subset_left hs_finite

theorem measure_inter_lt_top_of_left_ne_top (hs_finite : μ s ≠ ∞) : μ (s ∩ t) < ∞ := by
  finiteness

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem measure_inter_ne_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) ≠ ∞ :=
  measure_ne_top_of_subset inter_subset_right ht_finite

theorem measure_inter_lt_top_of_right_ne_top (ht_finite : μ t ≠ ∞) : μ (s ∩ t) < ∞ := by
  finiteness

theorem measure_inter_null_of_null_right (S : Set α) {T : Set α} (h : μ T = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_right h

theorem measure_inter_null_of_null_left {S : Set α} (T : Set α) (h : μ S = 0) : μ (S ∩ T) = 0 :=
  measure_mono_null inter_subset_left h

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
theorem _root_.MeasurableSpace.ae_induction_on_inter
    {α β : Type*} [MeasurableSpace β] {μ : Measure β}
    {C : β → Set α → Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = MeasurableSpace.generateFrom s)
    (h_inter : IsPiSystem s) (h_empty : ∀ᵐ x ∂μ, C x ∅) (h_basic : ∀ᵐ x ∂μ, ∀ t ∈ s, C x t)
    (h_compl : ∀ᵐ x ∂μ, ∀ t, MeasurableSet t → C x t → C x tᶜ)
    (h_union : ∀ᵐ x ∂μ, ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C x (f i)) → C x (⋃ i, f i)) :
    ∀ᵐ x ∂μ, ∀ ⦃t⦄, MeasurableSet t → C x t := by
  filter_upwards [h_empty, h_basic, h_compl, h_union] with x hx_empty hx_basic hx_compl hx_union
    using MeasurableSpace.induction_on_inter (C := fun t _ ↦ C x t)
      h_eq h_inter hx_empty hx_basic hx_compl hx_union

end ae

open Classical in
/-- A measurable set `t ⊇ s` such that `μ t = μ s`. It even satisfies `μ (t ∩ u) = μ (s ∩ u)` for
any measurable set `u` if `μ s ≠ ∞`, see `measure_toMeasurable_inter`.
This property holds without the assumption `μ s ≠ ∞` when the space is s-finite (for example
σ-finite); see `measure_toMeasurable_inter_of_sFinite`.
If `s` is a null measurable set, then
we also have `t =ᵐ[μ] s`, see `NullMeasurableSet.toMeasurable_ae_eq`.
This notion is sometimes called a "measurable hull" in the literature. -/
irreducible_def toMeasurable (μ : Measure α) (s : Set α) : Set α :=
  if h : ∃ t, t ⊇ s ∧ MeasurableSet t ∧ t =ᵐ[μ] s then h.choose else
    if h' : ∃ t, t ⊇ s ∧ MeasurableSet t ∧
      ∀ u, MeasurableSet u → μ (t ∩ u) = μ (s ∩ u) then h'.choose
    else (exists_measurable_superset μ s).choose

theorem subset_toMeasurable (μ : Measure α) (s : Set α) : s ⊆ toMeasurable μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.1, h's.choose_spec.1, (exists_measurable_superset μ s).choose_spec.1]

theorem ae_le_toMeasurable : s ≤ᵐ[μ] toMeasurable μ s :=
  HasSubset.Subset.eventuallyLE (subset_toMeasurable _ _)

@[simp]
theorem measurableSet_toMeasurable (μ : Measure α) (s : Set α) :
    MeasurableSet (toMeasurable μ s) := by
  rw [toMeasurable_def]; split_ifs with hs h's
  exacts [hs.choose_spec.2.1, h's.choose_spec.2.1,
          (exists_measurable_superset μ s).choose_spec.2.1]

@[simp]
theorem measure_toMeasurable (s : Set α) : μ (toMeasurable μ s) = μ s := by
  rw [toMeasurable_def]; split_ifs with hs h's
  · exact measure_congr hs.choose_spec.2.2
  · simpa only [inter_univ] using h's.choose_spec.2.2 univ MeasurableSet.univ
  · exact (exists_measurable_superset μ s).choose_spec.2.2

/-- A measure space is a measurable space equipped with a
  measure, referred to as `volume`. -/
class MeasureSpace (α : Type*) extends MeasurableSpace α where
  volume : Measure α

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
  `(tactic| exact MeasureTheory.MeasureSpace.volume)

end MeasureSpace

end

end MeasureTheory

section

open MeasureTheory

/-!
### Almost everywhere measurable functions

A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function. We define this property, called `AEMeasurable f μ`. It's properties are discussed in
`MeasureTheory.MeasureSpace`.
-/


variable {m : MeasurableSpace α} [MeasurableSpace β] {f g : α → β} {μ ν : Measure α}

/-- A function is almost everywhere measurable if it coincides almost everywhere with a measurable
function.

A similar notion is `MeasureTheory.NullMeasurable`. That notion is equivalent to `AEMeasurable` if
the σ-algebra on the codomain is countably generated, but weaker in general. -/
@[fun_prop]
def AEMeasurable {_m : MeasurableSpace α} (f : α → β) (μ : Measure α := by volume_tac) : Prop :=
  ∃ g : α → β, Measurable g ∧ f =ᵐ[μ] g

/-- A function is `m`-`AEMeasurable` with respect to a measure `μ` if it coincides almost everywhere
with a `m`-measurable function. -/
scoped[MeasureTheory] notation "AEMeasurable[" m "]" => @AEMeasurable _ _ _ m

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @AEMeasurable ..])
  (by fun_prop (disch := measurability))

@[fun_prop]
theorem Measurable.aemeasurable (h : Measurable f) : AEMeasurable f μ :=
  ⟨f, h, ae_eq_refl f⟩

namespace AEMeasurable

@[fun_prop]
lemma of_discrete [DiscreteMeasurableSpace α] : AEMeasurable f μ :=
  Measurable.of_discrete.aemeasurable

/-- Given an almost everywhere measurable function `f`, associate to it a measurable function
that coincides with it almost everywhere. `f` is explicit in the definition to make sure that
it shows in pretty-printing. -/
def mk (f : α → β) (h : AEMeasurable f μ) : α → β :=
  Classical.choose h

@[fun_prop]
theorem measurable_mk (h : AEMeasurable f μ) : Measurable (h.mk f) :=
  (Classical.choose_spec h).1

theorem ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f :=
  (Classical.choose_spec h).2

theorem congr (hf : AEMeasurable f μ) (h : f =ᵐ[μ] g) : AEMeasurable g μ :=
  ⟨hf.mk f, hf.measurable_mk, h.symm.trans hf.ae_eq_mk⟩

end AEMeasurable

theorem aemeasurable_congr (h : f =ᵐ[μ] g) : AEMeasurable f μ ↔ AEMeasurable g μ :=
  ⟨fun hf => AEMeasurable.congr hf h, fun hg => AEMeasurable.congr hg h.symm⟩

@[simp, fun_prop]
theorem aemeasurable_const {b : β} : AEMeasurable (fun _a : α => b) μ :=
  measurable_const.aemeasurable

@[fun_prop]
theorem aemeasurable_id : AEMeasurable id μ :=
  measurable_id.aemeasurable

@[fun_prop]
theorem aemeasurable_id' : AEMeasurable (fun x => x) μ :=
  measurable_id.aemeasurable

theorem Measurable.comp_aemeasurable [MeasurableSpace δ] {f : α → δ} {g : δ → β} (hg : Measurable g)
    (hf : AEMeasurable f μ) : AEMeasurable (g ∘ f) μ :=
  ⟨g ∘ hf.mk f, hg.comp hf.measurable_mk, EventuallyEq.fun_comp hf.ae_eq_mk _⟩

@[fun_prop]
theorem Measurable.comp_aemeasurable' [MeasurableSpace δ] {f : α → δ} {g : δ → β}
    (hg : Measurable g) (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ g (f x)) μ :=
  Measurable.comp_aemeasurable hg hf

variable {δ : Type*} {X : δ → Type*} {mX : ∀ a, MeasurableSpace (X a)}

protected theorem AEMeasurable.eval {g : α → Π a, X a} (hg : AEMeasurable g μ) (a : δ) :
    AEMeasurable (fun x ↦ g x a) μ := by
  use fun x ↦ hg.mk g x a, hg.measurable_mk.eval
  exact hg.ae_eq_mk.mono fun _ h ↦ congrFun h _

variable [Countable δ]

theorem aemeasurable_pi_iff {g : α → Π a, X a} :
    AEMeasurable g μ ↔ ∀ a, AEMeasurable (fun x ↦ g x a) μ := by
  constructor
  · exact AEMeasurable.eval
  · intro h
    use fun x a ↦ (h a).mk _ x, measurable_pi_lambda _ fun a ↦ (h a).measurable_mk
    exact (eventually_countable_forall.mpr fun a ↦ (h a).ae_eq_mk).mono fun _ h ↦ funext h

@[fun_prop]
theorem aemeasurable_pi_lambda (f : α → Π a, X a) (hf : ∀ a, AEMeasurable (fun c ↦ f c a) μ) :
    AEMeasurable f μ :=
  aemeasurable_pi_iff.mpr hf

end
