/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import Mathlib.Topology.Instances.ENNReal
import Mathlib.MeasureTheory.Measure.Dirac

#align_import probability.probability_mass_function.basic from "leanprover-community/mathlib"@"4ac69b290818724c159de091daa3acd31da0ee6d"

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in `ProbabilityMassFunction/Monad.lean`,
other constructions of `Pmf`s are found in `ProbabilityMassFunction/Constructions.lean`.

Given `p : Pmf α`, `Pmf.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `Pmf.toMeasure`.
`Pmf.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPmf` constructs a `Pmf` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/


noncomputable section

variable {α β γ : Type*}

open Classical BigOperators NNReal ENNReal MeasureTheory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }
#align pmf Pmf

namespace Pmf

instance funLike : FunLike (Pmf α) α fun _ => ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h
#align pmf.fun_like Pmf.funLike

@[ext]
protected theorem ext {p q : Pmf α} (h : ∀ x, p x = q x) : p = q :=
  FunLike.ext p q h
#align pmf.ext Pmf.ext

theorem ext_iff {p q : Pmf α} : p = q ↔ ∀ x, p x = q x :=
  FunLike.ext_iff
#align pmf.ext_iff Pmf.ext_iff

theorem hasSum_coe_one (p : Pmf α) : HasSum p 1 :=
  p.2
#align pmf.has_sum_coe_one Pmf.hasSum_coe_one

@[simp]
theorem tsum_coe (p : Pmf α) : ∑' a, p a = 1 :=
  p.hasSum_coe_one.tsum_eq
#align pmf.tsum_coe Pmf.tsum_coe

theorem tsum_coe_ne_top (p : Pmf α) : ∑' a, p a ≠ ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top
#align pmf.tsum_coe_ne_top Pmf.tsum_coe_ne_top

theorem tsum_coe_indicator_ne_top (p : Pmf α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl) ENNReal.summable
      ENNReal.summable)
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))
#align pmf.tsum_coe_indicator_ne_top Pmf.tsum_coe_indicator_ne_top

@[simp]
theorem coe_ne_zero (p : Pmf α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)
#align pmf.coe_ne_zero Pmf.coe_ne_zero

/-- The support of a `Pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.support p
#align pmf.support Pmf.support

@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl
#align pmf.mem_support_iff Pmf.mem_support_iff

@[simp]
theorem support_nonempty (p : Pmf α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero
#align pmf.support_nonempty Pmf.support_nonempty

theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]
#align pmf.apply_eq_zero_iff Pmf.apply_eq_zero_iff

theorem apply_pos_iff (p : Pmf α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm
#align pmf.apply_pos_iff Pmf.apply_pos_iff

theorem apply_eq_one_iff (p : Pmf α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine' ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => _)
    fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices : 1 < ∑' a, p a
  exact ne_of_lt this p.tsum_coe.symm
  have : 0 < ∑' b, ite (b = a) 0 (p b) := lt_of_le_of_ne' zero_le'
    ((tsum_ne_zero_iff ENNReal.summable).2
      ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩)
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero, le_rfl]
#align pmf.apply_eq_one_iff Pmf.apply_eq_one_iff

theorem coe_le_one (p : Pmf α) (a : α) : p a ≤ 1 := by
  refine' hasSum_le (fun b => _) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp only [h, zero_le', le_rfl]
#align pmf.coe_le_one Pmf.coe_le_one

theorem apply_ne_top (p : Pmf α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)
#align pmf.apply_ne_top Pmf.apply_ne_top

theorem apply_lt_top (p : Pmf α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)
#align pmf.apply_lt_top Pmf.apply_lt_top

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

/-- Construct an `OuterMeasure` from a `Pmf`, by assigning measure to each set `s : Set α` equal
  to the sum of `p x` for each `x ∈ α`. -/
def toOuterMeasure (p : Pmf α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x
#align pmf.to_outer_measure Pmf.toOuterMeasure

variable (p : Pmf α) (s t : Set α)

theorem toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s
#align pmf.to_outer_measure_apply Pmf.toOuterMeasure_apply

@[simp]
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ := by
  refine' eq_top_iff.2 <| le_trans (le_sInf fun x hx => _) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)
#align pmf.to_outer_measure_caratheodory Pmf.toOuterMeasure_caratheodory

@[simp]
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, p x := by
  refine' (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) _).trans _)
  · exact fun x hx => Set.indicator_of_not_mem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _
#align pmf.to_outer_measure_apply_finset Pmf.toOuterMeasure_apply_finset

theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a := by
  refine' (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => _).trans _)
  · exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl
#align pmf.to_outer_measure_apply_singleton Pmf.toOuterMeasure_apply_singleton

theorem toOuterMeasure_injective : (toOuterMeasure : Pmf α → OuterMeasure α).Injective :=
  fun p q h => Pmf.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)
#align pmf.to_outer_measure_injective Pmf.toOuterMeasure_injective

@[simp]
theorem toOuterMeasure_inj {p q : Pmf α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff
#align pmf.to_outer_measure_inj Pmf.toOuterMeasure_inj

theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  exact Function.funext_iff.symm.trans Set.indicator_eq_zero'
#align pmf.to_outer_measure_apply_eq_zero_iff Pmf.toOuterMeasure_apply_eq_zero_iff

theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support ⊆ s := by
  refine' (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => _, fun h => _⟩
  · refine' by_contra fun hs => ne_of_lt _ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · suffices : ∀ (x) (_ : x ∉ s), p x = 0
    exact _root_.trans (tsum_congr
      fun a => (Set.indicator_apply s p a).trans (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.not_mem_subset h ha
#align pmf.to_outer_measure_apply_eq_one_iff Pmf.toOuterMeasure_apply_eq_one_iff

@[simp]
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, Pmf.support, Set.indicator_inter_support]
#align pmf.to_outer_measure_apply_inter_support Pmf.toOuterMeasure_apply_inter_support

/-- Slightly stronger than `OuterMeasure.mono` having an intersection with `p.support`. -/
theorem toOuterMeasure_mono {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)
#align pmf.to_outer_measure_mono Pmf.toOuterMeasure_mono

theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left t p.support))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left s p.support))
#align pmf.to_outer_measure_apply_eq_of_inter_support_eq Pmf.toOuterMeasure_apply_eq_of_inter_support_eq

@[simp]
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)
#align pmf.to_outer_measure_apply_fintype Pmf.toOuterMeasure_apply_fintype

end OuterMeasure

section Measure

open MeasureTheory

/-- Since every set is Carathéodory-measurable under `Pmf.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`. -/
def toMeasure [MeasurableSpace α] (p : Pmf α) : Measure α :=
  p.toOuterMeasure.toMeasure ((toOuterMeasure_caratheodory p).symm ▸ le_top)
#align pmf.to_measure Pmf.toMeasure

variable [MeasurableSpace α] (p : Pmf α) (s t : Set α)

theorem toOuterMeasure_apply_le_toMeasure_apply : p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s
#align pmf.to_outer_measure_apply_le_to_measure_apply Pmf.toOuterMeasure_apply_le_toMeasure_apply

theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs
#align pmf.to_measure_apply_eq_to_outer_measure_apply Pmf.toMeasure_apply_eq_toOuterMeasure_apply

theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs).trans (p.toOuterMeasure_apply s)
#align pmf.to_measure_apply Pmf.toMeasure_apply

theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [toMeasure_apply_eq_toOuterMeasure_apply _ _ h, toOuterMeasure_apply_singleton]
#align pmf.to_measure_apply_singleton Pmf.toMeasure_apply_singleton

theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply p s hs, toOuterMeasure_apply_eq_zero_iff]
#align pmf.to_measure_apply_eq_zero_iff Pmf.toMeasure_apply_eq_zero_iff

theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s
#align pmf.to_measure_apply_eq_one_iff Pmf.toMeasure_apply_eq_one_iff

@[simp]
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) (hp : MeasurableSet p.support) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply s hs,
    p.toMeasure_apply_eq_toOuterMeasure_apply _ (hs.inter hp)]
#align pmf.to_measure_apply_inter_support Pmf.toMeasure_apply_inter_support

theorem toMeasure_mono {s t : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using toOuterMeasure_mono p h
#align pmf.to_measure_mono Pmf.toMeasure_mono

theorem toMeasure_apply_eq_of_inter_support_eq {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    toOuterMeasure_apply_eq_of_inter_support_eq p h
#align pmf.to_measure_apply_eq_of_inter_support_eq Pmf.toMeasure_apply_eq_of_inter_support_eq

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

theorem toMeasure_injective : (toMeasure : Pmf α → Measure α).Injective := by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x,
    ← q.toMeasure_apply_singleton x <| measurableSet_singleton x, h]
#align pmf.to_measure_injective Pmf.toMeasure_injective

@[simp]
theorem toMeasure_inj {p q : Pmf α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff
#align pmf.to_measure_inj Pmf.toMeasure_inj

@[simp]
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.measurableSet).trans
    (p.toOuterMeasure_apply_finset s)
#align pmf.to_measure_apply_finset Pmf.toMeasure_apply_finset

theorem toMeasure_apply_of_finite (hs : s.Finite) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s hs.measurableSet).trans (p.toOuterMeasure_apply s)
#align pmf.to_measure_apply_of_finite Pmf.toMeasure_apply_of_finite

@[simp]
theorem toMeasure_apply_fintype [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply s s.toFinite.measurableSet).trans
    (p.toOuterMeasure_apply_fintype s)
#align pmf.to_measure_apply_fintype Pmf.toMeasure_apply_fintype

end MeasurableSingletonClass

end Measure

end Pmf

namespace MeasureTheory

open Pmf

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `Pmf`, where the mass of a point
is the measure of the singleton set under the original measure. -/
def toPmf [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : Pmf α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩
#align measure_theory.measure.to_pmf MeasureTheory.Measure.toPmf

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]

theorem toPmf_apply (x : α) : μ.toPmf x = μ {x} := rfl
#align measure_theory.measure.to_pmf_apply MeasureTheory.Measure.toPmf_apply

@[simp]
theorem toPmf_toMeasure : μ.toPmf.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPmf.toMeasure_apply s hs, ← μ.tsum_indicator_apply_singleton s hs]
    rfl
#align measure_theory.measure.to_pmf_to_measure MeasureTheory.Measure.toPmf_toMeasure

end Measure

end MeasureTheory

namespace Pmf

open MeasureTheory

/-- The measure associated to a `Pmf` by `toMeasure` is a probability measure. -/
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : Pmf α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩
#align pmf.to_measure.is_probability_measure Pmf.toMeasure.isProbabilityMeasure

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : Pmf α) (μ : Measure α)
  [IsProbabilityMeasure μ]

@[simp]
theorem toMeasure_toPmf : p.toMeasure.toPmf = p :=
  Pmf.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x), p.toMeasure.toPmf_apply]
#align pmf.to_measure_to_pmf Pmf.toMeasure_toPmf

theorem toMeasure_eq_iff_eq_toPmf (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPmf := by rw [← toMeasure_inj, Measure.toPmf_toMeasure]
#align pmf.to_measure_eq_iff_eq_to_pmf Pmf.toMeasure_eq_iff_eq_toPmf

theorem toPmf_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPmf = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPmf_toMeasure]
#align pmf.to_pmf_eq_iff_to_measure_eq Pmf.toPmf_eq_iff_toMeasure_eq

end Pmf
