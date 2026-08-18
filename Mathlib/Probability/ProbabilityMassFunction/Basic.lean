/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in
`Mathlib/Probability/ProbabilityMassFunction/Monad.lean`, other constructions of `PMF`s are found in
`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.

Given `p : PMF α`, `PMF.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `PMF.toMeasure`.
`PMF.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPMF` constructs a `PMF` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/

@[expose] public section


noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0∞` such
  that the values have (infinite) sum `1`. -/
@[deprecated "Use a linear combination of Dirac masses via Measure.sum and Measure.dirac."
  (since := "2026-07-31")]
def PMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // HasSum f 1 }

namespace PMF

@[deprecated "" (since := "2026-08-01")]
instance instFunLike : FunLike (PMF α) α ℝ≥0∞ where
  coe p a := p.1 a
  coe_injective _ _ h := Subtype.ext h

@[deprecated Measure.sum_congr (since := "2026-08-01")]
protected theorem ext {p q : PMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

@[deprecated IsProbabilityMeasure.measure_univ (since := "2026-08-01")]
theorem hasSum_coe_one (p : PMF α) : HasSum p 1 :=
  p.2

@[deprecated IsProbabilityMeasure.measure_univ (since := "2026-08-16")]
theorem tsum_coe (p : PMF α) : ∑' a, p a = 1 :=
  p.hasSum_coe_one.tsum_eq

@[deprecated measure_ne_top (since := "2026-08-16")]
theorem tsum_coe_ne_top (p : PMF α) : ∑' a, p a ≠ ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top

@[deprecated measure_ne_top (since := "2026-08-16")]
theorem tsum_coe_indicator_ne_top (p : PMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[deprecated IsProbabilityMeasure.ne_zero (since := "2026-08-16")]
theorem coe_ne_zero (p : PMF α) : ⇑p ≠ 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

/-- The support of a `PMF` is the set where it is nonzero. -/
@[deprecated "Use Function.support of the scalars." (since := "2026-08-16")]
def support (p : PMF α) : Set α :=
  Function.support p

@[deprecated Function.mem_support (since := "2026-08-16")]
theorem mem_support_iff (p : PMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

@[deprecated Function.support_nonempty_iff (since := "2026-08-16")]
theorem support_nonempty (p : PMF α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero

@[deprecated Summable.countable_support_ennreal (since := "2026-08-16")]
theorem support_countable (p : PMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

@[deprecated Function.notMem_support (since := "2026-08-16")]
theorem apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

@[deprecated Function.notMem_support (since := "2026-08-16")]
theorem apply_pos_iff (p : PMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

@[deprecated tsum_eq_single (since := "2026-08-16")]
theorem apply_eq_one_iff (p : PMF α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
    fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero, ENNReal.summable.tsum_ne_zero_iff]
    exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, ite_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => ite_eq_right hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]

@[deprecated Summable.le_tsum' (since := "2026-08-16")]
theorem coe_le_one (p : PMF α) (a : α) : p a ≤ 1 := by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]

@[deprecated measure_ne_top (since := "2026-08-16")]
theorem apply_ne_top (p : PMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

@[deprecated measure_lt_top (since := "2026-08-16")]
theorem apply_lt_top (p : PMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

section OuterMeasure

open OuterMeasure

/-- Construct an `OuterMeasure` from a `PMF`, by assigning measure to each set `s : Set α` equal
  to the sum of `p x` for each `x ∈ α`. -/
@[deprecated "Use a linear combination of Dirac masses via OuterMeasure.sum and OuterMeasure.dirac."
  (since := "2026-08-16")]
def toOuterMeasure (p : PMF α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x

@[deprecated OuterMeasure.sum_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply (p : PMF α) (s : Set α) : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

@[deprecated "Use OuterMeasure.le_sum_caratheodory, OuterMeasure.le_smul_caratheodory and
  OuterMeasure.dirac_caratheodory." (since := "2026-08-16")]
theorem toOuterMeasure_caratheodory (p : PMF α) : p.toOuterMeasure.caratheodory = ⊤ := by
  refine eq_top_iff.2 <| le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[deprecated OuterMeasure.sum_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply_finset (p : PMF α) (s : Finset α) :
    p.toOuterMeasure s = ∑ x ∈ s, p x := by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _

@[deprecated OuterMeasure.sum_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply_singleton (p : PMF α) (a : α) : p.toOuterMeasure {a} = p a := by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
  · classical exact ite_eq_right_iff.2 fun hb' => False.elim <| hb hb'
  · classical exact ite_eq_left_iff.2 fun ha' => False.elim <| ha' rfl

@[deprecated congrArg (since := "2026-08-16")]
theorem toOuterMeasure_injective : (toOuterMeasure : PMF α → OuterMeasure α).Injective :=
  fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[deprecated congrArg (since := "2026-08-16")]
theorem toOuterMeasure_inj {p q : PMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff

@[deprecated Measure.sum_eq_zero (since := "2026-08-16")]
theorem toOuterMeasure_apply_eq_zero_iff (p : PMF α) (s : Set α) :
    p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply, ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

@[deprecated tsum_subtype_eq_of_support_subset (since := "2026-08-16")]
theorem toOuterMeasure_apply_eq_one_iff (p : PMF α) (s : Set α) :
    p.toOuterMeasure s = 1 ↔ p.support ⊆ s := by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
    have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim <| hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices ∀ (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
    exact fun a ha => (p.apply_eq_zero_iff a).2 <| Set.notMem_subset h ha

@[deprecated OuterMeasure.sum_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply_inter_support (p : PMF α) (s : Set α) :
    p.toOuterMeasure (s ∩ p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

@[deprecated measure_mono_ae (since := "2026-08-16")]
theorem toOuterMeasure_mono (p : PMF α) {s t : Set α} (h : s ∩ p.support ⊆ t) :
    p.toOuterMeasure s ≤ p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

@[deprecated MeasureTheory.measure_congr (since := "2026-08-16")]
theorem toOuterMeasure_apply_eq_of_inter_support_eq (p : PMF α) {s t : Set α}
    (h : s ∩ p.support = t ∩ p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[deprecated Measure.finsetSum_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply_fintype [Fintype α] (p : PMF α) (s : Set α) :
    p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

end OuterMeasure

section Measure

/-- Since every set is Carathéodory-measurable under `PMF.toOuterMeasure`,
  we can further extend this `OuterMeasure` to a `Measure` on `α`. -/
@[deprecated "Use a linear combination of Dirac masses via Measure.sum and Measure.dirac."
  (since := "2026-08-16")]
def toMeasure [MeasurableSpace α] (p : PMF α) : Measure α :=
  p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

variable [MeasurableSpace α] {s : Set α}

@[deprecated le_toMeasure_apply (since := "2026-08-16")]
theorem toOuterMeasure_apply_le_toMeasure_apply (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s

@[deprecated toMeasure_apply (since := "2026-08-16")]
theorem toMeasure_apply_eq_toOuterMeasure_apply (p : PMF α) (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs

@[deprecated Measure.sum_apply (since := "2026-08-16")]
theorem toMeasure_apply (p : PMF α) (hs : MeasurableSet s) :
    p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)

@[deprecated Measure.sum_smul_dirac_singleton (since := "2026-08-16")]
theorem toMeasure_apply_singleton (p : PMF α) (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]

@[deprecated Measure.sum_eq_zero (since := "2026-08-16")]
theorem toMeasure_apply_eq_zero_iff (p : PMF α) (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_eq_zero_iff]

@[deprecated tsum_subtype_eq_of_support_subset (since := "2026-08-16")]
theorem toMeasure_apply_eq_one_iff (p : PMF α) (hs : MeasurableSet s) :
    p.toMeasure s = 1 ↔ p.support ⊆ s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s

@[deprecated measure_mono_ae (since := "2026-08-16")]
theorem toMeasure_mono (p : PMF α) {t : Set α} (hs : MeasurableSet s)
    (h : s ∩ p.support ⊆ t) : p.toMeasure s ≤ p.toMeasure t := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[deprecated measure_congr (since := "2026-08-16")]
theorem toMeasure_apply_inter_support (p : PMF α) (hs : MeasurableSet s) :
    p.toMeasure (s ∩ p.support) = p.toMeasure s :=
  (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[deprecated Measure.restrict_eq_self_of_ae_mem (since := "2026-08-16")]
theorem restrict_toMeasure_support (p : PMF α) : p.toMeasure.restrict p.support = p.toMeasure := by
  ext s hs
  rw [Measure.restrict_apply hs, p.toMeasure_apply_inter_support hs]

@[deprecated measure_congr (since := "2026-08-16")]
theorem toMeasure_apply_eq_of_inter_support_eq (p : PMF α) {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s ∩ p.support = t ∩ p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

@[deprecated congrArg (since := "2026-08-16")]
theorem toMeasure_injective : (toMeasure : PMF α → Measure α).Injective := by
  intro p q h
  refine PMF.ext fun x ↦ ?_
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x,
    ← q.toMeasure_apply_singleton x <| measurableSet_singleton x, h]

@[deprecated congrArg (since := "2026-08-16")]
theorem toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff

@[deprecated MeasureTheory.toMeasure_apply (since := "2026-08-16")]
theorem toMeasure_apply_eq_toOuterMeasure (p : PMF α) (s : Set α) :
    p.toMeasure s = p.toOuterMeasure s := by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support, Measure.restrict_apply' p.support_countable.measurableSet,
    p.toMeasure_apply_eq_toOuterMeasure_apply hs, toOuterMeasure_apply_inter_support]

@[deprecated Measure.sum_apply (since := "2026-08-16")]
theorem toMeasure_apply_finset (p : PMF α) (s : Finset α) : p.toMeasure s = ∑ x ∈ s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)

@[deprecated Measure.sum_apply (since := "2026-08-16")]
theorem toMeasure_apply_eq_tsum (p : PMF α) (s : Set α) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[deprecated Measure.finsetSum_apply (since := "2026-08-16")]
theorem toMeasure_apply_fintype (p : PMF α) (s : Set α) [Fintype α] :
    p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

end MeasurableSingletonClass

end Measure

end PMF

namespace MeasureTheory

open PMF

namespace Measure

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
we can convert any probability measure into a `PMF`, where the mass of a point
is the measure of the singleton set under the original measure. -/
@[deprecated "Use a linear combination of Dirac masses via Measure.sum and Measure.dirac."
  (since := "2026-08-16")]
def toPMF [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : PMF α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]

@[deprecated Measure.sum_smul_dirac_singleton (since := "2026-08-16")]
theorem toPMF_apply (x : α) : μ.toPMF x = μ {x} := rfl

@[deprecated rfl (since := "2026-08-16")]
theorem toPMF_toMeasure : μ.toPMF.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs, ← μ.tsum_indicator_apply_singleton s hs]
    rfl

end Measure

end MeasureTheory

namespace PMF

@[deprecated "" (since := "2026-08-16")]
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : PMF α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

@[deprecated rfl (since := "2026-08-16")]
theorem toMeasure_toPMF (p : PMF α) : p.toMeasure.toPMF = p :=
  PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x), p.toMeasure.toPMF_apply]

@[deprecated Iff.rfl (since := "2026-08-16")]
theorem toMeasure_eq_iff_eq_toPMF (p : PMF α) (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPMF := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

@[deprecated Iff.rfl (since := "2026-08-16")]
theorem toPMF_eq_iff_toMeasure_eq (p : PMF α) (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPMF = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

end PMF
