/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.measure_space
! leanprover-community/mathlib commit 88fcb83fe7996142dfcfe7368d31304a9adc874a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.p2

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/


noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace

open TopologicalSpace (SecondCountableTopology)

open Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type _}

namespace MeasureTheory

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) := by
  rw [h] at ht_ne_top
  refine' le_antisymm (measure_mono (inter_subset_inter_left _ htu)) _
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_diff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_diff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) :=
        add_le_add le_rfl (measure_mono (diff_subset_diff htu Subset.rfl))

  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono (diff_subset _ _)) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A
#align measure_theory.measure.measure_inter_eq_of_measure_eq MeasureTheory.Measure.measure_inter_eq_of_measure_eq

/-- The measurable superset `to_measurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is sigma_finite, see `measure_to_measurable_inter_of_sigma_finite`. -/
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm
#align measure_theory.measure.measure_to_measurable_inter MeasureTheory.Measure.measure_toMeasurable_inter

/-! ### The `ℝ≥0∞`-module of measures -/


instance [MeasurableSpace α] : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_unionᵢ := fun _f _hf _hd => tsum_zero.symm
      trimmed := OuterMeasure.trim_zero }⟩

@[simp]
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl
#align measure_theory.measure.zero_to_outer_measure MeasureTheory.Measure.zero_toOuterMeasure

-- porting note: TODO: @[simp, norm_cast]
@[simp]
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl
#align measure_theory.measure.coe_zero MeasureTheory.Measure.coe_zero

instance [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by
    ext1 s _
    rw [eq_empty_of_isEmpty s]; simp only [measure_empty]⟩

theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0
#align measure_theory.measure.eq_zero_of_is_empty MeasureTheory.Measure.eq_zero_of_isEmpty

instance [MeasurableSpace α] : Inhabited (Measure α) :=
  ⟨0⟩

instance [MeasurableSpace α] : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_unionᵢ := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, μ₁ (s i) + μ₂ (s i) by
          rw [ENNReal.tsum_add, measure_unionᵢ hd hs, measure_unionᵢ hd hs]
      trimmed := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl
#align measure_theory.measure.add_to_outer_measure MeasureTheory.Measure.add_toOuterMeasure

-- porting note: TODO: @[norm_cast]
@[simp]
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl
#align measure_theory.measure.coe_add MeasureTheory.Measure.coe_add

theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl
#align measure_theory.measure.add_apply MeasureTheory.Measure.add_apply

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

-- porting note: TODO: refactor
instance [MeasurableSpace α] : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_unionᵢ := fun s hs hd => by
        rw [← smul_one_smul ℝ≥0∞ c (_ : OuterMeasure α)]
        conv_lhs =>
          change OuterMeasure.measure_of ((c • @OfNat.ofNat _ 1 One.toOfNat1 : ℝ≥0∞) • μ.toOuterMeasure) (⋃ i, s i)
          change (c • @OfNat.ofNat _ 1 One.toOfNat1 : ℝ≥0∞) * OuterMeasure.measure_of μ.toOuterMeasure (⋃ i, s i)
        conv_rhs =>
          change ∑' i, OuterMeasure.measure_of ((c • @OfNat.ofNat _ 1 One.toOfNat1 : ℝ≥0∞) • μ.toOuterMeasure) (s i)
          change ∑' i, (c • @OfNat.ofNat _ 1 One.toOfNat1 : ℝ≥0∞) * OuterMeasure.measure_of (μ.toOuterMeasure) (s i)
        simp_rw [measure_unionᵢ hd hs, ENNReal.tsum_mul_left]
      trimmed := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl
#align measure_theory.measure.smul_to_outer_measure MeasureTheory.Measure.smul_toOuterMeasure

-- porting note: TODO: @[simp, norm_cast]
@[simp]
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • μ :=
  rfl
#align measure_theory.measure.coe_smul MeasureTheory.Measure.coe_smul

@[simp]
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl
#align measure_theory.measure.smul_apply MeasureTheory.Measure.smul_apply

instance [SMulCommClass R R' ℝ≥0∞] [MeasurableSpace α] : SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

instance [SMul R R'] [IsScalarTower R R' ℝ≥0∞] [MeasurableSpace α] :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

instance [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] [MeasurableSpace α] :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

instance [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

instance addCommMonoid [MeasurableSpace α] : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _
#align measure_theory.measure.add_comm_monoid MeasureTheory.Measure.addCommMonoid

/-- Coercion to function as an additive monoid homomorphism. -/
def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.measure.coe_add_hom MeasureTheory.Measure.coeAddHom

@[simp]
theorem coe_finset_sum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i) := coeAddHom.map_sum μ I
#align measure_theory.measure.coe_finset_sum MeasureTheory.Measure.coe_finset_sum

theorem finset_sum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i in I, μ i) s = ∑ i in I, μ i s := by rw [coe_finset_sum, Finset.sum_apply]
#align measure_theory.measure.finset_sum_apply MeasureTheory.Measure.finset_sum_apply

instance [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

@[simp]
theorem coe_nNReal_smul_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl
#align measure_theory.measure.coe_nnreal_smul_apply MeasureTheory.Measure.coe_nNReal_smul_apply

theorem ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
    simp only [ae_iff, Algebra.id.smul_eq_mul, smul_apply, or_iff_right_iff_imp, mul_eq_zero]
    simp only [IsEmpty.forall_iff, hc]
#align measure_theory.measure.ae_smul_measure_iff MeasureTheory.Measure.ae_smul_measure_iff

theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine' le_antisymm (measure_mono h') _
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := add_le_add le_rfl (measure_mono h')

  apply ENNReal.le_of_add_le_add_right _ this
  simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne.def, coe_add] at h
  exact h.2
#align measure_theory.measure.measure_eq_left_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq

theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
#align measure_theory.measure.measure_eq_right_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_right_of_subset_of_measure_add_eq

theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine' (measure_inter_eq_of_measure_eq hs _ (subset_toMeasurable _ _) _).symm
  · refine'
      measure_eq_left_of_subset_of_measure_add_eq _ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne.def, coe_add] at ht
    exact ht.1
#align measure_theory.measure.measure_to_measurable_add_inter_left MeasureTheory.Measure.measure_toMeasurable_add_inter_left

theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht⊢
  exact measure_toMeasurable_add_inter_left hs ht
#align measure_theory.measure.measure_to_measurable_add_inter_right MeasureTheory.Measure.measure_toMeasurable_add_inter_right

/-! ### The complete lattice of measures -/


/-- Measures are partially ordered.

The definition of less equal here is equivalent to the definition without the
measurable set condition, and this is shown by `measure.le_iff'`. It is defined
this way since, to prove `μ ≤ ν`, we may simply `intros s hs` instead of rewriting followed
by `intros s hs`. -/
instance [MeasurableSpace α] : PartialOrder (Measure α) where
  le m₁ m₂ := ∀ s, MeasurableSet s → m₁ s ≤ m₂ s
  le_refl m s _hs := le_rfl
  le_trans m₁ m₂ m₃ h₁ h₂ s hs := le_trans (h₁ s hs) (h₂ s hs)
  le_antisymm m₁ m₂ h₁ h₂ := ext fun s hs => le_antisymm (h₁ s hs) (h₂ s hs)

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s :=
  Iff.rfl
#align measure_theory.measure.le_iff MeasureTheory.Measure.le_iff

theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := by
  rw [← μ₂.trimmed, OuterMeasure.le_trim_iff]; rfl
#align measure_theory.measure.to_outer_measure_le MeasureTheory.Measure.toOuterMeasure_le

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s :=
  toOuterMeasure_le.symm
#align measure_theory.measure.le_iff' MeasureTheory.Measure.le_iff'

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_le.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]
#align measure_theory.measure.lt_iff MeasureTheory.Measure.lt_iff

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_le.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]
#align measure_theory.measure.lt_iff' MeasureTheory.Measure.lt_iff'

instance covariant_add_le [MeasurableSpace α] :
    CovariantClass (Measure α) (Measure α) (· + ·) (· ≤ ·) :=
  ⟨fun _ν _μ₁ _μ₂ hμ s hs => add_le_add_left (hμ s hs) _⟩
#align measure_theory.measure.covariant_add_le MeasureTheory.Measure.covariant_add_le

protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s hs => le_add_left (h s hs)
#align measure_theory.measure.le_add_left MeasureTheory.Measure.le_add_left

protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s hs => le_add_right (h s hs)
#align measure_theory.measure.le_add_right MeasureTheory.Measure.le_add_right
