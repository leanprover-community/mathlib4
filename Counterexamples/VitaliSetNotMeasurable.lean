/-
Copyright (c) 2024 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Violeta Hernández Palacios, Lua Viana Reis
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Vitali set and its non-measurability

This file defines a Vitali set and proves that it is not measurable.

The construction is made by taking a representative of each coset of the subgroup of rational
numbers in the unit circle. This set is a fundamental domain for the left action of the subgroup,
meaning its translates form a partition of the unit circle.

A similar construction would work for any countable infinite subgroup of a group with a
left-invariant non-zero finite measure.
-/

public section

open Set Filter Real MeasureTheory

noncomputable section

/-- The additive subgroup of `UnitAddCircle` consisting of the images of the rational numbers. -/
def ratAddCircle : AddSubgroup UnitAddCircle :=
  (AddCircle.map (1 : ℚ) (Rat.castHom ℝ) (by simp)).range

/-- The quotient of `UnitAddCircle` by the action of `ratAddCircle` on the left. -/
def vitaliType : Type := AddAction.orbitRel.Quotient ratAddCircle UnitAddCircle

/-- The Vitali set is the range of `Quotient.out` on `vitaliType`, i.e. the range of some
arbitrary choice function. -/
def vitaliSet : Set UnitAddCircle := Set.range fun x : vitaliType ↦ x.out

/-- `vitaliSet` contains exactly one representative of each coset of `ratAddCircle`. -/
lemma isComplement_vitaliSet : AddSubgroup.IsComplement ratAddCircle vitaliSet :=
  AddSubgroup.isComplement_range_right Quotient.out_eq'

/-- Since `vitaliSet` is a complement of `ratAddCircle`, every point of `UnitAddCircle` has exactly
one translate by an element of `ratAddCircle` lying in `vitaliSet`. -/
lemma existsUnique_vadd_mem_vitaliSet (x : UnitAddCircle) :
    ∃! g : ratAddCircle, g + x ∈ vitaliSet :=
  isComplement_vitaliSet.existsUnique_add_mem_right x

/-- If `vitaliSet` were null-measurable, then it would be a fundamental domain for the action of
`ratAddCircle` on `UnitAddCircle`. -/
lemma isAddFundamentalDomain_vitaliSet (hm : NullMeasurableSet vitaliSet volume) :
    IsAddFundamentalDomain ratAddCircle vitaliSet volume :=
  .mk' hm existsUnique_vadd_mem_vitaliSet

/-- `ratAddCircle` is countable, being the image of the countable type `AddCircle (1 : ℚ)`. -/
instance : Countable ratAddCircle := Set.countable_range _

/-- If `vitaliSet` were null-measurable, then the volume of `UnitAddCircle` would be the sum of
countably many copies of the volume of `vitaliSet`. -/
lemma one_eq_tsum_volume_vitaliSet (hm : NullMeasurableSet vitaliSet volume) :
    1 = ∑' _ : ratAddCircle, volume vitaliSet := by
  simpa [Set.vadd_set_univ] using (isAddFundamentalDomain_vitaliSet hm).measure_eq_tsum Set.univ

/-- `ratAddCircle` is infinite, being the image of the infinite group `AddCircle (1 : ℚ)` under an
injective homomorphism. -/
instance : Infinite ratAddCircle :=
  (Set.infinite_range_of_injective
    (AddCircle.map_injective _ Rat.cast_injective Rat.cast_one)).to_subtype

/-- `vitaliSet` is not null-measurable. -/
theorem not_nullMeasurableSet_vitaliSet : ¬ NullMeasurableSet vitaliSet volume :=
  fun hm ↦ by simpa [ENNReal.top_mul', apply_ite] using one_eq_tsum_volume_vitaliSet hm

/-- `vitaliSet` is not measurable. -/
theorem not_measurableSet_vitaliSet : ¬ MeasurableSet vitaliSet :=
  MeasurableSet.nullMeasurableSet.mt not_nullMeasurableSet_vitaliSet

/-! ### A non-measurable subset of `ℝ` -/

/-- The preimage of `vitaliSet` in `ℝ` is not null-measurable. -/
theorem not_nullMeasurableSet_preimage_vitaliSet :
    ¬ NullMeasurableSet (((↑) : ℝ → UnitAddCircle) ⁻¹' vitaliSet) volume := by
  intro hm
  apply not_nullMeasurableSet_vitaliSet
  have hg : QuasiMeasurePreserving
      (fun x : UnitAddCircle ↦ (AddCircle.equivIoc 1 0 x : ℝ)) volume volume :=
    ((measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc 1)).quasiMeasurePreserving.mono_right
      Measure.restrict_le_self.absolutelyContinuous
  convert hm.preimage hg
  ext x
  simp [AddCircle.coe_equivIoc]

/-- The preimage of `vitaliSet` in `ℝ` is not measurable. -/
theorem not_measurableSet_preimage_vitaliSet :
    ¬ MeasurableSet (((↑) : ℝ → UnitAddCircle) ⁻¹' vitaliSet) :=
  MeasurableSet.nullMeasurableSet.mt not_nullMeasurableSet_preimage_vitaliSet
