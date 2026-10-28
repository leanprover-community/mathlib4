/-
Copyright (c) 2024 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Violeta Hernández Palacios, Lua Viana Reis
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.GroupTheory.Torsion

/-!
# Vitali set and its non-measurability

This file defines a Vitali set and proves that it is not measurable.
The proof constructs it by taking a representative of each coset
-/

public section

open Set Filter Real MeasureTheory

noncomputable section

/-- The additive subgroup of `UnitAddCircle` consisting of the images of the rational numbers. -/
def ratAddCircle : AddSubgroup UnitAddCircle :=
  (Rat.castHom ℝ : ℚ →+ ℝ).range.map (QuotientAddGroup.mk' _)

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

/-- If `vitaliSet` is null-measurable, then it is a fundamental domain for the action of
`ratAddCircle` on `UnitAddCircle`. -/
lemma isAddFundamentalDomain_vitaliSet (hm : NullMeasurableSet vitaliSet volume) :
    IsAddFundamentalDomain ratAddCircle vitaliSet volume :=
  .mk' hm existsUnique_vadd_mem_vitaliSet

/-- `ratAddCircle` is countable, being the image of the countable type `ℚ`. -/
instance : Countable ratAddCircle := (Set.countable_range _).image _

/-- If `vitaliSet` is null-measurable, then the volume of `UnitAddCircle` is the sum of countably
many copies of the volume of `vitaliSet`. -/
lemma one_eq_tsum_volume_vitaliSet (hm : NullMeasurableSet vitaliSet volume) :
    1 = ∑' _ : ratAddCircle, volume vitaliSet := by
  simpa [Set.vadd_set_univ] using (isAddFundamentalDomain_vitaliSet hm).measure_eq_tsum Set.univ

/-- `ratAddCircle` is infinite: it contains the point `1 / n`, of order `n`, for every `n > 0`,
while in a finite group every element has order at most the cardinality. -/
instance : Infinite ratAddCircle := by
  refine not_finite_iff_infinite.1 fun _ ↦ ?_
  let n := Nat.card ratAddCircle + 1
  let x : ratAddCircle := ⟨_, _, ⟨(1 / n : ℚ), rfl⟩, rfl⟩
  have hx : addOrderOf x = n := by
    rw [← AddSubgroup.addOrderOf_coe]
    simpa [x, n] using
      AddCircle.addOrderOf_period_div (p := (1 : ℝ)) (Nat.card ratAddCircle).succ_pos
  have := addOrderOf_le_card (x := x)
  omega

/-- `vitaliSet` is not null-measurable. -/
theorem not_nullMeasurableSet_vitaliSet : ¬ NullMeasurableSet vitaliSet volume := by
  intro hm
  have h := one_eq_tsum_volume_vitaliSet hm
  rcases eq_or_ne (volume vitaliSet) 0 with hz | hnz
  · simp [hz] at h
  · rw [ENNReal.tsum_const_eq_top_of_ne_zero hnz] at h
    exact ENNReal.one_ne_top h

/-- `vitaliSet` is not measurable. -/
theorem not_measurableSet_vitaliSet : ¬ MeasurableSet vitaliSet :=
  fun hm ↦ not_nullMeasurableSet_vitaliSet hm.nullMeasurableSet

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
  fun hm ↦ not_nullMeasurableSet_preimage_vitaliSet hm.nullMeasurableSet
