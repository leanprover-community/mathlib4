/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.NormedSpace.Units
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Topology.ContinuousFunction.Algebra

#align_import topology.continuous_function.units from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Units of continuous functions

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/


variable {X M R 𝕜 : Type*} [TopologicalSpace X]

namespace ContinuousMap

section Monoid

variable [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
-- Porting note: `simps` made bad `simp` lemmas (LHS simplifies) so we add them manually below
@[to_additive (attr := simps apply_val_apply symm_apply_apply_val)
"Equivalence between continuous maps into the additive units of an additive monoid with continuous
addition and the additive units of the additive monoid of continuous maps."]
def unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where
  toFun f :=
    { val := ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.continuous)⟩
      val_inv := ext fun x => Units.mul_inv _
      inv_val := ext fun x => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨(f : C(X, M)) x, (↑f⁻¹ : C(X, M)) x,
          ContinuousMap.congr_fun f.mul_inv x, ContinuousMap.congr_fun f.inv_mul x⟩
      continuous_toFun := continuous_induced_rng.2 <|
        (f : C(X, M)).continuous.prod_mk <|
        MulOpposite.continuous_op.comp (↑f⁻¹ : C(X, M)).continuous }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
#align continuous_map.units_lift ContinuousMap.unitsLift
#align continuous_map.add_units_lift ContinuousMap.addUnitsLift

-- Porting note: add manually because `simps` used `inv` and `simpNF` complained
@[to_additive (attr := simp)]
lemma unitsLift_apply_inv_apply (f : C(X, Mˣ)) (x : X) :
    (↑(ContinuousMap.unitsLift f)⁻¹ : C(X, M)) x = (f x)⁻¹ :=
  rfl

-- Porting note: add manually because `simps` used `inv` and `simpNF` complained
@[to_additive (attr := simp)]
lemma unitsLift_symm_apply_apply_inv' (f : C(X, M)ˣ) (x : X) :
    (ContinuousMap.unitsLift.symm f x)⁻¹ = (↑f⁻¹ : C(X, M)) x := by
  rfl

end Monoid

section NormedRing

variable [NormedRing R] [CompleteSpace R]

theorem continuous_isUnit_unit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) :
    Continuous fun x => (h x).unit := by
  refine
    continuous_induced_rng.2
      (Continuous.prod_mk f.continuous
        (MulOpposite.continuous_op.comp (continuous_iff_continuousAt.mpr fun x => ?_)))
  have := NormedRing.inverse_continuousAt (h x).unit
  simp only
  simp only [← Ring.inverse_unit, IsUnit.unit_spec] at this ⊢
  exact this.comp (f.continuousAt x)
#align normed_ring.is_unit_unit_continuous ContinuousMap.continuous_isUnit_unit
-- Porting note: this had the worst namespace: `NormedRing`

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def unitsOfForallIsUnit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) : C(X, Rˣ) where
  toFun x := (h x).unit
  continuous_toFun := continuous_isUnit_unit h
#align continuous_map.units_of_forall_is_unit ContinuousMap.unitsOfForallIsUnit

instance canLift :
    CanLift C(X, R) C(X, Rˣ) (fun f => ⟨fun x => f x, Units.continuous_val.comp f.continuous⟩)
      fun f => ∀ x, IsUnit (f x) where
  prf f h := ⟨unitsOfForallIsUnit h, by ext; rfl⟩
#align continuous_map.can_lift ContinuousMap.canLift

theorem isUnit_iff_forall_isUnit (f : C(X, R)) : IsUnit f ↔ ∀ x, IsUnit (f x) :=
  Iff.intro (fun h => fun x => ⟨unitsLift.symm h.unit x, rfl⟩) fun h =>
    ⟨ContinuousMap.unitsLift (unitsOfForallIsUnit h), by ext; rfl⟩
#align continuous_map.is_unit_iff_forall_is_unit ContinuousMap.isUnit_iff_forall_isUnit

end NormedRing

section NormedField

variable [NormedField 𝕜] [NormedDivisionRing R] [Algebra 𝕜 R] [CompleteSpace R]

theorem isUnit_iff_forall_ne_zero (f : C(X, R)) : IsUnit f ↔ ∀ x, f x ≠ 0 := by
  simp_rw [f.isUnit_iff_forall_isUnit, isUnit_iff_ne_zero]
#align continuous_map.is_unit_iff_forall_ne_zero ContinuousMap.isUnit_iff_forall_ne_zero

theorem spectrum_eq_preimage_range (f : C(X, R)) :
    spectrum 𝕜 f = algebraMap _ _ ⁻¹' Set.range f := by
  ext x
  simp only [spectrum.mem_iff, isUnit_iff_forall_ne_zero, not_forall, sub_apply,
    algebraMap_apply, mul_one, Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ (x • 1 : R) _, Set.mem_preimage, Algebra.algebraMap_eq_smul_one,
    smul_apply, one_apply]

theorem spectrum_eq_range [CompleteSpace 𝕜] (f : C(X, 𝕜)) : spectrum 𝕜 f = Set.range f := by
  rw [spectrum_eq_preimage_range, Algebra.id.map_eq_id]
  exact Set.preimage_id
#align continuous_map.spectrum_eq_range ContinuousMap.spectrum_eq_range

end NormedField

end ContinuousMap
