/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux

! This file was ported from Lean 3 source module topology.continuous_function.units
! leanprover-community/mathlib commit a148d797a1094ab554ad4183a4ad6f130358ef64
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.Units
import Mathlib.Algebra.Algebra.Spectrum
import Mathlib.Topology.ContinuousFunction.Algebra

/-!
# Units of continuous functions

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/


variable {X M R 𝕜 : Type _} [TopologicalSpace X]

namespace ContinuousMap

section Monoid

variable [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
@[to_additive
      "Equivalence between continuous maps into the additive units of an additive monoid\nwith continuous addition and the additive units of the additive monoid of continuous maps.",
  simps]
def unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where
  toFun f :=
    { val := ⟨fun x => f x, Units.continuous_val.comp f.Continuous⟩
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_val.comp (continuous_inv.comp f.Continuous)⟩
      val_inv := ext fun x => Units.mul_inv _
      inv_val := ext fun x => Units.inv_mul _ }
  invFun f :=
    { toFun := fun x =>
        ⟨f x, f⁻¹ x, ContinuousMap.congr_fun f.mul_inv x, ContinuousMap.congr_fun f.inv_mul x⟩
      continuous_toFun :=
        continuous_induced_rng.2 <|
          Continuous.prod_mk (f : C(X, M)).Continuous <|
            MulOpposite.continuous_op.comp (↑f⁻¹ : C(X, M)).Continuous }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
#align continuous_map.units_lift ContinuousMap.unitsLift
#align continuous_map.add_units_lift ContinuousMap.addUnitsLift

end Monoid

section NormedRing

variable [NormedRing R] [CompleteSpace R]

theorem NormedRing.isUnit_unit_continuous {f : C(X, R)} (h : ∀ x, IsUnit (f x)) :
    Continuous fun x => (h x).Unit := by
  refine'
    continuous_induced_rng.2
      (Continuous.prod_mk f.continuous
        (mul_opposite.continuous_op.comp (continuous_iff_continuous_at.mpr fun x => _)))
  have := NormedRing.inverse_continuousAt (h x).Unit
  simp only [← Ring.inverse_unit, IsUnit.unit_spec, ← Function.comp_apply] at this ⊢
  exact this.comp (f.continuous_at x)
#align normed_ring.is_unit_unit_continuous NormedRing.isUnit_unit_continuous

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def unitsOfForallIsUnit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) : C(X, Rˣ) where
  toFun x := (h x).Unit
  continuous_toFun := NormedRing.isUnit_unit_continuous h
#align continuous_map.units_of_forall_is_unit ContinuousMap.unitsOfForallIsUnit

instance canLift :
    CanLift C(X, R) C(X, Rˣ) (fun f => ⟨fun x => f x, Units.continuous_val.comp f.Continuous⟩)
      fun f => ∀ x, IsUnit (f x)
    where prf f h := ⟨unitsOfForallIsUnit h, by ext; rfl⟩
#align continuous_map.can_lift ContinuousMap.canLift

theorem isUnit_iff_forall_isUnit (f : C(X, R)) : IsUnit f ↔ ∀ x, IsUnit (f x) :=
  Iff.intro (fun h => fun x => ⟨unitsLift.symm h.Unit x, rfl⟩) fun h =>
    ⟨(unitsOfForallIsUnit h).unitsLift, by ext; rfl⟩
#align continuous_map.is_unit_iff_forall_is_unit ContinuousMap.isUnit_iff_forall_isUnit

end NormedRing

section NormedField

variable [NormedField 𝕜] [CompleteSpace 𝕜]

theorem isUnit_iff_forall_ne_zero (f : C(X, 𝕜)) : IsUnit f ↔ ∀ x, f x ≠ 0 := by
  simp_rw [f.is_unit_iff_forall_is_unit, isUnit_iff_ne_zero]
#align continuous_map.is_unit_iff_forall_ne_zero ContinuousMap.isUnit_iff_forall_ne_zero

theorem spectrum_eq_range (f : C(X, 𝕜)) : spectrum 𝕜 f = Set.range f := by
  ext
  simp only [spectrum.mem_iff, is_unit_iff_forall_ne_zero, not_forall, coe_sub, Pi.sub_apply,
    algebraMap_apply, Algebra.id.smul_eq_mul, mul_one, Classical.not_not, Set.mem_range,
    sub_eq_zero, @eq_comm _ x _]
#align continuous_map.spectrum_eq_range ContinuousMap.spectrum_eq_range

end NormedField

end ContinuousMap

