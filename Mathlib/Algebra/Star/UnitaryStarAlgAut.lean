/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.Unitary

/-!
# The ⋆-algebra automorphism given by a unitary element

This file defines the ⋆-algebra automorphism on `R` given by a unitary `u`,
which is `Unitary.conjStarAlgAut S R u`, defined to be `x ↦ u * x * star u`.
-/

@[expose] public section

namespace Unitary
variable {S R : Type*} [Semiring R] [StarMul R]
  [SMul S R] [IsScalarTower S R R] [SMulCommClass S R R]

variable (S R) in
/-- Each unitary element `u` defines a ⋆-algebra automorphism such that
`x ↦ u * x * star u`.

This is the ⋆-algebra automorphism version of a specialized version of
`MulSemiringAction.toAlgAut`. -/
def conjStarAlgAut : unitary R →* (R ≃⋆ₐ[S] R) where
  toFun u :=
  { toRingEquiv := MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u)
    map_smul' _ _ := smul_comm _ _ _ |>.symm
    map_star' _ := by
      dsimp [ConjAct.units_smul_def]
      simp [mul_assoc, ← Unitary.star_eq_inv] }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_smul]

@[simp] theorem conjStarAlgAut_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R u x = u * x * (star u : R) := rfl

theorem conjStarAlgAut_symm_apply (u : unitary R) (x : R) :
    (conjStarAlgAut S R u).symm x = (star u : R) * x * u := rfl

theorem conjStarAlgAut_star_apply (u : unitary R) (x : R) :
    conjStarAlgAut S R (star u) x = (star u : R) * x * u := by simp

@[simp] theorem conjStarAlgAut_symm (u : unitary R) :
    (conjStarAlgAut S R u).symm = conjStarAlgAut S R (star u) := by
  ext; simp [conjStarAlgAut_symm_apply]

theorem conjStarAlgAut_trans_conjStarAlgAut (u₁ u₂ : unitary R) :
    (conjStarAlgAut S R u₁).trans (conjStarAlgAut S R u₂) = conjStarAlgAut S R (u₂ * u₁) :=
  map_mul _ _ _ |>.symm

theorem conjStarAlgAut_mul_apply (u₁ u₂ : unitary R) (x : R) :
    conjStarAlgAut S R (u₁ * u₂) x = conjStarAlgAut S R u₁ (conjStarAlgAut S R u₂ x) := by simp

theorem toRingEquiv_conjStarAlgAut (u : unitary R) :
    (conjStarAlgAut S R u).toRingEquiv =
      MulSemiringAction.toRingEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

theorem toAlgEquiv_conjStarAlgAut {S : Type*} [CommSemiring S] [Algebra S R] (u : unitary R) :
    (conjStarAlgAut S R u).toAlgEquiv =
      MulSemiringAction.toAlgEquiv _ R (ConjAct.toConjAct <| toUnits u) :=
  rfl

theorem conjStarAlgAut_ext_iff {S : Type*} [CommSemiring S] [Algebra S R] [Algebra.IsCentral S R]
    (u v : unitary R) : conjStarAlgAut S R u = conjStarAlgAut S R v ↔ ∃ α : S, (u : R) = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, Units.eq_inv_mul_iff_mul_eq, mul_smul_comm,
    mul_one, eq_comm]

theorem conjStarAlgAut_ext_iff' {R S : Type*} [Ring R] [StarMul R] [CommRing S] [StarMul S]
    [Algebra S R] [StarModule S R] [Algebra.IsCentral S R] [IsCancelMulZero S]
    [Module.IsTorsionFree S R] (u v : unitary R) :
    conjStarAlgAut S R u = conjStarAlgAut S R v ↔ ∃ α : unitary S, u = α • v := by
  conv_lhs => rw [eq_comm]
  simp_rw [StarAlgEquiv.ext_iff, conjStarAlgAut_apply, ← coe_star, star_eq_inv,
    ← val_inv_toUnits_apply, ← val_toUnits_apply, mul_assoc, ← Units.eq_inv_mul_iff_mul_eq,
    ← mul_assoc, Units.eq_mul_inv_iff_mul_eq, mul_assoc, ← mul_assoc (((toUnits v)⁻¹ : Rˣ) : R),
    ← Subalgebra.mem_center_iff (R := S), Algebra.IsCentral.center_eq_bot, Algebra.mem_bot,
    Set.mem_range, Algebra.algebraMap_eq_smul_one, val_inv_toUnits_apply, val_toUnits_apply,
    ← star_eq_inv, coe_star]
  refine ⟨fun ⟨y, h⟩ ↦ ?_, fun ⟨y, h⟩ ↦ ⟨(y : S), by
    simp only [h, coe_smul, mul_smul_comm, SetLike.coe_mem, star_mul_self_of_mem]; rfl⟩⟩
  have huv : (u : R) = y • (v : R) := by simpa [← mul_assoc] using congr(v * $h).symm
  have hvu : (v : R) = star y • (u : R) := by simpa [← mul_assoc] using congr(u * (star $h)).symm
  have hvy : (v : R) = (star y * y) • (v : R) := by simp [← smul_smul, ← huv, ← hvu]
  nth_rw 1 [← one_smul S (v : R)] at hvy
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, eq_comm] at hvy
  obtain (this | this) := hvy
  · exact ⟨⟨y, by simp [mem_iff, this, mul_comm y]⟩, by ext; exact huv⟩
  · exact ⟨1, by ext; simp [this, huv] at huv ⊢⟩

end Unitary
