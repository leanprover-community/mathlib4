/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.AdjoinRoot.Basic

/-!
# Algebra homomorphism between adjoining a root of unity.

## Main definitions and results

The main definitions are in the `AdjoinRoot` namespace.

*  `mapCyclotomic f : (X ^ r - 1 : R[X]) →ₐ[R] AdjoinRoot (X ^ r - 1 : R[X]) `,
    an algebra homomorphism.
*  `mapCyclotomic_injective`, the given algebra homomorphism is injective.
-/


open Ideal Polynomial

@[expose] public section

namespace AdjoinRoot

variable (R : Type*) [CommRing R] (r j k : ℕ)

/-- The algebra homomorphism taking an element to the `k`-th power. -/
noncomputable def mapCyclotomic :
    AdjoinRoot (X ^ r - 1 : R[X]) →ₐ[R] AdjoinRoot (X ^ r - 1 : R[X]) :=
  quotientMapₐ _ (aeval (X ^ k))
    (by simpa [mem_span_singleton, pow_right_comm] using sub_one_dvd_pow_sub_one (X ^ r) k)

@[simp]
theorem mapCyclotomic_mk_eq_mk (f : R[X]) :
    mapCyclotomic R r k (mk (X ^ r - 1) f) = mk (X ^ r - 1) (f.comp (X ^ k)) :=
  rfl

@[simp]
theorem mapCyclotomic_root_eq_mk :
    mapCyclotomic R r k (root (X ^ r - 1)) = mk (X ^ r - 1) (X ^ k) := by
  simp [← mk_X]

@[simp]
theorem mapCyclotomic_one (R : Type*) [CommRing R] (r : ℕ) : mapCyclotomic R r 1 = 1 := by
  ext
  simp

@[simp]
theorem mapCyclotomic_mul (R : Type*) [CommRing R] (r j k : ℕ) :
    mapCyclotomic R r (j * k) = mapCyclotomic R r j * mapCyclotomic R r k := by
  ext
  simp [pow_mul]

theorem mapCyclotomic_apply_eq {R : Type*} [CommRing R] {r j k : ℕ} (h : j ≡ k [MOD r]) :
    mapCyclotomic R r j = mapCyclotomic R r k := by
  ext
  rw [mapCyclotomic_root_eq_mk, mapCyclotomic_root_eq_mk, AdjoinRoot.mk_eq_mk]
  wlog hjk : k ≤ j generalizing j k
  · rw [dvd_sub_comm]
    exact this h.symm (le_of_not_ge hjk)
  · rw [← Nat.add_sub_cancel' hjk, pow_add, ← mul_sub_one]
    exact dvd_mul_of_dvd_right (dvd_pow_sub_one_of_dvd ((Nat.modEq_iff_dvd' hjk).mp h.symm)) (X ^ k)

@[simp]
theorem mapCyclotomic_mod : mapCyclotomic R r (k % r) = mapCyclotomic R r k  :=
  mapCyclotomic_apply_eq (Nat.mod_modEq k r)

/-- The algebra homomorphism taking an element to the `k`-th power. -/
noncomputable def mapCyclotomicHom :
    ZMod r →* AdjoinRoot (X ^ r - 1 : R[X]) →ₐ[R] AdjoinRoot (X ^ r - 1 : R[X]) where
  toFun k := mapCyclotomic R r k.val
  map_one' := by simp [ZMod.val_one_eq_one_mod]
  map_mul' k l := by simp [ZMod.val_mul]

/-- The algebra homomorphism taking an element to the `k`-th power. -/
noncomputable def mapCyclotomicUnitHom :
    (ZMod r)ˣ →* AdjoinRoot (X ^ r - 1 : R[X]) ≃ₐ[R] AdjoinRoot (X ^ r - 1 : R[X]) where
  toFun k := AlgEquiv.ofAlgHom (mapCyclotomicHom R r k) (mapCyclotomicHom R r k⁻¹)
    (by ext; simp [← AlgHom.mul_apply, ← map_mul]) (by ext; simp [← AlgHom.mul_apply, ← map_mul])
  map_one' := by ext; simp
  map_mul' j k := by ext; simp

theorem mapCyclotomic_injective (h : k.Coprime r) : Function.Injective (mapCyclotomic R r k) := by
  rw [← mapCyclotomic_mod, ← ZMod.val_natCast]
  exact (mapCyclotomicUnitHom R r (ZMod.unitOfCoprime k h)).injective

end AdjoinRoot
