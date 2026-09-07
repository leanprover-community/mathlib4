/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: metakunt, Thomas Browning
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Algebra homomorphism between adjoining a root of unity.

Let `S` be an `R`-algebra obtained by adjoining a root of `X ^ r - 1`, as witnessed by
`h : IsAdjoinRoot S (X ^ r - 1 : R[X])`.

## Main definitions and results

The main definitions are in the `IsAdjoinRoot` namespace.

*  `h.mapCyclotomic k : S →ₐ[R] S`, the algebra homomorphism sending the root to its `k`-th power.
*  `mapCyclotomicHom h : ZMod r →* (S →ₐ[R] S)` and
   `mapCyclotomicUnitHom h : (ZMod r)ˣ →* (S ≃ₐ[R] S)`, the monoid homomorphisms assembling these.
*  `mapCyclotomic_injective`, the given algebra homomorphism is injective when `k` and `r` are
    coprime.
-/


open Polynomial

public section

namespace IsAdjoinRoot

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {r : ℕ}
  (h : IsAdjoinRoot S (X ^ r - 1 : R[X])) (j k : ℕ)

namespace RootsOfUnity

theorem root_pow_self : h.root ^ r = 1 := by
  simpa [map_sub, sub_eq_zero] using h.aeval_root_self

theorem aeval_root_pow_self : aeval (h.root ^ k) (X ^ r - 1 : R[X]) = 0 := by
  simp [pow_right_comm, root_pow_self h]

end RootsOfUnity

/-- The algebra homomorphism taking an element to the `k`-th power. -/
noncomputable def mapCyclotomic : S →ₐ[R] S :=
  h.liftHom (h.root ^ k) (RootsOfUnity.aeval_root_pow_self h k)

@[simp]
theorem mapCyclotomic_map_eq_map (f : R[X]) :
    h.mapCyclotomic k (h.map f) = h.map (f.comp (X ^ k)) := by
  rw [mapCyclotomic, liftHom_map, ← h.aeval_root_eq_map, aeval_comp]
  simp

@[simp]
theorem mapCyclotomic_root_eq_pow : h.mapCyclotomic k h.root = h.root ^ k := h.liftHom_root _

@[simp]
theorem mapCyclotomic_one : h.mapCyclotomic 1 = 1 :=
  h.algHom_eq_of_root (by simp)

@[simp]
theorem mapCyclotomic_mul :
    h.mapCyclotomic (j * k) = h.mapCyclotomic j * h.mapCyclotomic k :=
  h.algHom_eq_of_root (by simp [AlgHom.mul_apply, ← pow_mul])

theorem mapCyclotomic_apply_eq {j k : ℕ} (hjk : j ≡ k [MOD r]) :
    h.mapCyclotomic j = h.mapCyclotomic k := by
  apply h.algHom_eq_of_root
  rw [mapCyclotomic_root_eq_pow, mapCyclotomic_root_eq_pow]
  wlog hkj : k ≤ j generalizing j k
  · exact (this hjk.symm (le_of_not_ge hkj)).symm
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' hkj).mp hjk.symm
    rw [← Nat.add_sub_cancel' hkj, hm, pow_add, pow_mul, RootsOfUnity.root_pow_self h, one_pow,
      mul_one]

@[simp]
theorem mapCyclotomic_mod : h.mapCyclotomic (k % r) = h.mapCyclotomic k :=
  h.mapCyclotomic_apply_eq (Nat.mod_modEq k r)

/-- The algebra homomorphism taking an element to the `k`-th power, as a monoid homomorphism
from `ZMod r`. -/
noncomputable def mapCyclotomicHom : ZMod r →* (S →ₐ[R] S) where
  toFun k := h.mapCyclotomic k.val
  map_one' := by simp [ZMod.val_one_eq_one_mod]
  map_mul' k l := by simp [ZMod.val_mul]

/-- The algebra equivalence taking an element to the `k`-th power, for `k` a unit of `ZMod r`. -/
noncomputable def mapCyclotomicUnitHom : (ZMod r)ˣ →* (S ≃ₐ[R] S) where
  toFun k := AlgEquiv.ofAlgHom (mapCyclotomicHom h k) (mapCyclotomicHom h k⁻¹)
    (by ext; simp [← AlgHom.mul_apply, ← map_mul]) (by ext; simp [← AlgHom.mul_apply, ← map_mul])
  map_one' := by ext; simp
  map_mul' j k := by ext; simp

theorem mapCyclotomic_injective (hk : k.Coprime r) : Function.Injective (h.mapCyclotomic k) := by
  rw [← mapCyclotomic_mod, ← ZMod.val_natCast]
  exact (h.mapCyclotomicUnitHom (ZMod.unitOfCoprime k hk)).injective

end IsAdjoinRoot
