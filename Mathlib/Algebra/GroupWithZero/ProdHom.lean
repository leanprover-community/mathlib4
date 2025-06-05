/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Homomorphisms for products of groups with zero

This file defines homomorphisms for products of groups with zero,
which is identified with the `WithZero` of the product of the units of the groups.

The product of groups with zero `WithZero (αˣ × βˣ)` is a
group with zero itself with natural inclusions.

TODO: Create the "GrpWithZero" category.

-/

namespace MonoidWithZeroHom

variable (M₀ N₀ : Type*) [GroupWithZero M₀] [GroupWithZero N₀]

/-- Given groups with zero `M₀`, `N₀`, the natural inclusion ordered homomorphism from
`M₀` to `WithZero (M₀ˣ × N₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inl [DecidablePred fun x : M₀ ↦ x = 0] : M₀ →*₀ WithZero (M₀ˣ × N₀ˣ) :=
  (WithZero.map' (MonoidHom.inl _ _)).comp
    (MonoidWithZeroHomClass.toMonoidWithZeroHom (WithZero.withZeroUnitsEquiv.symm))

/-- Given groups with zero `M₀`, `N₀`, the natural inclusion ordered homomorphism from
`N₀` to `WithZero (M₀ˣ × N₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inr [DecidablePred fun x : N₀ ↦ x = 0] : N₀ →*₀ WithZero (M₀ˣ × N₀ˣ) :=
  (WithZero.map' (MonoidHom.inr _ _)).comp
    (MonoidWithZeroHomClass.toMonoidWithZeroHom (WithZero.withZeroUnitsEquiv.symm))

/-- Given groups with zero `M₀`, `N₀`, the natural projection homomorphism from
`WithZero (M₀ˣ × N₀ˣ)` to `M₀`, which is the group with zero that can be identified
as their product. -/
def fst : WithZero (M₀ˣ × N₀ˣ) →*₀ M₀ :=
  WithZero.lift' ((Units.coeHom _).comp (MonoidHom.fst ..))

/-- Given groups with zero `M₀`, `N₀`, the natural projection homomorphism from
`WithZero (M₀ˣ × N₀ˣ)` to `N₀`, which is the group with zero that can be identified
as their product. -/
def snd : WithZero (M₀ˣ × N₀ˣ) →*₀ N₀ :=
  WithZero.lift' ((Units.coeHom _).comp (MonoidHom.snd ..))

variable {M₀ N₀}

@[simp]
lemma inl_apply_unit [DecidablePred fun x : M₀ ↦ x = 0] (x : M₀ˣ) :
    inl M₀ N₀ x = ((x, (1 : N₀ˣ)) : WithZero (M₀ˣ × N₀ˣ)) := by
  simp [inl]
@[simp]
lemma inr_apply_unit [DecidablePred fun x : N₀ ↦ x = 0] (x : N₀ˣ) :
    inr M₀ N₀ x = (((1 : M₀ˣ), x) : WithZero (M₀ˣ × N₀ˣ)) := by
  simp [inr]
@[simp]
lemma fst_apply_coe (x : M₀ˣ × N₀ˣ) :
    fst M₀ N₀ x = x.fst := by
  rfl
@[simp]
lemma snd_apply_coe (x : M₀ˣ × N₀ˣ) :
    snd M₀ N₀ x = x.snd := by
  rfl

@[simp]
theorem fst_inl [DecidablePred fun x : M₀ ↦ x = 0] (x : M₀) :
    fst _ N₀ (inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]
@[simp]
theorem fst_comp_inl [DecidablePred fun x : M₀ ↦ x = 0] :
    (fst ..).comp (inl M₀ N₀) = MonoidWithZeroHom.id _ :=
  MonoidWithZeroHom.ext fun _ ↦ fst_inl _

@[simp]
theorem snd_comp_inl [DecidablePred fun x : M₀ ↦ x = 0] :
    (snd ..).comp (inl M₀ N₀) = trivial .. := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]
theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : M₀ ↦ x = 0] {x : M₀} (hx : x ≠ 0) :
    snd _ _ (inl _ N₀ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, snd_comp_inl, trivial_apply_of_ne_zero hx]

@[simp]
theorem fst_comp_inr [DecidablePred fun x : N₀ ↦ x = 0] :
    (fst ..).comp (inr M₀ N₀) = trivial .. := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]
theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : N₀ ↦ x = 0] {x : N₀} (hx : x ≠ 0) :
    fst _ _ (inr M₀ _ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, fst_comp_inr, trivial_apply_of_ne_zero hx]

@[simp]
theorem snd_inr [DecidablePred fun x : N₀ ↦ x = 0] (x : N₀) :
    snd _ _ (inr M₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]
@[simp]
theorem snd_comp_inr [DecidablePred fun x : N₀ ↦ x = 0] :
    (snd ..).comp (inr M₀ N₀) = MonoidWithZeroHom.id _ :=
  MonoidWithZeroHom.ext fun _ ↦ snd_inr _

lemma inl_injective [DecidablePred fun x : M₀ ↦ x = 0] :
    Function.Injective (inl M₀ N₀) :=
  Function.HasLeftInverse.injective ⟨fst .., fun _ ↦ by simp⟩
lemma inr_injective [DecidablePred fun x : N₀ ↦ x = 0] :
    Function.Injective (inr M₀ N₀) :=
  Function.HasLeftInverse.injective ⟨snd .., fun _ ↦ by simp⟩
lemma fst_surjective [DecidablePred fun x : M₀ ↦ x = 0] :
    Function.Surjective (fst M₀ N₀) :=
  Function.HasRightInverse.surjective ⟨inl .., fun _ ↦ by simp⟩
lemma snd_surjective [DecidablePred fun x : N₀ ↦ x = 0] :
    Function.Surjective (snd M₀ N₀) :=
  Function.HasRightInverse.surjective ⟨inr .., fun _ ↦ by simp⟩

@[simp]
lemma fst_eq_zero_iff (x : WithZero (M₀ˣ × N₀ˣ)) :
    fst M₀ N₀ x = 0 ↔ x = 0 := by
  cases x <;> simp
@[simp]
lemma snd_eq_zero_iff (x : WithZero (M₀ˣ × N₀ˣ)) :
    snd M₀ N₀ x = 0 ↔ x = 0 := by
  cases x <;> simp

variable [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]

theorem inl_mul_inr_eq_mk_of_unit (m : M₀ˣ) (n : N₀ˣ) :
    (inl M₀ N₀ m * inr M₀ N₀ n) = (m, n) := by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

theorem commute_inl_inr (m : M₀) (n : N₀) : Commute (inl M₀ N₀ m) (inr M₀ N₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m
  · simp [Commute.zero_left]
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n
  · simp [Commute.zero_right]
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end MonoidWithZeroHom
