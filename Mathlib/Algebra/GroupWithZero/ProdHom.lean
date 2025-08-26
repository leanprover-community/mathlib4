/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Homomorphisms for products of groups with zero

This file defines homomorphisms for products of groups with zero,
which is identified with the `WithZero` of the product of the units of the groups.

The product of groups with zero `WithZero (αˣ × βˣ)` is a
group with zero itself with natural inclusions.

TODO: Give `GrpWithZero` instances of `HasBinaryProducts` and `HasBinaryCoproducts`,
as well as a terminal object.

-/

namespace MonoidWithZeroHom

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
lemma one_apply_apply_eq {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) (x : M₀) :
    (1 : N₀ →*₀ G₀) (f x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
lemma one_comp {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) :
    (1 : N₀ →*₀ G₀).comp f = (1 : M₀ →*₀ G₀) :=
  ext <| one_apply_apply_eq _

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`G₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inl [DecidablePred fun x : G₀ ↦ x = 0] : G₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inl _ _)).comp
    (MonoidWithZeroHomClass.toMonoidWithZeroHom WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`H₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
def inr [DecidablePred fun x : H₀ ↦ x = 0] : H₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inr _ _)).comp
    (MonoidWithZeroHomClass.toMonoidWithZeroHom WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `G₀`, which is the group with zero that can be identified
as their product. -/
def fst : WithZero (G₀ˣ × H₀ˣ) →*₀ G₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.fst ..))

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `H₀`, which is the group with zero that can be identified
as their product. -/
def snd : WithZero (G₀ˣ × H₀ˣ) →*₀ H₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.snd ..))

variable {G₀ H₀}

@[simp]
lemma inl_apply_unit [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀ˣ) :
    inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inl]

@[simp]
lemma inr_apply_unit [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀ˣ) :
    inr G₀ H₀ x = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inr]

@[simp] lemma fst_apply_coe (x : G₀ˣ × H₀ˣ) : fst G₀ H₀ x = x.fst := rfl
@[simp] lemma snd_apply_coe (x : G₀ˣ × H₀ˣ) : snd G₀ H₀ x = x.snd := rfl

@[simp]
theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    fst _ H₀ (inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

@[simp]
theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (fst ..).comp (inl G₀ H₀) = .id _ :=
  MonoidWithZeroHom.ext fun _ ↦ fst_inl _

@[simp]
theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (snd ..).comp (inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]

theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ ↦ x = 0] {x : G₀} (hx : x ≠ 0) :
    snd _ _ (inl _ H₀ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, snd_comp_inl, one_apply_of_ne_zero hx]

@[simp]
theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (fst ..).comp (inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]

theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ ↦ x = 0] {x : H₀} (hx : x ≠ 0) :
    fst _ _ (inr G₀ _ x) = 1 := by
  rw [← MonoidWithZeroHom.comp_apply, fst_comp_inr, one_apply_of_ne_zero hx]

@[simp]
theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    snd _ _ (inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

@[simp]
theorem snd_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (snd ..).comp (inr G₀ H₀) = .id _ :=
  MonoidWithZeroHom.ext fun _ ↦ snd_inr _

lemma inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (inl G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨fst .., fun _ ↦ by simp⟩
lemma inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (inr G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨snd .., fun _ ↦ by simp⟩
lemma fst_surjective : Function.Surjective (fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ ↦ by simp⟩
lemma snd_surjective : Function.Surjective (snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ ↦ by simp⟩

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (inl G₀ H₀ m * inr G₀ H₀ n) = (m, n) := by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (inl G₀ H₀ m) (inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end MonoidWithZeroHom
