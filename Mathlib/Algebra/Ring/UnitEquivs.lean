/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez, Johan Commelin
-/
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RingTheory.Subring.Basic

/-!
# Equivalences relating to units

This file makes a couple equivalences that deal with unit groups under various other operations,
such as centralizers and stabilizers. These are mainly useful to prove Wedderburn's little theorem.

-/

variable {D : Type*}

/-- The stabilizer of `Dˣ` acting on itself by conjugation at `x : Dˣ` is exactly the
units of the centralizer of `x : D`. -/
def unitsCentralizerEquiv [Monoid D] (x : Dˣ) :
 MulAction.stabilizer (ConjAct Dˣ) x ≃* (Submonoid.centralizer ({↑x} : Set D))ˣ where
  toFun := MonoidHom.toHomUnits <|
  ⟨⟨fun u ↦ ⟨↑(ConjAct.ofConjAct u.1 : Dˣ), by
    rintro x ⟨rfl⟩; have : _ • _ = _ := u.2
    rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩, rfl⟩,
    fun a b ↦ rfl⟩
  invFun u := ⟨ConjAct.toConjAct (Units.map (Submonoid.centralizer ({↑x} : Set D)).subtype u), by
      change _ • _ = _
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
      exact Units.ext <| (u.1.2 x <| Set.mem_singleton _).symm⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' := map_mul _

/-- `unitsCentralizerEquiv` for a `Ring`. Restated for Wedderburn's little theorem. -/
def unitsCentralizerEquivSubring [Ring D] (x : Dˣ) :
 MulAction.stabilizer (ConjAct Dˣ) x ≃* (Subring.centralizer ({↑x} : Set D))ˣ :=
unitsCentralizerEquiv x

variable (D)

/-- For a monoid, the units of the center inject into the center of the units. This is not an
equivalence in general; one case when it is is for groups with zero, which is covered in
`centerUnitsEquivUnitsCenter`. -/
def unitsCenterToCenterUnits [Monoid D] : (Submonoid.center D)ˣ →* Submonoid.center (Dˣ) :=
(Units.map (Submonoid.center D).subtype).codRestrict _ <| fun u r ↦ Units.ext <| u.1.prop r

theorem unitsCenterToCenterUnits_injective [Monoid D] :
  Function.Injective (unitsCenterToCenterUnits D) := by
  intros a b h
  ext
  simp only [unitsCenterToCenterUnits, MonoidHom.codRestrict_apply, Subtype.mk.injEq] at h
  exact Units.ext_iff.mp h

/-- For a group with zero, the center of the units is the same as the units of the center. -/
def centerUnitsEquivUnitsCenter [GroupWithZero D] : Subgroup.center (Dˣ) ≃* (Submonoid.center D)ˣ
    where
  toFun := MonoidHom.toHomUnits <|
    ⟨⟨fun u ↦ ⟨(u : Dˣ), fun r ↦ by
      rcases eq_or_ne r 0 with (rfl | hr)
      · rw [mul_zero, zero_mul]
      exact congrArg Units.val <| u.2 <| Units.mk0 r hr⟩, rfl⟩, fun _ _ ↦ rfl⟩
  invFun u := unitsCenterToCenterUnits D u
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' := map_mul _

/-- `centerUnitsEquivUnitsCenter` but instead for `Subring.center`. This is convenient for
Wedderburn's little theorem. -/
def centerUnitsEquivUnitsRingCenter [DivisionRing D] :
    Subgroup.center (Dˣ) ≃* (Subring.center D)ˣ := centerUnitsEquivUnitsCenter D
