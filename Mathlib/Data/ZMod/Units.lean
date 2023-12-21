/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ashvni Narayanan, Michael Stoll
-/
import Mathlib.Data.ZMod.Basic


/-!
# Lemmas about units in `ZMod`.
-/


namespace ZMod

variable {n m : ℕ}
/-- `unitsMap` is a group homomorphism that maps units of `ZMod m` to units of `ZMod n` when `n`
divides `m`. -/
def unitsMap (hm : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))

lemma unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n)) := rfl

lemma unitsMap_comp {d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| castHom_comp hm hd

@[simp]
lemma unitsMap_self (n : ℕ) : unitsMap (dvd_refl n) = MonoidHom.id _ := by
  simp [unitsMap, castHom_self]

lemma IsUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) :  IsUnit ((a : ZMod m) : ZMod n) :=
  Units.isUnit (unitsMap hm a)

end ZMod
