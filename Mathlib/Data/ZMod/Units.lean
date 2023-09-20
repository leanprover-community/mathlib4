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

end ZMod
