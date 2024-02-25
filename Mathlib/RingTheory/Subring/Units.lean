/-
Copyright (c) 2021 Chris Birbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.GroupTheory.Submonoid.Order
import Mathlib.RingTheory.Subring.Basic

/-!

# Unit subgroups of a ring

-/

def Units.posSubgroup (R : Type*) [LinearOrderedSemiring R] : Subgroup Rˣ :=
  { (Submonoid.pos R).comap (Units.coeHom R) with
    carrier := { x | (0 : R) < x }
    inv_mem' := Units.inv_pos.mpr }
#align units.pos_subgroup Units.posSubgroup

@[simp]
theorem Units.mem_posSubgroup {R : Type*} [LinearOrderedSemiring R] (u : Rˣ) :
    u ∈ Units.posSubgroup R ↔ (0 : R) < u :=
  Iff.rfl
#align units.mem_pos_subgroup Units.mem_posSubgroup
