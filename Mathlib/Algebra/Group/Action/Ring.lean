/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Algebra.Module.End
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Action of a Ring on a Module

-/

variable (X : Type*) [AddCommGroup X]
variable {M : Type*} [Ring M] [Module M X]

open AddMonoidHom in
open Module in
lemma ker_id_sub_eq_range  {p : M} (h : IsIdempotentElem p) :
    ker (toAddMonoidEnd M X (1 - p)) = range (toAddMonoidEnd M X p) := by
  ext x
  rw [mem_ker, mem_range, map_sub, map_one, sub_apply, toAddMonoidEnd_apply_apply, sub_eq_zero,
    AddMonoid.End.coe_one, id_eq]
  simp_rw [toAddMonoidEnd_apply_apply]
  exact ⟨fun h => ⟨x,h.symm⟩, fun ⟨y,hy⟩ => by
    rw [← hy, ← smul_assoc, smul_eq_mul, h]⟩
