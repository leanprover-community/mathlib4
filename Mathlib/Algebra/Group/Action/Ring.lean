/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Group.Subgroup.Ker

variable (X : Type*) [AddCommGroup X]
variable {M : Type*} [Ring M] [Module M X]

variable (p : M)

open AddMonoidHom in
open DistribMulAction in
lemma ker_id_sub_eq_range  {p : M} (h : IsIdempotentElem p) :
    ker (toAddMonoidEnd M X (1 - p)) = range (toAddMonoidEnd M X p) := by
  ext x
  rw [mem_ker, mem_range, toAddMonoidEnd_apply, toAddMonoidHom_apply,  toAddMonoidEnd_apply,
    sub_smul, one_smul, sub_eq_zero]
  simp_rw [toAddMonoidHom_apply]
  exact ⟨fun h => ⟨x,h.symm⟩, fun ⟨y,hy⟩ => by rw [← hy, ← smul_assoc, smul_eq_mul, h]⟩
