/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.ConjAct
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Conjugation action of a field on itself
-/

@[expose] public section

namespace ConjAct

variable {K : Type*} [DivisionRing K]

instance distribMulAction₀ : DistribMulAction (ConjAct K) K :=
  { ConjAct.mulAction₀ with
    smul_zero := by simp [smul_def]
    smul_add := by simp [smul_def, mul_add, add_mul] }

end ConjAct
