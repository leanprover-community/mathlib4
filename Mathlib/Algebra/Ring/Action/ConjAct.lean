/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

@[expose] public section

/-!
# Conjugation action of a ring on itself
-/

assert_not_exists Field

namespace ConjAct
variable {R : Type*} [Semiring R]

instance unitsMulSemiringAction : MulSemiringAction (ConjAct Rˣ) R :=
  { ConjAct.unitsMulDistribMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

end ConjAct
