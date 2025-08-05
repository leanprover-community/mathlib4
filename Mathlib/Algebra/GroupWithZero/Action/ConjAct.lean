/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a group with zero on itself
-/

assert_not_exists Ring

variable {α G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

instance : GroupWithZero (ConjAct G₀) := ‹GroupWithZero G₀›

@[simp] lemma ofConjAct_zero : ofConjAct 0 = (0 : G₀) := rfl
@[simp] lemma toConjAct_zero : toConjAct (0 : G₀) = 0 := rfl

instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

instance smulCommClass₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀ where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

instance smulCommClass₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

end ConjAct
