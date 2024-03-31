import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.
-/

theorem smul_mono_right
    {M α : Type*} [Monoid M] [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) :
    Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

theorem smul_strict_mono_right
    {M α : Type*} [Monoid M] [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) :
    StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _
