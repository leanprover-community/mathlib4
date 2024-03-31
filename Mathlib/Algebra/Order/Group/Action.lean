import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Results about `CovariantClass G α HSMul.hSMul LE.le`

When working with group actions rather than modules, we drop the `0 < c` condition.
-/

variable {ι : Sort*} {M α : Type*}

theorem smul_mono_right [Monoid M] [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) : Monotone (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _

theorem smul_inf_le [Monoid M] [SMul M α] [SemilatticeInf α] [CovariantClass M α HSMul.hSMul LE.le]
    (m : M) (a₁ a₂ : α) : m • (a₁ ⊓ a₂) ≤ m • a₁ ⊓ m • a₂ :=
  le_inf (smul_mono_right _ inf_le_left) (smul_mono_right _ inf_le_right)

theorem smul_iInf_le
    [Monoid M] [SMul M α] [CompleteLattice α] [CovariantClass M α HSMul.hSMul LE.le]
    {m : M} {t : ι → α} :
    m • iInf t ≤ ⨅ i, m • t i :=
  le_iInf fun _ => smul_mono_right _ (iInf_le _ _)

theorem smul_strict_mono_right
    {M α : Type*} [Monoid M] [SMul M α] [Preorder α] [CovariantClass M α HSMul.hSMul LT.lt]
    (m : M) :
    StrictMono (HSMul.hSMul m : α → α) :=
  fun _ _ => CovariantClass.elim _
