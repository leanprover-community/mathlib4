module

public import Mathlib

variable (α : Type*) {β : Type*} [Group α] [MulAction α β] (b : β)

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst (α : Type*) {β : Type*} [Group α]
    [MulAction α β] (b : β) (a : α) :
    ((MulAction.orbitProdStabilizerEquivGroup α b).symm a).1 = a • b := rfl

@[to_additive (attr := simp)]
theorem MulAction.orbitProdStabilizerEquivGroup_apply_smul (x : orbit α b) (y : stabilizer α b) :
    MulAction.orbitProdStabilizerEquivGroup α b (x, y) • b = x := by
  rw [← MulAction.orbitProdStabilizerEquivGroup_symm_apply_fst, Equiv.symm_apply_apply]
