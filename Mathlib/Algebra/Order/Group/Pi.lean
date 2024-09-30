/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Order properties of `Pi.single`
-/

namespace Pi
variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}

@[to_additive (attr := simp)]
lemma mulSingle_le_mulSingle : mulSingle i a ≤ mulSingle i b ↔ a ≤ b := by
  simp [mulSingle, update_le_update_iff]

@[to_additive (attr := gcongr)] alias ⟨_, GCongr.mulSingle_mono⟩ := mulSingle_le_mulSingle

@[to_additive (attr := simp) single_nonneg]
lemma one_le_mulSingle : 1 ≤ mulSingle i a ↔ 1 ≤ a := by simp [mulSingle]

@[to_additive (attr := simp)]
lemma mulSingle_le_one : mulSingle i a ≤ 1 ↔ a ≤ 1 := by simp [mulSingle]

end Pi
