import Mathlib.Data.Finite.Defs
import Mathlib.Algebra.Group.Action.Defs

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

open scoped Pointwise

namespace Set
variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

@[to_additive (attr := simp)]
lemma finite_smul_set : (a • s).Finite ↔ s.Finite := finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]
lemma infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

end Set
