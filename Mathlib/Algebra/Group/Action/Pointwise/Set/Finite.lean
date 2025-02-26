/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Data.Finite.Prod

/-! # Finiteness lemmas for pointwise operations on sets -/

open scoped Pointwise
namespace Set
variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

@[to_additive (attr := simp)]
theorem finite_smul_set : (a • s).Finite ↔ s.Finite :=
  finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]
theorem infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

end Set
