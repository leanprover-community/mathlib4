/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Coset.Basic

/-! Results about the cardinality of a quotient module. -/

namespace Submodule

open LinearMap QuotientAddGroup

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem card_eq_card_quotient_mul_card (S : Submodule R M) :
    Nat.card M = Nat.card S * Nat.card (M ⧸ S) := by
  rw [mul_comm, ← Nat.card_prod]
  exact Nat.card_congr AddSubgroup.addGroupEquivQuotientProdAddSubgroup

end Submodule
