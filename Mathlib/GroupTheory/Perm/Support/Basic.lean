/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.End

/-!
# Support of a permutation: basic results

This file contains results about the set of points moved by a permutation that do not need any
finiteness assumptions.

See `Mathlib/GroupTheory/Perm/Support/Finset/Basic.lean` for `Equiv.Perm.support`, the `Finset`
of points moved by a permutation of a `Fintype`.
-/

public section

open Equiv Function

namespace Equiv.Perm

variable {α : Type*}

section Set

variable (p q : Perm α)

lemma set_support_symm_eq : {x | p.symm x ≠ x} = {x | p x ≠ x} := by
  ext; simp [eq_symm_apply, eq_comm]

theorem set_support_apply_mem {p : Perm α} {a : α} :
    p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by simp

theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  simp only [Set.mem_ofPred_eq, Ne]
  intro hx H
  simp [zpow_apply_eq_self_of_apply_eq_self H] at hx

theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  simp only [coe_mul]
  grind

end Set

end Equiv.Perm
