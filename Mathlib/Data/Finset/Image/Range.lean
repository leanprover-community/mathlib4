/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Algebra.Group.Embedding
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Image.Defs
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.Group.Int.Units

/-! # Image and map operations on `Finset.range`.

-/

assert_not_exists MonoidWithZero
assert_not_exists MulAction

variable {α β γ : Type*}

open Multiset

open Function

namespace Finset

/-! ### map -/

section Map

theorem disjoint_range_addLeftEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) s) := by
  simp_rw [disjoint_left, mem_map, mem_range, addLeftEmbedding_apply]
  rintro _ h ⟨l, -, rfl⟩
  omega

theorem disjoint_range_addRightEmbedding (a : ℕ) (s : Finset ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) s) := by
  rw [← addLeftEmbedding_eq_addRightEmbedding]
  apply disjoint_range_addLeftEmbedding

end Map

/-! ### image -/


section Image

variable [DecidableEq β]

theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b

end Image

end Finset
