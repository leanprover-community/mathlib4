/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Insert

/-!
# Booleans and set operations

This file contains three trivial lemmas about `Bool`, `Set.univ`, and `Set.range`.
-/

public section


open Set

namespace Bool

@[simp]
theorem univ_eq : (univ : Set Bool) = {false, true} := by grind

set_option linter.tacticAnalysis.verifyGrindOnly false in
@[simp, grind =]
theorem range_eq {α : Type*} (f : Bool → α) : range f = {f false, f true} := by
  grind only [cases Bool, = mem_insert_iff, = mem_range, = mem_singleton_iff]

set_option linter.tacticAnalysis.verifyGrindOnly false in
@[simp, grind =]
theorem compl_singleton (b : Bool) : ({b}ᶜ : Set Bool) = {!b} := by
  grind only [cases Bool, = mem_singleton_iff, = mem_compl_iff]

end Bool
