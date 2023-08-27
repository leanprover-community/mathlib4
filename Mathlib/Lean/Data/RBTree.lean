/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import Lean.Data.RBTree

/-!
# Additional functions on `Lean.RBTree`.
-/

universe u
variable {α : Type u} {cmp : α → α → Ordering}

/-- The intersection of a (non-empty) array of `RBTree`s. If
the input is empty, the empty tree is returned. -/
def Lean.RBTree.intersects (ts : Array (RBTree α cmp)) : RBTree α cmp :=
  if ts.isEmpty then {} else
  -- sorts smallest set to the back, and iterate over that one
  -- TODO: An `RBTree` admits bulk operations, which could replace this implementation
  let ts := ts.qsort (·.size > ·.size)
  ts.back.fold (init := {}) fun s m =>
    if ts.pop.all (·.contains m) then s.insert m else s
