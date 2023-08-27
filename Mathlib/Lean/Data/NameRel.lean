/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Lean.Data.NameMap
import Lean.Declaration
import Mathlib.Lean.Expr.Basic

/-!
## A data structure for a relation on names
-/

open Lean Meta

namespace Lean

/-- A `NameRel` maps names to sets of names -/
def NameRel := NameMap NameSet

instance : EmptyCollection NameRel :=
  inferInstanceAs $ EmptyCollection (NameMap NameSet)

instance : Inhabited NameRel :=
  inferInstanceAs $ Inhabited (NameMap NameSet)

/-- For all names `n` mentioned in the type of the constant `c`, add `c.name` to the set associated
with `n`. -/
def NameRel.addDecl (c : ConstantInfo) (m : NameRel) := do
  if ← c.name.isBlackListed then
    return m
  let consts := c.type.foldConsts {} (flip NameSet.insert)
  return consts.fold (init := m) fun m n =>
    m.insert n (
      m.findD n {} |> flip .insert c.name
    )

/-- Finds the set of names associated with the given one -/
def NameRel.find (m : NameRel) (n : Name) := m.findD n {}

end Lean
