/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
module

-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public import Mathlib.Tactic.Linter.Header  --shake: keep

/-!
# Support for `Sort*` and `Type*`.

These elaborate as `Sort u` and `Type u` with a fresh implicit universe variable `u`.
-/

public meta section

namespace Lean.Elab.Term

/--
Given a `namePrefix` (`` `u`` by default), returns the first name out of `namePrefix_1`,
`namePrefix_2`, ... which does not appear in `usedLevelNames`. Note `mkFreshLevelName` does not
attempt to use `namePrefix` itself as a level name.
-/
partial def mkFreshLevelName (usedLevelNames : List Name) (namePrefix : Name := `u) : Name :=
  go 1
where
  /-- Check if `namePrefix.appendIndexAfter n` is unused, else recurse with `n+1`. -/
  go n : Name :=
    let u := namePrefix.appendIndexAfter n
    if usedLevelNames.contains u then go (n+1) else u

/--
Creates a fresh `Level` parameter which does not appear in the current state's `levelNames`, and
updates the state to include the new level parameter.

By default, the new level parameter is of the form `u_i` and is included in the state as the most
recent level parameter (at the front of the list).

Supplying a `namePrefix` will cause the new level parameter to be of the form `namePrefix_i`, with
`i` starting at `1`.

The new level name can be inserted at a custom position in the list of level names by providing a
function `insert : List Name → Name → List Name` which will be called as
`insert currentLevelNames newLevelName`. It is expected that the result will contain the new level
name and still contain all current level names.
-/
def mkFreshLevelParam (namePrefix : Name := `u)
    (insert : List Name → Name → List Name := (·.cons)) : TermElabM Level := do
  let levelNames ← getLevelNames
  let u := mkFreshLevelName levelNames namePrefix
  setLevelNames <| insert levelNames u
  return mkLevelParam u

/-- The syntax `variable (X Y ... Z : Sort*)` creates a new distinct implicit universe variable
for each variable in the sequence. -/
elab "Sort*" : term => return .sort <| ← mkFreshLevelParam

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => return .sort <| .succ <| ← mkFreshLevelParam

end Lean.Elab.Term
