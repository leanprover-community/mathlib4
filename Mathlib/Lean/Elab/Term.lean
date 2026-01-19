/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Thomas R. Murrills
-/
module

public import Mathlib.Init
public import Lean.Elab.Term

/-!
# Additions to `Lean.Elab.Term`
-/

public meta section

namespace Lean.Elab.Term

/-- Fully elaborates the term `patt`, allowing typeclass inference failure,
but while setting `errToSorry` to false.
Typeclass failures result in plain metavariables.
Instantiates all assigned metavariables. -/
def elabPattern (patt : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context ({ · with ignoreTCFailures := true, errToSorry := false }) <|
    withSynthesizeLight do
      let t ← elabTerm patt expectedType?
      synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
      instantiateMVars t

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

end Lean.Elab.Term
