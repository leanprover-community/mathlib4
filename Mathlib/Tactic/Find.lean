/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

public import Mathlib.Init
public meta import Batteries.Util.Cache
public meta import Lean.HeadIndex
public meta import Lean.Elab.Command
public import Batteries.Util.Cache

/-!
# The `#find` command and tactic.

The `#find` command finds definitions & lemmas using pattern matching on the type. For instance:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```
Inside tactic proofs, there is a `#find` tactic with the same syntax,
or the `find` tactic which looks for lemmas which are `apply`able against the current goal.

-/

public meta section

open Lean Std
open Lean.Meta
open Lean.Elab

open Batteries.Tactic

namespace Mathlib.Tactic.Find

private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false

-- from Lean.Server.Completion
private def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  pure <| declName.isInternal
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName
  <||> isMatcher declName

initialize findDeclsPerHead : DeclCache (Std.HashMap HeadIndex (Array Name)) ←
  DeclCache.mk "#find: init cache" failure {} fun _ c headMap ↦ do
    if (← isBlackListed c.name) then
      return headMap
    -- TODO: this should perhaps use `forallTelescopeReducing` instead,
    -- to avoid leaking metavariables.
    let (_, _, ty) ← forallMetaTelescopeReducing c.type
    let head := ty.toHeadIndex
    pure <| headMap.insert head (headMap.getD head #[] |>.push c.name)

def findType (t : Expr) : TermElabM Unit := withReducible do
  let t ← instantiateMVars t
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars t

  let env ← getEnv
  let mut numFound := 0
  for n in (← findDeclsPerHead.get).getD head #[] do
    let c := env.find? n |>.get!
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    let found ← forallTelescopeReducing cTy fun cParams cTy' ↦ do
      let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
        (← mkFreshLevelMVars pat.numMVars).toArray
      let (_, _, pat) ← lambdaMetaTelescope pat
      let (patParams, _, pat) ← forallMetaTelescopeReducing pat
      isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
    if found then
      numFound := numFound + 1
      if numFound > 20 then
        logInfo m!"maximum number of search results reached"
        break
      logInfo m!"{n}: {cTy}"

open Lean.Elab.Command in
/--
`#find t` finds definitions and theorems whose result type matches the term `t`, and prints them as
info lines. Use holes in `t` to indicate arbitrary subexpressions, for example `#find _ ∧ _` will
match any conjunction.

`#find` is also available as a tactic, and there is also the `find` tactic which looks for lemmas
which are `apply`able against the current goal.

Examples:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```
-/
elab "#find " t:term : command =>
  liftTermElabM do
    let t ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    findType t

/- (Note that you'll get an error trying to run these here:
``cannot evaluate `[init]` declaration 'findDeclsPerHead' in the same module``
but they will work fine in a new file!) -/
-- #find _ + _ = _ + _
-- #find _ + _ = _ + _
-- #find ?n + _ = _ + ?n
-- #find (_ : Nat) + _ = _ + _
-- #find Nat → Nat
-- #find ?n ≤ ?m → ?n + _ ≤ ?m + _

open Lean.Elab.Tactic
/--
`find` finds definitions and theorems whose result type matches the current goal exactly,
and prints them as info lines.
In other words, `find` lists definitions and theorems that are `apply`able against the current goal.
`find` will not affect the goal by itself and should be removed from the finished proof.

For a command or tactic that takes the type to search for as an argument, see `#find`.

Example:
```lean
example : True := by
  find
  -- True.intro: True
  -- trivial: True
  -- ...
```
-/
elab "find" : tactic => do
  findType (← getMainTarget)

/--
`#find t` finds definitions and theorems whose result type matches the term `t`, and prints them as
info lines. Use holes in `t` to indicate arbitrary subexpressions, for example `#find _ ∧ _` will
match any conjunction. `#find` is also available as a command.
`#find` will not affect the goal by itself and should be removed from the finished proof.

There is also the `find` tactic which looks for lemmas which are `apply`able against the current
goal.

Examples:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```
-/
elab "#find " t:term : tactic => do
  let t ← Term.elabTerm t none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  findType t

end Mathlib.Tactic.Find
