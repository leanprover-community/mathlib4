/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
import Batteries.Util.Cache
import Lean.HeadIndex
import Lean.Elab.Command

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

open Lean
open Lean.Meta
open Lean.Elab
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

initialize findDeclsPerHead : DeclCache (Lean.HashMap HeadIndex (Array Name)) ←
  DeclCache.mk "#find: init cache" failure {} fun _ c headMap ↦ do
    if (← isBlackListed c.name) then
      return headMap
    -- TODO: this should perhaps use `forallTelescopeReducing` instead,
    -- to avoid leaking metavariables.
    let (_, _, ty) ← forallMetaTelescopeReducing c.type
    let head := ty.toHeadIndex
    pure <| headMap.insert head (headMap.findD head #[] |>.push c.name)

def findType (t : Expr) : TermElabM Unit := withReducible do
  let t ← instantiateMVars t
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars t

  let env ← getEnv
  let mut numFound := 0
  for n in (← findDeclsPerHead.get).findD head #[] do
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
/-
The `#find` command finds definitions & lemmas using pattern matching on the type. For instance:
```lean
#find _ + _ = _ + _
#find ?n + _ = _ + ?n
#find (_ : Nat) + _ = _ + _
#find Nat → Nat
```
Inside tactic proofs, the `#find` tactic can be used instead.
There is also the `find` tactic which looks for
lemmas which are `apply`able against the current goal.
-/
elab "#find " t:term : command =>
  liftTermElabM do
    let t ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
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
/-
Display theorems (and definitions) whose result type matches the current goal,
i.e. which should be `apply`able.
```lean
example : True := by find
```
`find` will not affect the goal by itself and should be removed from the finished proof.
For a command that takes the type to search for as an argument,
see `#find`, which is also available as a tactic.
-/
elab "find" : tactic => do
  findType (← getMainTarget)

/-
Tactic version of the `#find` command.
See also the `find` tactic to search for theorems matching the current goal.
-/
elab "#find " t:term : tactic => do
  let t ← Term.elabTerm t none
  Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
  findType t
