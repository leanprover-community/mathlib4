/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Jannis Limperg
-/
import Lean.MetavarContext

/-!
# Miscellaneous helper functions for tactics.

[TODO] Ideally we would find good homes for everything in this file, eventually removing it.
-/

set_option autoImplicit true

namespace Mathlib.Tactic

open Lean Meta Tactic

variable [Monad m]

/--
`modifyMetavarDecl mvarId f` updates the `MetavarDecl` for `mvarId` with `f`.
Conditions on `f`:

- The target of `f mdecl` is defeq to the target of `mdecl`.
- The local context of `f mdecl` must contain the same fvars as the local
  context of `mdecl`. For each fvar in the local context of `f mdecl`, the type
  (and value, if any) of the fvar must be defeq to the corresponding fvar in
  the local context of `mdecl`.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
def modifyMetavarDecl [MonadMCtx m] (mvarId : MVarId)
    (f : MetavarDecl → MetavarDecl) : m Unit := do
  modifyMCtx fun mctx ↦
    match mctx.decls.find? mvarId with
    | none => mctx
    | some mdecl => { mctx with decls := mctx.decls.insert mvarId (f mdecl) }

/--
`modifyTarget mvarId f` updates the target of the metavariable `mvarId` with
`f`. For any `e`, `f e` must be defeq to `e`. If `mvarId` does not refer to
a declared metavariable, nothing happens.
-/
def modifyTarget [MonadMCtx m] (mvarId : MVarId) (f : Expr → Expr) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with type := f mdecl.type }

/--
`modifyLocalContext mvarId f` updates the local context of the metavariable
`mvarId` with `f`. The new local context must contain the same fvars as the old
local context and the types (and values, if any) of the fvars in the new local
context must be defeq to their equivalents in the old local context.

If `mvarId` does not refer to a declared metavariable, nothing happens.
-/
def modifyLocalContext [MonadMCtx m] (mvarId : MVarId)
    (f : LocalContext → LocalContext) : m Unit :=
  modifyMetavarDecl mvarId fun mdecl ↦
    { mdecl with lctx := f mdecl.lctx }

/--
`modifyLocalDecl mvarId fvarId f` updates the local decl `fvarId` in the local
context of `mvarId` with `f`. `f` must leave the `fvarId` and `index` of the
`LocalDecl` unchanged. The type of the new `LocalDecl` must be defeq to the type
of the old `LocalDecl` (and the same applies to the value of the `LocalDecl`, if
any).

If `mvarId` does not refer to a declared metavariable or if `fvarId` does not
exist in the local context of `mvarId`, nothing happens.
-/
def modifyLocalDecl [MonadMCtx m] (mvarId : MVarId) (fvarId : FVarId)
    (f : LocalDecl → LocalDecl) : m Unit :=
  modifyLocalContext mvarId fun lctx ↦ lctx.modifyLocalDecl fvarId f
