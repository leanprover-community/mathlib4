/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kim Morrison
-/

module

import Mathlib.Init
public import Lean.Meta.Basic

/-!
# Tools for extracting `Expr`s from `MessageData` nodes

This file provides `for (ppCtx, e) in msg.exprs do` notation, which iterates through the
expressions `e` in a `msg : MessageData`. The surrounding monad must support `BaseIO` to handle
`.ofLazy` `MessageData` nodes. `e` may be interpreted in a `MetaM` context using `ppCtx.runMetaM e`.

Some helpers are provided implemented in terms of this.
-/

public section

namespace Lean.MessageData

universe u

variable {m : Type → Type u} [Monad m] [MonadLiftT BaseIO m]

/-- Iterate over all the expressions in a `MessageData`. Used to implement
`for (ppCtx, e) in msg.exprs do` notation, which should be preferred over using this declaration
directly. -/
partial def forExprsIn {σ} (msg : MessageData) (s : σ)
    (f : PPContext × Expr → σ → m (ForInStep σ)) : m σ := do
  return (← go ⟨.anonymous, []⟩ none s msg).value
where
  go (nctx : NamingContext) (ctx? : Option MessageDataContext) (s : σ) :
      MessageData → m (ForInStep σ)
    | .withContext ctx m => go nctx (some ctx) s m
    | .withNamingContext nctx m => go nctx ctx? s m
    | .compose a b => do
      let ra ← go nctx ctx? s a
      let .yield s := ra | return ra
      go nctx ctx? s b
    | .ofLazy f _ => do
      let ppCtx? := ctx?.map (mkPPContext nctx)
      let dyn ← f ppCtx?
      let some innerMsg := dyn.get? MessageData | return .yield s
      go nctx ctx? s innerMsg
    | .nest _ m | .group m | .tagged _ m => go nctx ctx? s m
    | .ofWidget _ alt => go nctx ctx? s alt
    | .trace _ msg children => do
      let rmsg ← go nctx ctx? s msg
      let .yield s := rmsg | return rmsg
      let mut s' := s
      for c in children do
        let rc ← go nctx ctx? s' c
        let .yield s := rc | return rc
        s' := s
      return .yield s'
    | .ofGoal m => do
      if let some ppCtx := ctx?.map (mkPPContext nctx) then
        -- See below; `.goal`s also go through `ctx.runMetaM` when being displayed.
        f ({ ppCtx with env := ppCtx.env.setExporting false }, .mvar m) s
      else
        return .yield s
    | .ofFormatWithInfos fwi => do
      let some ppCtx := ctx?.map (mkPPContext nctx) | return .yield s
      goFmt ppCtx fwi.infos s fwi.fmt
  /-- Iterate over the tags of a `Format` using `f`. -/
  goFmt (ppCtx : PPContext) (infos) (s : σ) : Format → m (ForInStep σ)
    | .tag n fmt => do
      match infos.get? n with
      | some (.ofTermInfo { expr, lctx .. })
      | some (.ofDelabTermInfo { expr, lctx .. }) => do
        /- When displaying interactive expressions, lean creates a `ctx : Elab.ContextInfo` from
        the surrounding `ppCtx`, abandoning the `ppCtx`'s `lctx` and using whatever `lctx` is
        provided by the info. But we want to expose a uniform interface, so we try to create a
        `ppCtx` such that `ppCtx.runMetaM` behaves the same as `ctx.runMetaM info.lctx`. This means
        passing in the `lctx` from the info node and setting exporting to `false` (see
        `ContextInfo.runCoreM`). We regard the other differences (e.g. `ngen`, `diag`) as
        too minor to change.

        See `Lean.Widget.Interactive` and `msgToInteractiveAux` to see how lean handles
        `FormatWithInfos` in the language server. -/
        let ppCtx := { ppCtx with lctx, env := ppCtx.env.setExporting false }
        f (ppCtx, expr) s
      | _ => goFmt ppCtx infos s fmt
    | .group fmt _ => goFmt ppCtx infos s fmt
    | .nest _ fmt => goFmt ppCtx infos s fmt
    | .append fmt1 fmt2 => do
      let r1 ← goFmt ppCtx infos s fmt1
      let .yield s := r1 | return r1
      goFmt ppCtx infos s fmt2
    | .text _ | .align _ | .line | .nil => return .yield s

/-- A wrapper structure for `MessageData` to enable `for (ppCtx, e) in msg.exprs do` notation. -/
protected structure Exprs where
  /-- The `MessageData` whose expressions will be iterated over. -/
  msg : MessageData

/-- `for (ppCtx, e) in msg.exprs do` iterates through the expressions in `MessageData` together
with their `ppCtx : PPContext`. The `ppCtx` can be used to interpret the expression in a valid
`MetaM` context via `ppCtx.runMetaM`.

The monad must support `BaseIO` in order to interpret `.ofLazy` nodes in `MessageData`.

Expressions without a valid `ppCtx` are skipped. -/
def exprs (msg : MessageData) : MessageData.Exprs := ⟨msg⟩

instance : ForIn m MessageData.Exprs (PPContext × Expr) where
  forIn exprs := exprs.msg.forExprsIn

/-- Find the expression in a message on which `f` does not return `none`. -/
partial def firstExpr? {α} (msg : MessageData) (f : Expr → MetaM (Option α)) :
    IO (Option α) := do
  for (ppCtx, e) in msg.exprs do
    let a@(some _) ← ppCtx.runMetaM (f e) | continue
    return a
  return none

/-- Get all the expressions in a message, in order.

If you need the context of the expressions, prefer iterating over the expressions via
`for (ppCtx, e) in msg.exprs do` directly. -/
partial def getExprs (msg : MessageData) : m (Array Expr) := do
  let mut arr := #[]
  for (_, e) in msg.exprs do
    arr := arr.push e
  return arr

end Lean.MessageData
