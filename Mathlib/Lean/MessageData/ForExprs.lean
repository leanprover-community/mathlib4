/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kim Morrison
-/

module

import Mathlib.Init
public import Lean.Message
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
        f (ppCtx, .mvar m) s
      else
        return .yield s
    | .ofFormatWithInfos fwi => do
      let some ppCtx := ctx?.map (mkPPContext nctx) | return .yield s
      goFmt fwi.infos s (fun s' i => do
        match fwi.infos.get? i with
        | some (.ofTermInfo { expr .. })
        | some (.ofDelabTermInfo { expr .. }) => return (← f (ppCtx, expr) s', true)
        | _ => return (.yield s', false)
      ) fwi.fmt
  /-- Iterate over the tags of a `Format` using `f`. If `f` returns `true` as its second piece,
  do not recurse further into the tag.  -/
  goFmt {σ} (infos) (s : σ) (f : σ → Nat → m (ForInStep σ × Bool)) : Format → m (ForInStep σ)
    | .tag n fmt => do
      let (rn, b) ← f s n
      if b then return rn
      let .yield s := rn | return rn
      goFmt infos s f fmt
    | .group fmt _ => goFmt infos s f fmt
    | .nest _ fmt => goFmt infos s f fmt
    | .append fmt1 fmt2 => do
      let r1 ← goFmt infos s f fmt1
      let .yield s := r1 | return r1
      goFmt infos s f fmt2
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
