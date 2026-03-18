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

The main definition in this file is `Lean.MessageData.forExprs`,
which locates `Expr` objects nested within a message.

Some helpers are provided implemented in terms of this.
-/

public section

/-- Iterate over all the expressions in a `MessageData`.

`σ` is a state, allowing this to emulate `ForIn`.

`f` is run with `PPContext.runMetaM` with the appropriate context. -/
partial def Lean.MessageData.forExprs {σ} (msg : MessageData) (s : σ)
    (f : σ → Expr → MetaM (ForInStep σ)) : IO σ := do
  return (← go ⟨.anonymous, []⟩ none s msg).value
where
  go (nctx : NamingContext) (ctx? : Option MessageDataContext) (s : σ) :
      MessageData → IO (ForInStep σ)
    | .withContext ctx m => go nctx (some ctx) s m
    | .withNamingContext nctx m => go nctx ctx? s m
    | .compose a b => do
      let ra ← go nctx ctx? s a
      let .yield s := ra | return ra
      go nctx ctx? s b
    | .ofLazy f _ => do
      let ppCtx? := ctx?.map (mkPPContext nctx)
      let dyn ← f ppCtx?
      let some innerMsg := dyn.get? MessageData |
        return .yield s
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
        ppCtx.runMetaM (f s (.mvar m))
      else
        return .yield s
    | .ofFormatWithInfos fwi => do
      let some ppCtx := ctx?.map (mkPPContext nctx) | return .yield s
      goFmt fwi.infos s (fun s' i _ => do
        let some (.ofTermInfo i) := fwi.infos.get? i | return (.yield s', false)
        let ri ← ppCtx.runMetaM (f s' i.expr)
        return (ri, true)
      ) fwi.fmt
  /-- Iterate over the tags of a `Format` using `f`. If `f` returns `true` as its second piece,
  do not recurse further into the tag.  -/
  goFmt {σ} (infos) (s : σ) (f : σ → Nat → Format → IO (ForInStep σ × Bool)) :
      Format → IO (ForInStep σ)
    | .tag n fmt => do
      let (rn, b) ← f s n fmt
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

/-- Find the expression in a message on which `f` does not return `none`. -/
partial def Lean.MessageData.firstExpr? {α} (msg : MessageData) (f : Expr → MetaM (Option α)) : IO (Option α) :=
  msg.forExprs none fun s e => do
    if let .some a ← f e then
      return .done (some a)
    return .yield s

/-- Get all the expressions in a message, in order.

If you need the context of the expressions, prefer to use `forExprs` directly. -/
partial def Lean.MessageData.getExprs (msg : MessageData) : IO (Array Expr) :=
  msg.forExprs #[] fun s e => return .yield (s.push e)
