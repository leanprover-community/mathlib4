/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kim Morrison
-/

module

public import Lean.Message
public import Lean.Meta.Basic

/-!
# Tools for extracting `Expr`s from `MessageData` nodes

The main definition in this file is `Lean.MessageData.forExprs`,
which locates `Expr` objects nested within a message.

Some helpers are provided implemented in terms of this.
-/

public section

/-- Iterate over all the expressions in a `MessageData`. `σ` is a state, allowing this to emulate `ForIn`. -/
partial def Lean.MessageData.forExprs (msg : MessageData) (s : σ) (f : σ → Expr → MetaM (ForInStep σ)) : IO σ := do
  return (← go ⟨.anonymous, []⟩ none s msg).value
where
  go (nctx : NamingContext) (ctx? : Option MessageDataContext) (s : σ) : MessageData → IO (ForInStep σ)
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
        IO.println s!"Bad lazy"
        return .yield s
      IO.println s!"Got lazy"
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
      let mut s' := s
      if let some ppCtx := ctx?.map (mkPPContext nctx) then
        for (_, info) in fwi.infos do
          if let .ofTermInfo i := info then
            let ri ← ppCtx.runMetaM (f s' i.expr)
            let .yield s := ri | return ri
            s' := s
      return .yield s'

/-- Find the first expression in a message. -/
partial def Lean.MessageData.findExpr? (msg : MessageData) (f : Expr → MetaM (Option α)) : IO (Option α) :=
  msg.forExprs none fun s e => do
    if let .some a ← f e then
      return .done (some a)
    return .yield s

/-- Get all expressions in a message.

If you need the context of the expressions, prefer to use `forExprs` directly. -/
partial def Lean.MessageData.getExprs (msg : MessageData) : IO (List Expr) :=
  msg.forExprs [] fun s e => return .yield (e :: s)
