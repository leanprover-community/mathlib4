/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Message
public import Std.Data.HashSet.Basic

/-!
# Trace Tree Analysis Utilities for `MessageData`

Lean's `MessageData.trace` nodes form a tree structure used by the tracing infrastructure
(`withTraceNode`, `withTraceNodeBefore`). These utilities provide generic traversal
and analysis of trace trees embedded in `MessageData`.

## Status Encoding

`TraceData` has no structured success/failure field. Instead, `withTraceNodeBefore`
(in `Lean.Util.Trace`) prepends emoji to the rendered header message using `ExceptToEmoji`:
- `✅️` (`checkEmoji`) for success
- `❌️` (`crossEmoji`) for failure
- `💥️` (`bombEmoji`) for exceptions

The `TraceStatus` type and `traceStatusOf` function provide structured access to this encoding.

## Upstream Candidates

`foldTraceNodes`, `TraceStatus`, and `traceStatusOf` are candidates for upstreaming to lean4,
alongside `MessageData.hasTag` in `Lean/Message.lean`.
-/

public section

namespace Lean.MessageData

/-- The success/failure status of a trace node, as encoded by `withTraceNodeBefore`
via emoji prefix on the rendered header. -/
inductive TraceStatus where
  /-- Header starts with ✅️ (checkEmoji) -/
  | success
  /-- Header starts with ❌️ (crossEmoji) -/
  | failure
  /-- Header starts with 💥️ (bombEmoji) -/
  | error
  /-- No recognized emoji prefix -/
  | unknown
  deriving DecidableEq, Repr

/-- Determine the status of a trace node from its rendered header string.

Lean's `withTraceNodeBefore` prepends `checkEmoji`/`crossEmoji`/`bombEmoji`
(defined in `Lean.Util.Trace`) to trace headers to indicate outcomes.

Note: the emoji constants include a variation selector (U+FE0F), but `String.startsWith`
handles this since we check for the base codepoint which is always the prefix. -/
def traceStatusOf (headerStr : String) : TraceStatus :=
  if headerStr.startsWith "✅" then .success
  else if headerStr.startsWith "❌" then .failure
  else if headerStr.startsWith "💥" then .error
  else .unknown

/-- Strip the leading status emoji and space from a trace header string,
leaving just the semantic content for comparison across trace runs.

Trace headers from `withTraceNodeBefore` have the form `"{emoji}[{VS16}] {content}"`.
This strips everything through the first space. Returns the string unchanged if
no recognized status prefix is present. -/
def stripTraceStatusPrefix (s : String) : String :=
  if traceStatusOf s == .unknown then s
  else match s.splitOn " " with
  | _ :: rest@(_ :: _) => " ".intercalate rest
  | _ => s

/-- Fold over trace nodes in a `MessageData` tree.

Automatically recurses through structural wrappers (`.compose`, `.nest`, `.group`,
`.tagged`, `.withContext`, `.withNamingContext`), invoking `onTrace` only for
`.trace` nodes. The `onTrace` callback receives:
- `data`: the `TraceData` (class name, timing, etc.)
- `header`: the trace node's header message
- `children`: the trace node's child messages
- `go`: continuation to recurse into a child `MessageData`

`.ofLazy` nodes are skipped (return `empty`) because they contain unevaluated
formatting thunks, not trace tree structure. This is consistent with `hasTag`
in `Lean/Message.lean` which also skips `.ofLazy`. -/
protected partial def foldTraceNodes {m : Type → Type} [Monad m] {α : Type}
    (msg : Lean.MessageData)
    (onTrace : TraceData → Lean.MessageData → Array Lean.MessageData →
      (Lean.MessageData → m α) → m α)
    (combine : α → α → α) (empty : α) : m α :=
  go msg
where
  go : Lean.MessageData → m α
    | .trace td header children => onTrace td header children go
    | .compose a b => return combine (← go a) (← go b)
    | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m => go m
    | _ => return empty

/-- Deduplicate an array of `MessageData` by their rendered string representation. -/
def dedupByString (msgs : Array Lean.MessageData) : BaseIO (Array Lean.MessageData) := do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array Lean.MessageData := #[]
  for msg in msgs do
    let s ← msg.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push msg
  return unique

end Lean.MessageData

end
