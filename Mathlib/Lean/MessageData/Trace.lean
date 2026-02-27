/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import Mathlib.Init
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

The `TraceResult` type and `traceResultOf` function provide structured access to this encoding.

## Upstream Candidates

`foldTraceNodes`, `TraceResult`, and `traceResultOf` are candidates for upstreaming to lean4,
alongside `MessageData.hasTag` in `Lean/Message.lean`.

## Pending lean4 PRs (not required for this module)

These lean4 PRs will simplify things further but are not prerequisites:

- https://github.com/leanprover/lean4/pull/12698 adds `TraceResult` to `TraceData`.
  Once available, callers can use `td.result?` instead of parsing the header string.
- https://github.com/leanprover/lean4/pull/12699 adds a `Meta.synthInstance.apply` trace class,
  so synthesis "apply" nodes can be identified via `td.cls` instead of string-matching.
-/

public section

namespace Lean.MessageData

/-- The success/failure status of a trace node, as encoded by `withTraceNodeBefore`
via emoji prefix on the rendered header.
Intended to match `TraceResult` from https://github.com/leanprover/lean4/pull/12698,
wrapped in `Option` (where `none` = no recognized emoji prefix).
Once that PR is available, callers should prefer `td.result?` over parsing the header string. -/
inductive TraceResult where
  /-- Header starts with ✅️ (checkEmoji) -/
  | success
  /-- Header starts with ❌️ (crossEmoji) -/
  | failure
  /-- Header starts with 💥️ (bombEmoji) — an exception was thrown -/
  | error
  deriving DecidableEq, Repr

/-- Determine the status of a trace node from its rendered header string.

Lean's `withTraceNodeBefore` prepends `checkEmoji`/`crossEmoji`/`bombEmoji`
(defined in `Lean.Util.Trace`) to trace headers to indicate outcomes.

Note: the emoji constants include a variation selector (U+FE0F), but `String.startsWith`
handles this since we check for the base codepoint which is always the prefix. -/
def traceResultOf (headerStr : String) : Option TraceResult :=
  if headerStr.startsWith "✅" then some .success
  else if headerStr.startsWith "❌" then some .failure
  else if headerStr.startsWith "💥" then some .error
  else none

/-- Strip the leading status emoji and space from a trace header string,
leaving just the semantic content for comparison across trace runs.

Trace headers from `withTraceNodeBefore` have the form `"{emoji}[{VS16}] {content}"`.
This strips everything through the first space. Returns the string unchanged if
no recognized status prefix is present. -/
def stripTraceResultPrefix (s : String) : String :=
  if (traceResultOf s).isNone then s
  else match s.splitOn " " with
  | _ :: rest@(_ :: _) => " ".intercalate rest
  | _ => s

/-- A return value for functions called by traversals of `MessageData`. May either descend into
children or ascend immediately (skipping children), optionally including a value accumulated by the
traversal in both cases. -/
inductive VisitStep (α) where
/-- Descends through the `MessageData`, visiting all children. If the argument `butFirst` is given
as `some a` (`none` by default), starts with `a`, and combines any values produced by children with
this value. -/
| descend (butFirst : Option α := none)
/-- Skips visiting children, and ascends to the parent, returning the value given in `returning`
(if any). -/
| ascend (returning : Option α := none)

variable {m : Type → Type} [Monad m] {α : Type}

/-- Collect and combine values of type `α` produced by visiting all trace nodes in a `MessageData`
tree.

Automatically recurses through structural wrappers, invoking `onTrace` only for
`.trace` nodes. The `onTrace` callback receives the arguments of `.trace`:
- the `TraceData` (class name, timing, etc.)
- the trace node's header message
- the trace node's child messages

Each call to `onTrace` is expected to produce either a `descend`, in which case the children of the
trace nodes will be visited, or an `ascend`, in which case they will not. Both may take an argument
`butFirst := some a`, which will cause `a` to be `combine`d into the accumulated value.

We assume `x = combine empty x = combine x empty`. `empty` is attempted to be synthesized as the
`EmptyCollection`, and `combine` is attempted to be synthesized first via the notation `(· ++ ·)`
then via `(· ∪ ·)` as a fallback.

Note that the children may be visited manually via a recursive call to `collectWith` or
`collectWithAndAscend`.

Note: `.ofLazy` nodes are skipped (return `empty`) because they contain unevaluated
formatting thunks, not trace tree structure. This is consistent with `hasTag`
in `Lean.Message` which also skips `.ofLazy`. -/
partial def visitTraceNodesM (msg : MessageData)
    (onTrace : TraceData → MessageData → Array MessageData → m (MessageData.VisitStep α))
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m α :=
  go msg
where
  /-- The continuation for `visitTraceNodesM`; this is mainly for readability (takes only one
  argument in source). -/
  go : MessageData → m α
    | .trace td header children => do
      match ← onTrace td header children with
      | .descend a? => do
        let mut result := a?.getD empty
        for child in children do
          result := combine result (← go child)
        return result
      | .ascend a? => return a?.getD empty
    | .compose a b => return combine (← go a) (← go b)
    | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m => go m
    | .ofLazy _ _ | .ofWidget _ _ | .ofGoal _ | .ofFormatWithInfos _ => return empty

/-- Convenience wrapper which accumulates the results of `visitM` across `arr`, attempting to
produce `empty` and `combine` from `{}` and `(· ++ ·)` or `(· ∪ ·)`. -/
@[inline] def visitWithM {β} (arr : Array β) (visitM : β → m α)
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m α :=
  arr.foldlM (init := empty) fun acc msg => return combine acc (← visitM msg)

/-- Convenience wrapper which accumulates the results of `visitM` across `arr`, attempting to
produce `empty` and `combine` from `{}` and `(· ++ ·)` or `(· ∪ ·)`, then `.ascend`s with the result
(if any). This effectively replaces a return value of `.descend`. -/
@[inline] def visitWithAndAscendM {β} (arr : Array β) (visitM : β → m α)
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m (VisitStep α) := do
  if arr.isEmpty then return .ascend else
    return .ascend <|← visitWithM arr visitM empty combine

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
