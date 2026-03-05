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
# Utilities for analyzing `MessageData`

**WARNING**: The declarations in this module may become obsolete with upcoming core changes.

`TraceData` has no structured success/failure field. Instead, `withTraceNodeBefore`
(in `Lean.Util.Trace`) prepends emoji to the rendered header message using `ExceptToEmoji`:
- `✅️` (`checkEmoji`) for success
- `❌️` (`crossEmoji`) for failure
- `💥️` (`bombEmoji`) for exceptions

The `TraceResult` type and `traceResultOf` function provide structured access to this encoding.

## Pending lean4 PRs

These lean4 PRs may render declarations in this module obsolete:

- [lean4#12698](https://github.com/leanprover/lean4/pull/12698) adds `TraceResult` to `TraceData`.
  Once available, callers can use `td.result?` instead of parsing the header string.
- [lean4#12699](https://github.com/leanprover/lean4/pull/12699) adds a `Meta.synthInstance.apply`
  trace class, so synthesis "apply" nodes can be identified via `td.cls` instead of string-matching.
-/

public section

namespace Lean.MessageData

/-- The success/failure status of a trace node, as encoded by `withTraceNodeBefore`
via emoji prefix on the rendered header.

Intended to match `TraceResult` from [lean4#12698](https://github.com/leanprover/lean4/pull/12698).
Once that PR is available, callers should prefer `td.result?` over parsing the header string with
`traceResultOf`. -/
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

The `TraceResult` will be recorded in trace messages directly in [lean4#12698](https://github.com/leanprover/lean4/pull/12698).
Once that PR is available, callers should prefer `td.result?` over calling this function.

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
  if (traceResultOf s).isNone then s else
    s.toSlice.dropPrefix (!·.isWhitespace) |>.dropPrefix ' ' |>.copy

/-- Extract the instance name from a rendered `apply @Foo to Goal` trace header.
Returns the string between `"apply "` and `" to "`.

Note: this is fragile string matching against Lean's `Meta.synthInstance` trace format.
If the trace format changes, this function will silently return the original string.
Once [lean4#12699](https://github.com/leanprover/lean4/pull/12699) is available,
these nodes will have trace class `Meta.synthInstance.apply` and can be identified
structurally via `td.cls` instead of string-matching on the header. -/
def extractInstName (s : String) : String :=
  match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

/-- Deduplicate an array of `MessageData` by their rendered string representations. -/
def dedupByString (msgs : Array MessageData) : BaseIO (Array MessageData) := do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for msg in msgs do
    let s ← msg.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push msg
  return unique

end Lean.MessageData

end
