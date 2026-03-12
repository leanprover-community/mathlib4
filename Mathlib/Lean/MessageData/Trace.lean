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

Utility functions for working with trace messages.

`withTraceNode` (in `Lean.Util.Trace`) stores a `TraceResult` in `TraceData.result?`
and prepends emoji to the rendered header:
- `✅️` (`checkEmoji`) for success
- `❌️` (`crossEmoji`) for failure
- `💥️` (`bombEmoji`) for exceptions

The `traceResultOf` function provides backward-compatible parsing of rendered headers.
-/

public section

namespace Lean.MessageData

/-- Determine the status of a trace node from its rendered header string.

`withTraceNode` prepends `checkEmoji`/`crossEmoji`/`bombEmoji`
(defined in `Lean.Util.Trace`) to trace headers to indicate outcomes.

Prefer `td.result?` when the `TraceData` is available. -/
def traceResultOf (headerStr : String) : Option TraceResult :=
  if headerStr.startsWith "✅" then some .success
  else if headerStr.startsWith "❌" then some .failure
  else if headerStr.startsWith "💥" then some .error
  else none

/-- Strip the leading status emoji and space from a trace header string,
leaving just the semantic content for comparison across trace runs.

Trace headers from `withTraceNode` have the form `"{emoji}[{VS16}] {content}"`.
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
