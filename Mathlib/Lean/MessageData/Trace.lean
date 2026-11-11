/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean.Message

import Mathlib.Init

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
