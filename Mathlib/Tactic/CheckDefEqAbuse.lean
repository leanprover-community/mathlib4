/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init

/-!
# The `check_defeq_abuse` tactic combinator

`check_defeq_abuse tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting, helping to diagnose where Mathlib relies on
definitional equality that isn't available at instance transparency.

## Usage

```
check_defeq_abuse rw [Set.disjoint_singleton_right]
```

will report something like:
```
Tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  (i : ℕ) → (fun a ↦ Prop) i =?= Set ℕ
```
-/

public meta section

open Lean Meta Elab Tactic

namespace Mathlib.Tactic.CheckDefEqAbuse

/-- Check if a string contains a given substring. -/
private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Recursively walk a `MessageData` tree to find the deepest failing
`Meta.isDefEq` trace nodes.

The algorithm:
- Skips nodes with `cls = Meta.isDefEq.onFailure` (retry traces)
- Only follows ❌ branches — failures inside ✅ nodes were recovered
  from and are not root causes
- A "leaf failure" is a ❌ node whose only ❌ children are onFailure
- Returns the header messages of all leaf failures
-/
partial def findLeafFailures (msg : MessageData) : BaseIO (Array MessageData) := do
  match msg with
  | .trace td header children =>
    -- Skip onFailure retry nodes (cls is Meta.isDefEq.onFailure)
    if td.cls == `Meta.isDefEq.onFailure then
      return #[]
    -- Check if this is a failing isDefEq check
    let headerStr ← header.toString
    if hasSubstr headerStr "❌" then
      -- Failing node. Recurse into children to find deeper failures.
      -- Note: ✅ children will return #[] (we don't follow recovered paths).
      let childFailures ← children.foldlM (init := #[]) fun acc child => do
        return acc ++ (← findLeafFailures child)
      if childFailures.isEmpty then
        -- This is a leaf failure - the deepest point of divergence
        return #[header]
      else
        return childFailures
    else
      -- ✅ node: failures inside were recovered from, not root causes.
      return #[]
  | .compose a b =>
    return (← findLeafFailures a) ++ (← findLeafFailures b)
  | .nest _ m => findLeafFailures m
  | .group m => findLeafFailures m
  | .tagged _ m => findLeafFailures m
  | .withContext _ m => findLeafFailures m
  | .withNamingContext _ m => findLeafFailures m
  | _ => return #[]

/--
`check_defeq_abuse tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.
-/
syntax (name := checkDefEqAbuse) "check_defeq_abuse " tactic : tactic

elab_rules : tactic
  | `(tactic| check_defeq_abuse%$tk $tac) => withMainContext do
    let s ← saveState
    -- First, try with respectTransparency true (the strict/new default)
    let strictResult ← try
      withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) do
        evalTactic tac
        pure (Except.ok ())
    catch e =>
      pure (Except.error e.toMessageData)
    match strictResult with
    | .ok () =>
      -- Tactic works fine with strict setting, nothing to report.
      -- The tactic has already been executed, so proof state is updated.
      logInfoAt tk
        "check_defeq_abuse: tactic succeeds with \
          `backward.isDefEq.respectTransparency true`. No abuse detected."
    | .error _ =>
      s.restore
      -- Try with respectTransparency false (the permissive/old setting)
      let permissiveResult ← try
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac
          pure (Except.ok ())
      catch e =>
        pure (Except.error e.toMessageData)
      match permissiveResult with
      | .error _ =>
        s.restore
        logWarningAt tk
          "check_defeq_abuse: tactic fails regardless of \
            `backward.isDefEq.respectTransparency` setting."
        -- Still run the tactic so the user sees the original error
        evalTactic tac
      | .ok () =>
        s.restore
        -- Now we know: strict fails, permissive works.
        -- Run with strict + tracing to capture the failure details.
        let oldTraces ← getTraces
        modifyTraces (fun _ => {})
        _ ← try
          withOptions (fun o =>
              (o.setBool `backward.isDefEq.respectTransparency true)
                |>.setBool `trace.Meta.isDefEq true) do
            evalTactic tac
            pure (Except.ok ())
        catch e =>
          pure (Except.error e.toMessageData)
        let failTraces ← getTraces
        modifyTraces (fun _ => oldTraces)
        s.restore
        -- Find leaf failures in the trace tree
        let mut leafFailures : Array MessageData := #[]
        for trace in failTraces do
          leafFailures := leafFailures ++ (← findLeafFailures trace.msg)
        -- Deduplicate by rendering to string
        let mut seen : Array String := #[]
        let mut uniqueFailures : Array MessageData := #[]
        for failure in leafFailures do
          let s ← failure.toString
          unless seen.contains s do
            seen := seen.push s
            uniqueFailures := uniqueFailures.push failure
        if uniqueFailures.isEmpty then
          logWarningAt tk
            m!"check_defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              Could not identify specific failing isDefEq checks from traces."
        else
          let failureList := MessageData.joinSep
            (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
          logWarningAt tk
            m!"check_defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              The following isDefEq checks are the root causes of the failure:\n{failureList}"
        -- Run the tactic with permissive setting so it actually succeeds
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac

end Mathlib.Tactic.CheckDefEqAbuse
