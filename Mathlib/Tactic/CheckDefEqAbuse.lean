/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init

/-!
# The `#defeq_abuse` tactic and command combinators

`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting, helping to diagnose where Mathlib relies on
definitional equality that isn't available at instance transparency.

`#defeq_abuse in cmd` does the same for commands (e.g. `instance` declarations), where
type class synthesis failures may occur during elaboration rather than during a tactic.
It additionally traces `Meta.synthInstance` to group `isDefEq` failures by the synthesis
application that triggered them.

## Usage

### Tactic mode
```
#defeq_abuse in rw [Set.disjoint_singleton_right]
```

will report something like:
```
Tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  (i : ℕ) → (fun a ↦ Prop) i =?= Set ℕ
```

### Command mode
```
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l
```

will report the synthesis failures grouped by instance application.
-/

public meta section

open Lean Meta Elab Tactic Command

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
    -- Only analyze Meta.isDefEq trace nodes for success/failure
    if Name.isPrefixOf `Meta.isDefEq td.cls then
      let headerStr ← header.toString
      if hasSubstr headerStr "❌" then
        -- Failing node. Recurse into children to find deeper failures.
        -- Note: ✅ children will return #[] (we don't follow recovered paths).
        let mut childFailures := #[]
        for child in children do
          childFailures := childFailures.append (← findLeafFailures child)
        if childFailures.isEmpty then
          -- This is a leaf failure - the deepest point of divergence
          return #[header]
        else
          return childFailures
      else
        -- ✅ node: failures inside were recovered from, not root causes.
        return #[]
    else
      -- Non-isDefEq trace node: recurse through children to find nested isDefEq traces.
      let mut results := #[]
      for child in children do
        results := results.append (← findLeafFailures child)
      return results
  | .compose a b =>
    return (← findLeafFailures a) ++ (← findLeafFailures b)
  | .nest _ m => findLeafFailures m
  | .group m => findLeafFailures m
  | .tagged _ m => findLeafFailures m
  | .withContext _ m => findLeafFailures m
  | .withNamingContext _ m => findLeafFailures m
  | _ => return #[]

/-- Within a synthesis trace, find failing instance application attempts
(`apply @Instance to Goal`) and their `isDefEq` root causes.

Returns an array of `(instanceApp, isDefEqLeafFailures)` pairs. Only reports
applications that have isDefEq leaf failures. -/
partial def findSynthAppFailures (msg : MessageData) :
    BaseIO (Array (MessageData × Array MessageData)) := do
  match msg with
  | .trace td header children =>
    if td.cls == `Meta.isDefEq.onFailure then return #[]
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if hasSubstr headerStr "❌" && hasSubstr headerStr "apply" then
        -- Instance application that failed. Find isDefEq leaf failures.
        let mut failures := #[]
        for child in children do
          failures := failures.append (← findLeafFailures child)
        if failures.isEmpty then
          -- No isDefEq failures here; maybe a sub-synthesis failed. Recurse.
          let mut results := #[]
          for child in children do
            results := results.append (← findSynthAppFailures child)
          return results
        else
          return #[(header, failures)]
      else if hasSubstr headerStr "❌" then
        -- Other failing synthInstance node, recurse into children
        let mut results := #[]
        for child in children do
          results := results.append (← findSynthAppFailures child)
        return results
      else
        -- Successful synthesis can still contain failed sub-attempts. Recurse.
        let mut results := #[]
        for child in children do
          results := results.append (← findSynthAppFailures child)
        return results
    -- Recurse through non-synthInstance children
    let mut results := #[]
    for child in children do
      results := results.append (← findSynthAppFailures child)
    return results
  | .compose a b =>
    return (← findSynthAppFailures a) ++ (← findSynthAppFailures b)
  | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m =>
    findSynthAppFailures m
  | _ => return #[]

/-- Walk a combined `Meta.synthInstance` + `Meta.isDefEq` trace tree to find synthesis failures
and their `isDefEq` root causes.

Returns an array of `(instanceApp, isDefEqLeafFailures)` pairs where:
- `instanceApp` is the header of a failing `apply @Instance to Goal` node
- `isDefEqLeafFailures` are the deepest `isDefEq` failures within that application

Only enters failing top-level synthesis nodes (to avoid reporting failed sub-attempts
that were recovered from within a successful synthesis). -/
partial def findSynthFailures (msg : MessageData) :
    BaseIO (Array (MessageData × Array MessageData)) := do
  match msg with
  | .trace td header children =>
    if td.cls == `Meta.isDefEq.onFailure then return #[]
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if hasSubstr headerStr "❌" then
        -- Failing synthesis. Look for child instance application attempts.
        let mut results := #[]
        for child in children do
          results := results.append (← findSynthAppFailures child)
        return results
      else
        return #[]
    -- For non-synthInstance, non-isDefEq trace nodes, recurse to find nested synthInstance.
    if !Name.isPrefixOf `Meta.isDefEq td.cls &&
        !Name.isPrefixOf `Meta.synthInstance td.cls then
      let mut results := #[]
      for child in children do
        results := results.append (← findSynthFailures child)
      return results
    return #[]
  | .compose a b =>
    return (← findSynthFailures a) ++ (← findSynthFailures b)
  | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m =>
    findSynthFailures m
  | _ => return #[]

/-- Walk a synthesis trace tree and collect the instance names from successful
`apply @Instance to Goal` nodes. Returns a set of instance name strings
(the part between "apply " and " to "). -/
partial def findSynthSuccessApps (msg : MessageData) : BaseIO (Std.HashSet String) := do
  match msg with
  | .trace td header children =>
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if hasSubstr headerStr "apply" && !hasSubstr headerStr "❌" then
        -- Successful application. Extract instance name.
        let parts : List String := headerStr.splitOn "apply "
        let instName := match parts with
          | [_, rest] => match (rest.splitOn " to ") with
            | name :: _ => name.trim
            | _ => headerStr
          | _ => headerStr
        let mut result : Std.HashSet String := {}
        result := result.insert instName
        -- Also recurse into children for nested successes
        for child in children do
          result := result.union (← findSynthSuccessApps child)
        return result
      else
        let mut result : Std.HashSet String := {}
        for child in children do
          result := result.union (← findSynthSuccessApps child)
        return result
    let mut result : Std.HashSet String := {}
    for child in children do
      result := result.union (← findSynthSuccessApps child)
    return result
  | .compose a b =>
    return (← findSynthSuccessApps a).union (← findSynthSuccessApps b)
  | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m =>
    findSynthSuccessApps m
  | _ => return {}

/-- Deduplicate an array of `MessageData` by rendering to string. -/
private def dedup (failures : Array MessageData) : BaseIO (Array MessageData) := do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for failure in failures do
    let s ← failure.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push failure
  return unique

/--
`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.
-/
elab (name := defeqAbuse) "#defeq_abuse " "in " tac:tactic : tactic => withMainContext do
    let tk ← getRef
    let s ← saveState
    -- First, try with respectTransparency true (the strict/new default)
    let strictResult ← try
      withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) do
        evalTactic tac
        pure (Except.ok ())
    catch
      | .internal id ref => throw (.internal id ref)
      | e => pure (Except.error e.toMessageData)
    match strictResult with
    | .ok () =>
      -- Tactic works fine with strict setting, nothing to report.
      -- The tactic has already been executed, so proof state is updated.
      logInfoAt tk
        "#defeq_abuse: tactic succeeds with \
          `backward.isDefEq.respectTransparency true`. No abuse detected."
    | .error _ =>
      s.restore
      -- Try with respectTransparency false (the permissive/old setting)
      let permissiveResult ← try
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac
          pure (Except.ok ())
      catch
        | .internal id ref => throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      match permissiveResult with
      | .error _ =>
        s.restore
        logWarningAt tk
          "#defeq_abuse: tactic fails regardless of \
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
        catch
          | .internal id ref =>
            modifyTraces (fun _ => oldTraces)
            throw (.internal id ref)
          | e => pure (Except.error e.toMessageData)
        let failTraces ← getTraces
        modifyTraces (fun _ => oldTraces)
        s.restore
        -- Find leaf failures in the trace tree
        let mut leafFailures : Array MessageData := #[]
        for trace in failTraces do
          leafFailures := leafFailures ++ (← findLeafFailures trace.msg)
        let uniqueFailures ← dedup leafFailures
        if uniqueFailures.isEmpty then
          logWarningAt tk
            m!"#defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              Could not identify specific failing isDefEq checks from traces."
        else
          let failureList := MessageData.joinSep
            (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
          logWarningAt tk
            m!"#defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              The following isDefEq checks are the root causes of the failure:\n{failureList}"
        -- Run the tactic with permissive setting so it actually succeeds
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac

/--
`#defeq_abuse in cmd` runs `cmd` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the command succeeds with `false` but fails with `true`, it identifies the specific
synthesis applications and `isDefEq` checks that fail with the stricter setting.

This is useful for diagnosing `instance` declarations or other commands where type class synthesis
failures occur during elaboration rather than within a tactic.

The command is re-executed with the permissive setting so that it actually takes effect.
-/
syntax (name := defeqAbuseCmd) "#defeq_abuse " "in" command : command

elab_rules : command
  | `(command| #defeq_abuse%$tk in $cmd) => do
    let saved ← get
    -- Helper: run command and check for errors (elabCommand doesn't throw on synth failures).
    let runAndCheck (opts : Scope → Scope) : CommandElabM (Except MessageData Unit) := do
      try
        withScope opts do
          elabCommand cmd
          if (← get).messages.hasErrors then
            pure (Except.error m!"command produced errors")
          else
            pure (Except.ok ())
      catch
        | .internal id ref => throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
    -- First, try with respectTransparency true (the strict/new default)
    let strictResult ← runAndCheck (fun scope =>
      { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency true })
    set saved
    match strictResult with
    | .ok () =>
      logInfoAt tk "#defeq_abuse: command succeeds with \
        `backward.isDefEq.respectTransparency true`. No abuse detected."
      elabCommand cmd
    | .error _ =>
      -- Try with respectTransparency false (the permissive/old setting)
      let permissiveResult ← runAndCheck (fun scope =>
        { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency false })
      set saved
      match permissiveResult with
      | .error _ =>
        logWarningAt tk "#defeq_abuse: command fails regardless of \
          `backward.isDefEq.respectTransparency` setting."
        elabCommand cmd
      | .ok () =>
        -- Strict fails, permissive works. Trace both to find root causes.
        -- Traces end up in the message log after elabCommand, not in TraceState.
        let traceOpts (strict : Bool) (scope : Scope) : Scope :=
          { scope with opts := (scope.opts.setBool `backward.isDefEq.respectTransparency strict)
              |>.setBool `trace.Meta.isDefEq true
              |>.setBool `trace.Meta.synthInstance true }
        -- Run with strict + tracing
        let savedMsgCount := saved.messages.toList.length
        _ ← try
          withScope (traceOpts true) do elabCommand cmd; pure ()
        catch
          | .internal id ref => throw (.internal id ref)
          | _ => pure ()
        let strictMsgs := ((← get).messages.toList).drop savedMsgCount
        set saved
        -- Run with permissive + tracing to identify failures that happen regardless
        let savedMsgCount2 := saved.messages.toList.length
        _ ← try
          withScope (traceOpts false) do elabCommand cmd; pure ()
        catch
          | .internal id ref => throw (.internal id ref)
          | _ => pure ()
        let permissiveMsgs := ((← get).messages.toList).drop savedMsgCount2
        set saved
        -- Collect instance names that SUCCEED with permissive setting.
        -- Only strict-failing applications that succeed permissively are due
        -- to the transparency change.
        let mut permissiveSuccessApps : Std.HashSet String := {}
        for m in permissiveMsgs do
          permissiveSuccessApps := permissiveSuccessApps.union
            (← findSynthSuccessApps m.data)
        -- Find synthesis failures with isDefEq root causes (strict only)
        let mut synthResults : Array (MessageData × Array MessageData) := #[]
        for m in strictMsgs do
          synthResults := synthResults.append (← findSynthFailures m.data)
        -- Filter to only applications that succeed with permissive transparency.
        let filteredResults ← synthResults.filterM fun (app, _) => do
          let appStr ← app.toString
          -- Extract instance name between "apply " and " to "
          let parts : List String := appStr.splitOn "apply "
          let instName := match parts with
            | [_, rest] => match (rest.splitOn " to ") with
              | name :: _ => name.trim
              | _ => appStr
            | _ => appStr
          return permissiveSuccessApps.contains instName
        if filteredResults.isEmpty then
          -- Fall back to flat isDefEq leaf failures
          let mut leafFailures : Array MessageData := #[]
          for m in strictMsgs do
            leafFailures := leafFailures.append (← findLeafFailures m.data)
          let uniqueFailures ← dedup leafFailures
          if uniqueFailures.isEmpty then
            logWarningAt tk
              m!"#defeq_abuse: command fails with \
                `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
                Could not identify specific failing isDefEq checks from traces."
          else
            let failureList := MessageData.joinSep
              (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
            logWarningAt tk
              m!"#defeq_abuse: command fails with \
                `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
                The following isDefEq checks are the root causes of the failure:\n{failureList}"
        else
          -- Format structured report: group by instance application
          let mut entries : Array MessageData := #[]
          for (app, failures) in filteredResults do
            let uniqueFailures ← dedup failures
            let failureList := MessageData.joinSep
              (uniqueFailures.toList.map fun f => m!"    {f}") "\n"
            entries := entries.push m!"  {app}\n{failureList}"
          let report := MessageData.joinSep entries.toList "\n"
          logWarningAt tk
            m!"#defeq_abuse: command fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              The following synthesis applications fail due to transparency:\n{report}"
        -- Run the command with permissive setting so it actually succeeds
        withScope (fun scope =>
          { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency false }) do
          elabCommand cmd

end Mathlib.Tactic.CheckDefEqAbuse
