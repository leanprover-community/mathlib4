import Lean.Server.Requests

/-!
# Running `RequestM` actions inside `CommandElabM` for testing

This file demonstrates how to drive language-server request handler logic
(`RequestM`) from ordinary meta code (here, `CommandElabM`), so that handler
bodies can be unit-tested and their results inspected/printed.

The strategy ("Strategy A"): rather than re-running the whole file-worker
processing pipeline, we
* build a *stub* `RequestContext` whose `doc.meta` is real but whose snapshot
  fields are inert placeholders, and
* fabricate a `Snapshots.Snapshot` directly from the live `CommandElabM` state
  (`stx`/`mpState`/`cmdState`).

This lets us exercise `RequestM.runCoreM` / `runTermElabM` / `runCommandElabM`,
which only read `rc.doc.meta` plus the supplied snapshot, without simulating
parsing or elaboration of a whole document.
-/

open Lean Lean.Server Lean.Server.FileWorker Lean.Elab.Command

/--
Build a stub `RequestContext` over the given source text.

`doc.meta` is genuine (real `FileMap`, uri, module name); everything else is a
placeholder sufficient for handlers that do not traverse the snapshot tree, do
RPC, or read client capabilities.
-/
def mkStubRequestContext (source : String) : IO RequestContext := do
  let «meta» : DocumentMeta := {
    uri                 := "file:///test.lean"
    mod                 := `Test
    version             := 0
    text                := source.toFileMap
    dependencyBuildMode := .never
  }
  -- An inert "header parsed" snapshot: `result? := none` means no further
  -- processing is available, and `mkCmdSnaps` (the `cmdSnaps` default) yields an
  -- empty list. Neither is read by Strategy A.
  let initSnap : Language.Lean.InitialSnapshot := {
    diagnostics := .empty
    metaSnap    := default
    ictx        := meta.mkInputContext
    stx         := .missing
    result?     := none
  }
  let diagnosticsMutex ← Std.Mutex.new { stickyDiagsRef := ← IO.mkRef {} }
  let doc : EditableDocument := {
    «meta», initSnap, diagnosticsMutex
    reporter := .pure ()
  }
  let bufRef ← IO.mkRef { : IO.FS.Stream.Buffer }
  return {
    rpcSessions          := ∅
    doc
    hLog                 := IO.FS.Stream.ofBuffer bufRef
    initParams           := { capabilities := {} }
    cancelTk             := ← RequestCancellationToken.new
    serverRequestEmitter := fun _ _ => return .pure (.failure .internalError "stub emitter")
  }

/-- Run a `RequestM` action against a context, surfacing `RequestError` as an elaboration error. -/
def runRequest (ctx : RequestContext) (action : RequestM α) : CommandElabM α := do
  match ← (action.run ctx).toBaseIO with
  | .ok a    => return a
  | .error e => throwError "RequestM failed: {e.message}"

/-- Fabricate a `Snapshots.Snapshot` from the current `CommandElabM` state. -/
def snapshotOfCurrentState : CommandElabM Snapshots.Snapshot := do
  return {
    stx     := .missing
    mpState := {}
    cmdState := ← get
  }

/-! ## Demonstrations -/

-- 1. A bare `RequestM` action that reads `doc.meta`.
run_cmd do
  let ctx ← mkStubRequestContext "theorem ex : True := trivial"
  let summary ← runRequest ctx do
    let doc ← RequestM.readDoc
    return s!"uri={doc.meta.uri} version={doc.meta.version} len={doc.meta.text.source.length}"
  logInfo summary

-- 2. `RequestM.runCoreM`: inspect the environment carried by the snapshot.
run_cmd do
  let ctx ← mkStubRequestContext "-- snapshot env probe"
  let snap ← snapshotOfCurrentState
  let hasNat ← runRequest ctx do
    RequestM.runCoreM snap do
      let env ← getEnv
      return env.contains ``Nat
  logInfo s!"env contains `Nat`: {hasNat}"

-- 3. `RequestM.runTermElabM`: elaborate a term and report its type.
run_cmd do
  let ctx ← mkStubRequestContext "-- snapshot term elab"
  let snap ← snapshotOfCurrentState
  let typeStr ← runRequest ctx do
    RequestM.runTermElabM snap do
      let e ← Lean.Elab.Term.elabTerm (← `(term| (1 : Nat) + 1)) none
      let ty ← Lean.Meta.inferType e
      return toString (← Lean.Meta.ppExpr ty)
  logInfo s!"inferred type: {typeStr}"
