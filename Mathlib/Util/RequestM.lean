import Lean.Server.Requests
import Lean.Server.CodeActions.Basic

/-!
# Utilities for `RequestM`

This file provides a means to run `RequestM` and `CodeActionProvider` inside of other meta monads for testing purposes.
-/

open Lean Server FileWorker Elab Command

def mkDummyInitSnap (ictx : Parser.InputContext) (stx : Syntax) :
    Language.Lean.InitialSnapshot where
  diagnostics := .empty
  metaSnap    := default
  ictx
  stx
  result?     := none

open Lean Language Lean in
def mkCommandResultSnapshot (desc := "syntheticSnap") : CommandElabM CommandResultSnapshot :=
  return {
    desc
    cmdState := ← get
    diagnostics := ← Snapshot.Diagnostics.ofMessageLog (← get).messages
    traces := ← getTraceState
    infoTree? := (← getInfoTrees)[0]?
  }

def Lean.FileMap.mkDummyRequestContext (map : FileMap) (fileName : System.FilePath) (mod : Name)
    (cmdSnaps? : Option (IO.AsyncList IO.Error Snapshots.Snapshot) := none)
    (initSnap? : Option Language.Lean.InitialSnapshot := none) :
    IO RequestContext := do
  let «meta» : DocumentMeta := {
    uri                 := System.Uri.pathToUri fileName
    mod                 := mod
    version             := 0
    text                := map
    dependencyBuildMode := .never
  }
  let initSnap := initSnap?.getD (mkDummyInitSnap meta.mkInputContext .missing)
  let diagnosticsMutex ← Std.Mutex.new { stickyDiagsRef := ← IO.mkRef {} }
  let doc : EditableDocument := if let some cmdSnaps := cmdSnaps? then
      { «meta», initSnap, cmdSnaps, diagnosticsMutex, reporter := .pure () }
    else
      { «meta», initSnap, diagnosticsMutex, reporter := .pure () }

  let bufRef ← IO.mkRef { : IO.FS.Stream.Buffer }
  return {
    rpcSessions          := ∅
    doc
    hLog                 := IO.FS.Stream.ofBuffer bufRef
    initParams           := { capabilities := {} }
    cancelTk             := ← RequestCancellationToken.new
    serverRequestEmitter := fun _ _ => return .pure (.failure .internalError "dummy emitter")
  }

/-- Fabricate a `Snapshots.Snapshot` from the current `CommandElabM` state. -/
def mkDummySnapshot (cmd : Syntax) : CommandElabM Snapshots.Snapshot := do
  return {
  stx      := cmd
  mpState  := { pos := cmd.getTrailingTailPos?.get! } -- wrong? end of `stx` instead?
  cmdState := ← get }

def mkDummyRequestContext (cmd : Syntax)
  (initSnap? : Option Language.Lean.InitialSnapshot := none) : CommandElabM RequestContext := do
  (← getFileMap).mkDummyRequestContext ⟨← getFileName⟩ (← getMainModule)
    (some <| IO.AsyncList.ofList [← mkDummySnapshot cmd]) initSnap?

deriving instance Repr for JsonRpc.ErrorCode

-- Ultimately, the `cmd` is responible for giving the `cmdSnaps` in the `RequestM` context appropriate position info, such that `withWaitForSnap` in `handleCodeAction` accepts it.
/-- Run a `RequestM` action against a context, surfacing `RequestError` as an elaboration error. -/
def liftRequestM {α} (cmd : Syntax)
    (action : RequestM α) : CommandElabM α := do
  match ← (action.run (← mkDummyRequestContext cmd)).toBaseIO.toIO with -- TODO: lifting?
  | .ok a    => return a
  | .error e => throwError "`RequestM` action failed with code [{repr e.code}]:\n{e.message}"



#check Lsp.CodeActionParams

@[inline] def Lean.Server.CodeActionProvider.runRequestM (cmd : Syntax)
    (params : Lsp.CodeActionParams) (snap : Snapshots.Snapshot) (action : CodeActionProvider) :
    CommandElabM (Array LazyCodeAction) :=
  liftRequestM cmd (action params snap)

open RequestM in
@[inline] def mkCodeActionParams (range : Lsp.Range) (context : Lsp.CodeActionContext := {}) :
    RequestM Lsp.CodeActionParams :=
  return { textDocument := ⟨(← readDoc).meta.uri⟩, range, context }

open RequestM in
def Lean.Server.CodeActionProvider.run (cmd : Syntax)
    (range : Lsp.Range) (action : CodeActionProvider) (context : Lsp.CodeActionContext := {}) :
    CommandElabM (Array LazyCodeAction) := do
  let snap ← mkDummySnapshot (← getRef)
  liftRequestM cmd do
    action (← mkCodeActionParams range context) snap

open RequestM in

-- def Lean.Server.CodeActionProvider.runSyntax
--     (range : Syntax.Range) (action : CodeActionProvider) (context : Lsp.CodeActionContext := {}) :
--     CommandElabM (Array LazyCodeAction) := do
--   let snap ← mkDummySnapshot
--   liftRequestM do
--     let m := (← readDoc).meta
--     action { textDocument := ⟨m.uri⟩, range := m.text.utf8RangeToLspRange range, context } snap

def simple : CodeActionProvider := fun params _ => return #[{
    eager.title := s!"{params.range.start} → {params.range.end}"}]

def String.Slice.toSyntaxRange (s : String.Slice) : Syntax.Range where
  start := s.startInclusive.offset
  stop  := s.endExclusive.offset

def Lean.FileMap.ofPosition? (map : FileMap) (pos : Position) : Option String.Pos.Raw := do
  guard <| 1 ≤ pos.line && pos.line ≤ map.getLastLine
  let p := map.ofPosition pos
  guard <| p ≤ map.lineStart (pos.line + 1)
  return p

def Lean.FileMap.lspPosToUtf8Pos? (text : FileMap) (pos : Lsp.Position) :
    Option String.Pos.Raw := do
  guard <| pos.line < text.getLastLine
  let p := text.lspPosToUtf8Pos pos
  -- `Lsp.Position` is 0-indexed; `+1` for equivalent `line` index, `+1` to check next line
  guard <| p ≤ text.lineStart (pos.line + 2)
  return p

def Lean.FileMap.lspRangeToUtf8Range? (text : FileMap) (range : Lsp.Range) :
    Option Syntax.Range := do
  let start ← text.lspPosToUtf8Pos? range.start
  let stop ← text.lspPosToUtf8Pos? range.end
  return { start, stop }

def getCaretRanges (cmd : Syntax) : CommandElabM <|
    Array (Except Syntax.Range (Syntax.Range × Lsp.Range)) := do
  let some range := cmd.getRangeWithTrailing? | return #[]
  let src := (← getFileMap).source
  let slice := src.slice! (src.pos! range.start) (src.pos! range.stop)
  let splits := slice.split "--"
  let carets := splits.filterMap fun slice =>
    let carets := slice.takeWhile '^'
    if carets.isEmpty then none else some carets
  let mut ranges := #[]
  for caret in carets do
    let originalRange := caret.toSyntaxRange
    let aboveRange := originalRange.toLspRange (← getFileMap)
    let aboveRange := { aboveRange with
      start.line := aboveRange.start.line - 1
      end.line := aboveRange.end.line - 1 }
    if let some aboveSyntaxRange := (← getFileMap).lspRangeToUtf8Range? aboveRange then
      ranges := ranges.push <| .ok (aboveSyntaxRange, aboveRange)
    else
      ranges := ranges.push <| .error originalRange
  return ranges

instance : ToMessageData RequestError where
  toMessageData e := m!"[error code: {repr e.code}]\n{e.message}"

nonrec def Lean.Lsp.CodeAction.logAt (stx : Syntax) (action : Lsp.CodeAction)
    (severity := MessageSeverity.information) : CommandElabM Unit := do
  let mut msg := m!"Code action{action.kind?.elim "" (s!"({·})")}: {action.title}\n"
  -- if let some edit := action.edit? then
    -- msg := msg ++ m!"{edit.documentChanges?}"
  -- let anyExtraData := action.command?.isSome || action.data?.isSome || action.diagnostics?.isSome || action.isPreferred?.isSome || action.disabled?.isSome
  -- if anyExtraData then
  --   pure () -- TODO: add metadata
  logAt stx msg severity

def testCodeActions : Linter where
  run cmd := do
    let caretRanges ← getCaretRanges cmd
    for range in caretRanges do
      match range with
      | .error orig =>
        -- TODO: tweak message
        logErrorAt (.ofRange orig) m!"This range does not have characters above it."
      | .ok (stxRange, lspRange) =>
        let snap ← mkDummySnapshot cmd
        let actions ← liftRequestM cmd do
          let params ← mkCodeActionParams lspRange
          let task ← handleCodeAction params
          let s := (← simple params snap).map (·.eager)
          return task.get.map (· ++ s)
        match actions with
        | .error e => logErrorAt (.ofRange stxRange) m!"{e}"
        | .ok actions =>
          for action in actions do action.logAt (.ofRange stxRange)

initialize addLinter testCodeActions
