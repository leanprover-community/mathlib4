/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Cli.Basic

/-!
# Nightly testing checklist

`lake exe nightly-testing-checklist` reports the current state of the `nightly-testing` branches
at Batteries and Mathlib, including toolchain versions and CI status.

This script takes no actions — it only reports.
-/

namespace ANSIColor

def red (s : String) : String := s!"\x1b[31m{s}\x1b[0m"
def green (s : String) : String := s!"\x1b[32m{s}\x1b[0m"
def yellow (s : String) : String := s!"\x1b[33m{s}\x1b[0m"
def blue (s : String) : String := s!"\x1b[34m{s}\x1b[0m"
def bold (s : String) : String := s!"\x1b[1m{s}\x1b[0m"
def dim (s : String) : String := s!"\x1b[2m{s}\x1b[0m"

end ANSIColor

open ANSIColor in
/-- Run a command and return trimmed stdout, or an error description. -/
def runCmd (cmd : String) (args : Array String) : IO (Except String String) := do
  let r ← IO.Process.output { cmd, args }
  if r.exitCode != 0 then
    return .error s!"{cmd} failed: {r.stderr.trimAscii.toString}"
  return .ok r.stdout.trimAscii.toString

/-- Fetch a file's raw content from a GitHub repo at a given ref. -/
def ghRawFile (repo ref path : String) : IO (Except String String) :=
  runCmd "gh" #["api", s!"repos/{repo}/contents/{path}?ref={ref}",
    "-H", "Accept: application/vnd.github.raw"]

/-- Extract the nightly tag from a toolchain string like `leanprover/lean4:nightly-2026-03-25`. -/
def toolchainTag (tc : String) : String :=
  match tc.trimAscii.toString.splitOn ":" with
  | [_, tag] => tag
  | _ => tc.trimAscii.toString

/-- Find the latest lean4 nightly release tag from `leanprover/lean4-nightly`. -/
def getLatestNightly : IO (Except String String) := do
  let r ← runCmd "gh" #["api", "repos/leanprover/lean4-nightly/releases?per_page=1",
    "--jq", ".[0].tag_name"]
  match r with
  | .ok tag => if tag == "" then return .error "no nightly found" else return .ok tag
  | .error e => return .error e

/-- A CI run's key fields. -/
structure CIRun where
  status : String     -- "completed", "in_progress", "queued"
  conclusion : String -- "success", "failure", "" (if not yet completed)
  url : String

/-- Parse a CI run from three lines of jq output (status, conclusion, url). -/
def parseCIRun (lines : List String) : Except String CIRun :=
  match lines with
  | [status, conclusion, url] =>
    if status == "null" || status == "" then .error "no CI runs found"
    else .ok { status, conclusion := if conclusion == "null" then "" else conclusion, url }
  | _ => .error "unexpected output format"

/-- Get the most recent CI run for a repo/branch/workflow. -/
def getCIRun (repo branch workflow : String) : IO (Except String CIRun) := do
  match ← runCmd "gh" #["run", "list", "-R", repo, "-b", branch, "-w", workflow, "-L", "1",
      "--json", "status,conclusion,url",
      "--jq", ".[0] | .status, .conclusion, .url"] with
  | .error e => return .error e
  | .ok output => return parseCIRun (output.splitOn "\n")

/-- Get the most recent *completed* CI run for a repo/branch/workflow. -/
def getLastCompletedCIRun (repo branch workflow : String) : IO (Except String CIRun) := do
  match ← runCmd "gh" #["run", "list", "-R", repo, "-b", branch, "-w", workflow,
      "--status", "completed", "-L", "1",
      "--json", "status,conclusion,url",
      "--jq", ".[0] | .status, .conclusion, .url"] with
  | .error e => return .error e
  | .ok output => return parseCIRun (output.splitOn "\n")

/-- Extract the run ID from a GitHub Actions URL like
    `https://github.com/owner/repo/actions/runs/12345`. -/
def runIdFromUrl (url : String) : Option String :=
  match url.splitOn "/actions/runs/" with
  | [_, id] => some id
  | _ => none

/-- A failing CI job's id and name. -/
structure FailingJob where
  id : String
  name : String

/-- Get failing jobs for a CI run. -/
def getFailingJobs (repo : String) (runId : String) : IO (Array FailingJob) := do
  match ← runCmd "gh" #["api", s!"repos/{repo}/actions/runs/{runId}/jobs",
      "--paginate", "--jq",
      ".jobs[] | select(.conclusion == \"failure\") | (.id | tostring) + \"\\t\" + .name"] with
  | .ok output =>
    if output == "" then return #[]
    return output.splitOn "\n" |>.filterMap (fun line =>
      match line.splitOn "\t" with
      | [id, name] => some { id, name }
      | _ => none) |>.toArray
  | .error _ => return #[]

/-- Run a shell pipeline and return trimmed stdout. -/
def runShell (script : String) : IO String := do
  let r ← IO.Process.output { cmd := "bash", args := #["-c", script] }
  return r.stdout.trimAscii.toString

/-- Fetch build error lines from a job's log.
    Extracts Lean errors matching `path.lean:line:col: message`. -/
def getJobErrors (repo : String) (jobId : String) (limit : Nat := 10) : IO (Array String) := do
  let output ← runShell
    s!"gh api repos/{repo}/actions/jobs/{jobId}/logs 2>/dev/null | grep -oE 'error: [A-Za-z][A-Za-z0-9_/.]*\\.lean:[0-9]+:[0-9]+: .+' | sort -u | head -{limit}"
  if output == "" then return #[]
  return output.splitOn "\n" |>.toArray

open ANSIColor in
/-- Wait for a GitHub Actions run to complete, waking early on first job failure.
    Returns the conclusion ("success", "failure", etc.). -/
def watchRun (repo : String) (runId : String) (pollSeconds : Nat := 30) : IO String := do
  IO.print s!"  Waiting for CI "
  let stdout ← IO.getStdout
  let jq := "\"\\([.jobs[] | select(.status == \"completed\")] | length) \\([.jobs[] | select(.conclusion == \"failure\")] | length) \\(.jobs | length)\""
  let mut lastMsg := ""
  repeat
    match ← runCmd "gh" #["api", s!"repos/{repo}/actions/runs/{runId}/jobs", "--jq", jq] with
    | .ok output =>
      match output.splitOn " " with
      | [completedStr, failedStr, totalStr] =>
        let completed := completedStr.toNat?.getD 0
        let failed := failedStr.toNat?.getD 0
        let total := totalStr.toNat?.getD 1
        -- Wake on first failure
        if failed > 0 then
          IO.println s!" {red "✗"} ({completed}/{total} jobs, {failed} failed)"
          return "failure"
        -- Wake when all complete
        if completed == total then
          IO.println s!" {green "✓"} ({total}/{total} jobs)"
          -- Fetch the actual conclusion
          match ← runCmd "gh" #["api", s!"repos/{repo}/actions/runs/{runId}", "--jq", ".conclusion"] with
          | .ok conclusion => return conclusion
          | .error _ => return "success"
        -- Show progress
        let msg := s!"({completed}/{total})"
        if msg != lastMsg then
          IO.print s!"{dim msg} "
          stdout.flush
          lastMsg := msg
      | _ => pure ()
    | .error _ => pure ()
    -- Sleep between polls
    let _ ← IO.Process.output { cmd := "sleep", args := #[toString pollSeconds] }
  return "unknown"

/-! ## Fix infrastructure -/

/-- A parsed build error. -/
structure BuildError where
  file : String
  line : Nat
  col : Nat
  message : String
deriving Repr

/-- Parse an error line like `error: Foo/Bar.lean:123:8: message` into a `BuildError`. -/
def parseBuildError (s : String) : Option BuildError := do
  -- Strip "error: " prefix
  guard (s.startsWith "error: ")
  let rest := (s.drop 7).toString
  -- Split on ":" to get file:line:col: message
  let parts := rest.splitOn ":"
  guard (parts.length ≥ 4)
  let file := parts[0]!
  let line ← parts[1]!.toNat?
  let col ← parts[2]!.toNat?
  let message := (":".intercalate (parts.drop 3)).trimAscii.toString
  some { file, line, col, message }

/-- Is this error one we know how to fix? -/
def BuildError.isFixable (e : BuildError) : Bool :=
  e.message.contains "has already been declared"

deriving instance Inhabited for BuildError

/-- Clone a repo's nightly-testing branch to /tmp. Returns the directory path. -/
def cloneRepo (repo name : String) : IO String := do
  let dir := s!"/tmp/nightly-checking-{name}"
  -- Check if already cloned
  let dirCheck ← IO.Process.output { cmd := "test", args := #["-d", dir] }
  if dirCheck.exitCode == 0 then
    IO.println s!"  Using existing clone: {dir}"
    -- Reset to clean state and pull latest
    let _ ← IO.Process.output { cmd := "git", args := #["checkout", "."], cwd := dir }
    let _ ← IO.Process.output { cmd := "git", args := #["clean", "-fd"], cwd := dir }
    let _ ← IO.Process.output { cmd := "git", args := #["pull"], cwd := dir }
  else
    IO.println s!"  Cloning {repo} nightly-testing → {dir}"
    let cloneArgs := #["clone", "--depth", "1", "--branch", "nightly-testing",
        s!"https://github.com/{repo}.git", dir]
    let r ← IO.Process.output { cmd := "git", args := cloneArgs }
    if r.exitCode != 0 then
      throw <| IO.userError s!"clone failed: {r.stderr.trimAscii.toString}"
  return dir

/-- Check if a file belongs to this repo (not a dependency in .lake/packages/). -/
def isOwnFile (dir : String) (file : String) : IO Bool := do
  let check ← IO.Process.output { cmd := "test", args := #["-f", s!"{dir}/{file}"] }
  return check.exitCode == 0

/-- Run `lake build` in a directory and return parsed build errors for the repo's own files. -/
def buildAndCaptureErrors (dir : String) : IO (Array BuildError) := do
  IO.println s!"  Building in {dir}..."
  let r ← IO.Process.output { cmd := "lake", args := #["build"], cwd := dir }
  -- Write combined output to a temp file for reliable grep processing
  let tmpFile := s!"{dir}/.build-output.log"
  IO.FS.writeFile tmpFile (r.stdout ++ "\n" ++ r.stderr)
  let output ← runShell
    s!"grep -oE 'error: [A-Za-z][A-Za-z0-9_/.]*\\.lean:[0-9]+:[0-9]+: .+' {tmpFile} | sort -u"
  IO.FS.removeFile tmpFile |>.catchExceptions fun _ => pure ()
  if output == "" then return #[]
  let mut errors : Array BuildError := #[]
  for line in output.splitOn "\n" do
    if let some e := parseBuildError line then
      -- Only include errors in the repo's own files, not dependencies
      if ← isOwnFile dir e.file then
        errors := errors.push e
  return errors

/-- Copy the find_command_range.lean helper to the target repo. -/
def deployHelper (dir : String) : IO String := do
  let helperSrc := "scripts/find_command_range.lean"
  let helperDst := s!"{dir}/find_command_range.lean"
  let _ ← IO.Process.output { cmd := "cp", args := #[helperSrc, helperDst] }
  return helperDst

/-- Find the byte range of the command at a given position using the Lean parser.
    Includes any preceding attributes/doc comments that the parser split into separate commands. -/
def findCommandRange (dir : String) (file : String) (line col : Nat) :
    IO (Option (Nat × Nat)) := do
  let helperArgs := #["env", "lean", "--run", "find_command_range.lean", file,
    toString line, toString col]
  let r ← IO.Process.output { cmd := "lake", args := helperArgs, cwd := dir }
  if r.exitCode != 0 then
    IO.eprintln s!"    find_command_range failed: {r.stderr.trimAscii.toString}"
    return none
  let output := r.stdout.trimAscii.toString
  match output.splitOn " " with
  | [startStr, endStr] =>
    match (startStr.toNat?, endStr.toNat?) with
    | (some s, some e) => return some (s, e)
    | _ => return none
  | _ => return none

/-- Remove the byte range [start, end) from a file, trimming trailing whitespace at the cut. -/
def removeByteRange (filePath : String) (start stop : Nat) : IO Unit := do
  let contents ← IO.FS.readFile filePath
  -- Convert Nat byte positions to String slice operations
  let bytes := contents.toUTF8
  if stop > bytes.size then
    throw <| IO.userError s!"range {start}-{stop} exceeds file size {bytes.size}"
  let before := bytes.extract 0 start
  -- Skip whitespace/newlines after the removed range
  let mut afterStart := stop
  while afterStart < bytes.size && (bytes.get! afterStart == '\n'.toNat.toUInt8
      || bytes.get! afterStart == ' '.toNat.toUInt8
      || bytes.get! afterStart == '\r'.toNat.toUInt8) do
    afterStart := afterStart + 1
  -- But keep exactly one newline before the next content
  if afterStart > stop then
    afterStart := afterStart - 1
  let after := bytes.extract afterStart bytes.size
  let result := String.fromUTF8! (before ++ after)
  IO.FS.writeFile filePath result

/-- Check if we made progress: the first error moved to a later position or disappeared. -/
def madeProgress (oldErrors newErrors : Array BuildError) : Bool :=
  if newErrors.isEmpty then true
  else if oldErrors.isEmpty then false
  else
    let o := oldErrors[0]!
    let n := newErrors[0]!
    -- Progress if: different (later) file, or same file with same-or-later line
    n.file > o.file || (n.file == o.file && n.line >= o.line)

open ANSIColor in
/-- The fix loop: repeatedly fix the first fixable error, rebuild, and check progress. -/
def fixLoop (dir : String) : IO (Array String) := do
  let helperPath ← deployHelper dir
  let mut modifiedFiles : Array String := #[]
  let mut errors ← buildAndCaptureErrors dir
  let mut iterations := 0
  let maxIterations := 50
  while iterations < maxIterations do
    iterations := iterations + 1
    -- Find first fixable error
    let fixable := errors.filter (·.isFixable)
    if fixable.isEmpty then break
    let err := fixable[0]!  -- Inhabited instance derived above
    IO.println s!"  {yellow "→"} Fixing: {err.file}:{err.line}:{err.col}: {err.message}"
    -- Find the command range
    let some (start, stop) ← findCommandRange dir err.file err.line err.col
      | do IO.println s!"    {red "✗"} Could not find command range"; break
    IO.println s!"    Deleting bytes {start}-{stop}"
    -- Remove the declaration
    let filePath := s!"{dir}/{err.file}"
    removeByteRange filePath start stop
    if !modifiedFiles.contains err.file then
      modifiedFiles := modifiedFiles.push err.file
    -- Rebuild and check progress
    let newErrors ← buildAndCaptureErrors dir
    if !madeProgress errors newErrors then
      IO.println s!"    {red "✗"} No progress made, reverting"
      -- Revert the file
      let _ ← IO.Process.output { cmd := "git", args := #["checkout", "--", err.file], cwd := dir }
      break
    errors := newErrors
  -- Clean up helper
  IO.FS.removeFile helperPath |>.catchExceptions fun _ => pure ()
  return modifiedFiles

/-- Generate a patch from the current git diff. -/
def generatePatch (dir name : String) : IO String := do
  let patchPath := s!"/tmp/nightly-checking-{name}.patch"
  let r ← IO.Process.output { cmd := "git", args := #["diff"], cwd := dir }
  IO.FS.writeFile patchPath r.stdout
  return patchPath

/-- Commit and push changes. -/
def commitAndPush (dir : String) : IO Unit := do
  let _ ← IO.Process.output { cmd := "git", args := #["add", "-A"], cwd := dir }
  let commitArgs := #["commit", "-m", "chore: remove declarations that have been upstreamed"]
  let _ ← IO.Process.output { cmd := "git", args := commitArgs, cwd := dir }
  let pushArgs := #["push", "origin", "nightly-testing"]
  let r ← IO.Process.output { cmd := "git", args := pushArgs, cwd := dir }
  if r.exitCode != 0 then
    throw <| IO.userError s!"push failed: {r.stderr.trimAscii.toString}"

/-- An upstream dependency to check: package name and its GitHub repo. -/
structure UpstreamDep where
  name : String       -- lake package name (as it appears in lake-manifest.json)
  repo : String       -- GitHub repo (e.g. "leanprover-community/batteries")
  branch : String     -- branch to track (e.g. "nightly-testing")

/-- Get the rev of a package from a repo's lake-manifest.json. -/
def getManifestRev (repo branch pkg : String) : IO (Except String String) := do
  let jq := s!".packages[] | select(.name == \"{pkg}\") | .rev"
  runCmd "gh" #["api", s!"repos/{repo}/contents/lake-manifest.json?ref={branch}",
    "-H", "Accept: application/vnd.github.raw", "--jq", jq]

/-- Get the latest commit SHA on a branch. -/
def getLatestCommit (repo branch : String) : IO (Except String String) := do
  runCmd "gh" #["api", s!"repos/{repo}/commits/{branch}", "--jq", ".sha"]

open ANSIColor Cli in
/-- The implementation of `lake exe nightly-testing-checklist`. -/
def nightlyTestingChecklistCLI (args : Parsed) : IO UInt32 := do
  let noClone := args.hasFlag "no-clone"
  let noBuild := args.hasFlag "no-build"
  let doFix := args.hasFlag "fix"
  let doWatch := args.hasFlag "watch"
  IO.println (bold "Nightly Testing Checklist")
  IO.println ""

  -- Find the latest lean4 nightly
  let latestNightly ← getLatestNightly
  match latestNightly with
  | .ok tag => IO.println s!"Latest lean4 nightly: {blue tag}"
  | .error e => IO.println s!"Latest lean4 nightly: {red s!"unknown ({e})"}"
  IO.println ""

  let mut allGood := true
  let mut producedPatches := false

  let repos : Array (String × String × String × Array UpstreamDep) := #[
    ("Batteries", "leanprover-community/batteries", "build.yml", #[]),
    ("Mathlib", "leanprover-community/mathlib4-nightly-testing", "build.yml",
      #[{ name := "batteries", repo := "leanprover-community/batteries",
           branch := "nightly-testing" }])]

  for (name, repo, workflow, upstreamDeps) in repos do
    IO.println s!"{bold name} {dim s!"({repo})"} nightly-testing"

    -- Toolchain
    match ← ghRawFile repo "nightly-testing" "lean-toolchain" with
    | .ok tc =>
      let tag := toolchainTag tc
      IO.println s!"  Toolchain: {blue tag}"
      if let .ok latest := latestNightly then
        if tag == latest then
          IO.println s!"  {green "✓ up to date"}"
        else
          IO.println s!"  {red s!"✗ behind (latest: {latest})"}"
          allGood := false
    | .error e =>
      IO.println s!"  Toolchain: {red s!"error - {e}"}"
      allGood := false

    -- Upstream dependency freshness
    for dep in upstreamDeps do
      match ← getManifestRev repo "nightly-testing" dep.name,
            ← getLatestCommit dep.repo dep.branch with
      | .ok currentRev, .ok latestRev =>
        if currentRev == latestRev then
          IO.println s!"  {green s!"✓ {dep.name} up to date"}"
        else
          IO.println s!"  {red s!"✗ {dep.name} is stale"}"
          IO.println s!"    manifest: {dim (currentRev.take 12).toString}"
          IO.println s!"    latest:   {dim (latestRev.take 12).toString}"
          allGood := false
      | .error e, _ | _, .error e =>
        IO.println s!"  {dep.name}: {red s!"error - {e}"}"

    -- CI
    match ← getCIRun repo "nightly-testing" workflow with
    | .ok run =>
      let mut label := if run.conclusion == "" then run.status else run.conclusion
      if label == "success" then
        IO.println s!"  {green s!"✓ CI {label}"}"
      else if run.status == "in_progress" || run.status == "queued" then
        if doWatch then
          -- Wait for the run to finish
          if let some runId := runIdFromUrl run.url then
            IO.println s!"    {dim run.url}"
            let conclusion ← watchRun repo runId
            label := conclusion
            if conclusion == "success" then
              IO.println s!"  {green s!"✓ CI {conclusion}"}"
            else
              IO.println s!"  {red s!"✗ CI {conclusion}"}"
              allGood := false
        else
          IO.println s!"  {yellow s!"⋯ CI {label}"}"
          -- Show last completed run for context
          if let .ok prev ← getLastCompletedCIRun repo "nightly-testing" workflow then
            let prevColor := if prev.conclusion == "success" then green else red
            IO.println s!"    {dim s!"(last completed: {prevColor prev.conclusion})"}"
      else
        IO.println s!"  {red s!"✗ CI {label}"}"
        allGood := false
      unless doWatch && (run.status == "in_progress" || run.status == "queued") do
        IO.println s!"    {dim run.url}"
      -- Show failing jobs and their errors
      if label == "failure" then
        if let some runId := runIdFromUrl run.url then
          let jobs ← getFailingJobs repo runId
          for job in jobs do
            let errors ← getJobErrors repo job.id
            if errors.isEmpty then
              IO.println s!"    {red "✗"} {bold job.name}"
            else
              IO.println s!"    {red "✗"} {bold job.name}"
              for e in errors do
                IO.println s!"      {e}"
    | .error e =>
      IO.println s!"  CI: {red s!"error - {e}"}"
      allGood := false

    IO.println ""

  -- Phase 2: Fix staleness and failures (unless --no-clone)
  unless noClone do
    for (name, repo, _, upstreamDeps) in repos do
      -- Check what needs fixing
      let toolchainStale := match ← ghRawFile repo "nightly-testing" "lean-toolchain" with
        | .ok tc => match latestNightly with
          | .ok latest => toolchainTag tc != latest
          | .error _ => false
        | .error _ => false
      let mut depsStale := false
      for dep in upstreamDeps do
        match ← getManifestRev repo "nightly-testing" dep.name,
              ← getLatestCommit dep.repo dep.branch with
        | .ok currentRev, .ok latestRev => if currentRev != latestRev then depsStale := true
        | _, _ => pure ()
      let ciFailure := match ← getCIRun repo "nightly-testing" "build.yml" with
        | .ok run => run.conclusion == "failure"
        | .error _ => false
      unless toolchainStale || depsStale || ciFailure do continue
      IO.println (bold s!"Fixing {name}")
      let dir ← cloneRepo repo name
      -- Update toolchain if stale
      if toolchainStale then
        if let .ok latest := latestNightly then
          IO.println s!"  Updating lean-toolchain to {latest}..."
          IO.FS.writeFile s!"{dir}/lean-toolchain" s!"leanprover/lean4:{latest}\n"
          IO.println s!"  {green s!"✓ toolchain updated"}"
      -- Update stale upstream dependencies
      for dep in upstreamDeps do
        match ← getManifestRev repo "nightly-testing" dep.name,
              ← getLatestCommit dep.repo dep.branch with
        | .ok currentRev, .ok latestRev =>
          if currentRev != latestRev then
            IO.println s!"  Updating {dep.name}..."
            let r ← IO.Process.output { cmd := "lake", args := #["update", dep.name], cwd := dir }
            if r.exitCode != 0 then
              IO.println s!"  {red s!"lake update {dep.name} failed: {r.stderr.trimAscii.toString}"}"
            else
              IO.println s!"  {green s!"✓ {dep.name} updated"}"
        | _, _ => pure ()
      -- Fix build errors
      unless noBuild do
        let modifiedFiles ← fixLoop dir
        if modifiedFiles.isEmpty then
          IO.println s!"  No fixable errors found."
        else
          IO.println s!"  Modified {modifiedFiles.size} file(s)"
          for f in modifiedFiles do
            IO.println s!"    {f}"
      -- Check if there are any changes to commit (toolchain, deps, and/or fix loop)
      let diffCheck ← IO.Process.output { cmd := "git", args := #["diff", "--quiet"], cwd := dir }
      let cachedArgs := #["diff", "--quiet", "--cached"]
      let cachedCheck ← IO.Process.output { cmd := "git", args := cachedArgs, cwd := dir }
      let hasChanges := diffCheck.exitCode != 0 || cachedCheck.exitCode != 0
      if hasChanges then
        if doFix then
          commitAndPush dir
          IO.println s!"  {green "✓ Changes committed and pushed"}"
        else
          let patchPath ← generatePatch dir name
          IO.println s!"  {green s!"Patch written to: {patchPath}"}"
          producedPatches := true
      IO.println ""

  if producedPatches then
    IO.println s!"To automatically apply the patches, use `lake exe nightly-testing-checklist --fix`."

  return if allGood then 0 else 1

open Cli in
/-- Setting up command line options and help text for `lake exe nightly-testing-checklist`. -/
def nightlyTestingChecklist : Cmd := `[Cli|
  «nightly-testing-checklist» VIA nightlyTestingChecklistCLI; ["0.0.1"]
  "Report the current state of the nightly-testing branches at Batteries and Mathlib,
  including toolchain versions, CI status, and build errors."

  FLAGS:
    "no-clone"; "Do not clone repositories into /tmp for local investigation."
    "no-build"; "Do not run lake build in cloned repositories."
    "fix";      "Actually commit and push fixes (default is dry-run: generate patch only)."
    "watch";    "Wait for in-progress CI runs to complete before proceeding."
]

/-- The entrypoint to the `lake exe nightly-testing-checklist` command. -/
def main (args : List String) : IO UInt32 := nightlyTestingChecklist.validate args
