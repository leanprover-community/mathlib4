import Lean

open Lean

/--
Given a list `l` of `α` and a predicate `f : α → Bool`, group the entries of `l` into
consecutive sublists that either all satisfy the predicate, or are singletons, and then
remove all singletons that do not satisfy `f`.
-/
def List.isolate {α} [Inhabited α] (l : List α) (f : α → Bool) : List (List α) :=
  let grp := l.splitBy (f · && f ·)
  grp.filterMap fun s => if s.isEmpty || f (s.getD 0 default) then some s else none

/-- Similar to `List.isolate`, except that it acts on the characters making up the list input. -/
def String.isolate (str : String) (f : Char → Bool) : List String :=
  str.toList.isolate f |>.map (⟨·⟩)

#guard "abA 123,cd\n456\n7 \n0".isolate (·.isDigit) == ["123", "456", "7", "0"]

/-- `String.getNats l` takes as input a string and returns the list of `Nat`
where each entry is the natural number corresponding to each consecutive
sequence of digits in `l`, in their order. -/
def String.getNats (l : String) : List Nat :=
  l.isolate (·.isDigit) |>.map (·.toNat!)

/--  A `lineRg` contains the first and last modified lines in a `GitDiff`. -/
structure lineRg where
  first : Nat
  last : Nat
  deriving Inhabited

/-- A `GitDiff` contains a file and a line range. -/
structure GitDiff where
  file : System.FilePath := ""
  rg : lineRg := default
  deriving Inhabited

instance : ToString GitDiff where
  toString := fun
  | {file := f, rg := {first := fi, last := la}} => s!"file: {f}, lines {fi}-{la}"

/--
`GitDiff.isReady g` checks whether the `GitDiff` `g` contains a non-empty file name
and a non-empty range.
-/
def GitDiff.isReady : GitDiff → Bool
  | {file := f, rg := {first := fi, last := la}} => f != "" && fi != la

/--
Check whether the `GitDiff` `g` is ready.
* If `g.isReady`, then append it to the array `a` and return the "template" `GitDiff`
  containing just the input file name.
* If `! g.isReady`, then return `g` and `a` unchanged.
-/
def GitDiff.appendIfReady (a : Array GitDiff) (g : GitDiff) (f : System.FilePath) :
    GitDiff × Array GitDiff :=
  if g.isReady then ({file := f}, a.push g) else (g, a)

/--
Convert a string containing either a single natural number or two natural numbers into a `lineRg`.
The convention seems to be that
* a single natural number `a` corresponds to line `a` having been modified;
* two natural numbers `a`, `b` correspond to a range starting with `a` and spanning `b` lines.
A range of `0` lines, i.e. `b = 0`, corresponds to no modification.

`GitDiff.isReady` is aware of this and acts consequently.
-/
def assignLineRanges (s : String) : lineRg :=
  match s.getNats with
  | [a] => {first := a, last := a + 1}
  | [a, b] => {first := a, last := a + b}
  | _ => panic s!"{s}: I have not seen this range of lines in a git-diff"

/--
`diffToGitDiff s` converts the output of `git diff` into two arrays of `GitDiff`s,
the first one corresponding to the edits in the source,
the second one corresponding to the edits in the target.
-/
def diffToGitDiff (s : String) : Array GitDiff × Array GitDiff := Id.run do
  let mut totA : Array GitDiff := ∅
  let mut totB : Array GitDiff := ∅
  let lines := s.splitOn "\n"
  let mut nextGDA : GitDiff := {}
  let mut nextGDB : GitDiff := {}
  let mut fileA := ""
  let mut fileB := ""
  for l in lines do
    if l.startsWith "diff --git a/" then
      let [fA, fB] := l.drop "diff --git a/".length |>.splitOn " b/" | continue
      fileA := fA
      fileB := fB
      nextGDA := {nextGDA with file := fileA}
      nextGDB := {nextGDB with file := fileB}
    if l.startsWith "@@ -" then
      let _ :: ls :: _ := l.splitOn "@@" | continue
      let [left, right] := ls.trim.splitOn " " | continue
      let rgA := assignLineRanges left
      let rgB := assignLineRanges right
      nextGDA := {nextGDA with rg := rgA}
      nextGDB := {nextGDB with rg := rgB}
    (nextGDA, totA) := nextGDA.appendIfReady totA fileA
    (nextGDB, totB) := nextGDB.appendIfReady totB fileA
  return (totA, totB)

def test := "+          ./scripts/declarations_diff_lean_shell_glue.sh \"${PR_NUMBER}\" \"${PR_HASH}\"
diff --git a/.github/workflows/bench_summary_comment.yml b/.github/workflows/bench_summary_comment.yml
index fe14ecdc32a..4d3c99a8f2c 100644
--- a/.github/workflows/bench_summary_comment.yml
+++ b/.github/workflows/bench_summary_comment.yml
@@ -33,3 +33,11 @@ jobs:
         env:
           PR:  ${{ github.event.issue.number }}
           GH_TOKEN: ${{secrets.GITHUB_TOKEN}}
+
+      - name: Remove \"bench-after-CI\"
+        # we use curl rather than octokit/request-action so that the job won't fail
+        # (and send an annoying email) if the labels don't exist
+        run: |
+          curl --request DELETE \
+            --url https://api.github.com/repos/${{ github.repository }}/issues/${{ github.event.issue.number }}/labels/bench-after-CI \
+            --header 'authorization: Bearer ${{ secrets.GITHUB_TOKEN }}'
diff --git a/.github/workflows/bors.yml b/.github/workflows/bors.yml
index 9fbfeec9e2e..f381810c095 100644
--- a/.github/workflows/bors.yml
+++ b/.github/workflows/bors.yml
@@ -186,10 +186,12 @@ jobs:
           # Because the `lean-pr-testing-NNNN` branches use toolchains that are \"updated in place\"
           # the cache mechanism is unreliable, so we don't test it if we are on such a branch.
           if [[ ! $(cat lean-toolchain) =~ ^leanprover/lean4-pr-releases:pr-release-[0-9]+$ ]]; then
-            lake exe cache clean!
-            rm -rf .lake/build/lib/Mathlib
+            cd DownstreamTest
+            cp ../lean-toolchain .
+            MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
             lake exe cache get || (sleep 1; lake exe cache get)
-            lake build --no-build
+            lake build Plausible ProofWidgets
+            lake build --no-build Mathlib
           fi

       - name: build archive
@@ -330,6 +332,15 @@ jobs:
           cp ../lean-toolchain .
           lake build

+      - name: Add the \"awaiting-CI\" label
+        if: always()
+        # we use curl rather than octokit/request-action so that the job won't fail
+        # (and send an annoying email) if the labels don't exist
+        run: |
+          curl --request ADD \
+            --url https://api.github.com/repos/${{ github.repository }}/issues/${{ github.event.issue.number }}/labels/awaiting-CI \
+            --header 'authorization: Bearer ${{ secrets.GITHUB_TOKEN }}'
"

/--
info: [file: .github/workflows/bench_summary_comment.yml, lines 33-36,
 file: .github/workflows/bors.yml, lines 186-196,
 file: .github/workflows/bors.yml, lines 330-336]
---
info: [file: .github/workflows/bench_summary_comment.yml, lines 33-44,
 file: .github/workflows/bors.yml, lines 186-198,
 file: .github/workflows/bors.yml, lines 332-347]
-/
#guard_msgs in
#eval do
  let (totA, totB) := diffToGitDiff test
  logInfo m!"{totA}"
  logInfo m!"{totB}"

/--
info: [file: scripts/parseGit.lean, lines 26-27]
---
info: [file: scripts/parseGit.lean, lines 26-27,
 file: scripts/parseGit.lean, lines 32-33,
 file: scripts/parseGit.lean, lines 42-46,
 file: scripts/parseGit.lean, lines 49-55]
-/
#guard_msgs in
run_cmd
  let args := #["diff", "--unified=0",
    "420e511d5f1d81458aef9bd76f48b96b07d32908..55741ae1d9aaa639953dd63bcfe32ed00cf3b4f5"]
  let diffString ← IO.Process.run {cmd := "git", args := args}
  let (totA, totB) := diffToGitDiff diffString
  logInfo m!"{totA}"
  logInfo m!"{totB}"

/-- Get the `GitDiff`s with respect to `origin/master...HEAD`. -/
def gitDiffMaster (commit : String := "HEAD") : IO (Array GitDiff × Array GitDiff) := do
  let diffString ← IO.Process.run
    {cmd := "git", args := #["diff", "--unified=0", s!"origin/master...{commit}"]}
  pure <| diffToGitDiff diffString

/-
The linter reads the modified ranges and only emits a warning if `stx.getRange?` overlaps with
at least one range.

To feed the information about the ranges, maybe I can add an import on the first line, without a line break.

The new file contains the modified ranges and the linter option.
-/

def disjointRange (l m : lineRg) : Bool := (l.last < m.first) || (m.last < l.first)

def overlapOne (l m : lineRg) : Bool := ! disjointRange l m
  --(l.first ≤ m.first && m.first ≤ l.last) &&
  --(m.first ≤ l.first && l.first ≤ m.last) &&
  --true

def overlaps {m} [Monad m] [MonadLog m] [MonadFileMap m] (as : Array GitDiff) (rg : String.Range) : m Bool := do
  let fname ← getFileName
  let fm ← getFileMap
  let lineRange : lineRg :=
    { first := (fm.toPosition rg.start).line
      last  := (fm.toPosition rg.stop).line }
  pure <| (as.filter (·.file.toString == fname)).any (overlapOne lineRange ·.rg)

run_cmd
  let args := #["diff", "--unified=0",
    "420e511d5f1d81458aef9bd76f48b96b07d32908..55741ae1d9aaa639953dd63bcfe32ed00cf3b4f5"]
  let diffString ← IO.Process.run {cmd := "git", args := args}
  let (totA, totB) := diffToGitDiff diffString
  logInfo m!"{totA}"
  logInfo m!"{totB}"


run_cmd
  let mut tots := #[]
  let declsInModule := (← getEnv).constants.map₂
  --let declRanges := declRangeExt.get (← getEnv)
  for (name, _cinfo) in declsInModule do
    if ! name.isInternalDetail then
      if let some r ← findDeclarationRanges? name then
        tots := tots.binInsert (·.2.1.1 < ·.2.1.1) (name, (r.range.pos, r.range.endPos))
        --dbg_trace (name, (r.range.pos, r.range.endPos))
  dbg_trace ← gitDiffMaster
  dbg_trace tots
  --let edit := 34
  --dbg_trace tots.binSearch (default, ⟨0, 0⟩, default) fun (_, p1, q1) (_, p2, q2) => edit ≤ q1.1
  --_
