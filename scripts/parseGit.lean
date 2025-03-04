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
  | {file := f, rg := {first := _, last := la}} => f != "" && la != 0

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
      nextGDA := {nextGDA with file := fA}
      nextGDB := {nextGDB with file := fB}
    if l.startsWith "@@ -" then
      let [la, ra, lb, rb] := l.getNats | continue
      nextGDA := {nextGDA with rg := ⟨la, la + ra⟩}
      nextGDB := {nextGDB with rg := ⟨lb, lb + rb⟩}
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
info: (#[file: .github/workflows/bench_summary_comment.yml, lines 33-36, file: .github/workflows/bors.yml, lines 186-196, file: .github/workflows/bors.yml, lines 330-336], #[file: .github/workflows/bench_summary_comment.yml, lines 33-44, file: .github/workflows/bors.yml, lines 186-198, file: .github/workflows/bors.yml, lines 332-347])
-/
#guard_msgs in
#eval do
  let tots := diffToGitDiff test
  dbg_trace tots
