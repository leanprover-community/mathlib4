/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Estimator
import Mathlib.Data.MLList.BestFirst
import Mathlib.Data.Nat.Interval

/-!
# The `rw_search` tactic

`rw_search` attempts to solve an equality goal
by repeatedly rewriting using lemmas from the library.

If no solution is found,
the best sequence of rewrites found before `maxHeartbeats` elapses is returned.

The search is a best-first search, minimising the Levenshtein edit distance between
the pretty-printed expressions on either side of the equality.
(The strings are tokenized at spaces,
separating delimiters `(`, `)`, `[`, `]`, and `,` into their own tokens.)

The implementation avoids completely computing edit distances where possible,
only computing lower bounds sufficient to decide which path to take in the search.

# Future improvements

We could call `simp` as an atomic step of rewriting.

The edit distance heuristic could be replaced by something else.

No effort has been made to choose the best tokenization scheme, and this should be investigated.
Moreover, the Levenshtein distance function is customizable with different weights for each token,
and it would be interesting to try optimizing these
(or dynamically updating them,
adding weight to tokens that persistently appear on one side of the equation but not the other.)

Currently the `rw?` tactic (for generating a single rewrite) will not rewrite by a local hypothesis.
Similarly, it will not use local hypotheses to discharge side conditions during rewriting.

-/

set_option autoImplicit true

namespace Mathlib.Tactic.RewriteSearch

open Lean Meta
open Mathlib.Tactic.Rewrites

/-- Separate a string into a list of strings by pulling off initial `(` or `]` characters,
and pulilng off terminal `)`, `]`, or `,` characters. -/
partial def splitDelimiters (s : String) : List String :=
  if s.startsWith "(" || s.startsWith "[" then
    s.take 1 :: splitDelimiters (s.drop 1)
  else if s.endsWith ")" || s.endsWith "]" || s.endsWith "," then
    splitDelimiters (s.dropRight 1) ++ [s.takeRight 1]
  else
    [s]

/--
Tokenize a string at whitespace, and then pull off delimiters.
-/
-- This appears to work better than just breaking the string into characters,
-- but more extensive testing would be great!
def tokenize (e : Expr) : MetaM (List String) := do
  let s := (← ppExpr e).pretty
  return s.splitOn.map splitDelimiters |>.join

/-- info: ["1", "+", "(", "3", "+", "5", ")"] -/
#guard_msgs in
open Qq in
#eval tokenize q(1 + (3 + 5))

/--
Data structure containing the history of a rewrite search.
-/
structure SearchNode where mk' ::
  /-- The lemmas used so far. -/
  history : Array (Name × Bool)
  /-- The metavariable context after rewriting.
  We carry this around so the search can safely backtrack. -/
  mctx : MetavarContext
  /-- The current goal. -/
  goal : MVarId
  /-- The type of the current goal. -/
  type : Expr
  /-- The pretty printed current goal. -/
  ppGoal : String
  /-- The tokenization of the left-hand-side of the current goal. -/
  lhs : List String
  /-- The tokenization of the right-hand-side of the current goal. -/
  rhs : List String
  /-- Whether the current goal can be closed by `rfl` (or `none` if this hasn't been test yet). -/
  rfl? : Option Bool := none
  /-- The edit distance between the tokenizations of the two sides
  (or `none` if this hasn't been computed yet). -/
  dist? : Option Nat := none

namespace SearchNode

/-- Construct a `SearchNode`. -/
def mk (history : Array (Name × Bool)) (goal : MVarId) (ctx : Option MetavarContext := none) :
    MetaM (Option SearchNode) := do
  let type ← instantiateMVars (← goal.getType)
  match type.eq? with
  | none => return none
  | some (_, lhs, rhs) =>
    let lhsTokens ← tokenize lhs
    let rhsTokens ← tokenize rhs
    return some
      { history := history
        mctx := ← ctx.getDM getMCtx
        goal := goal
        type := type
        ppGoal := (← ppExpr type).pretty
        lhs := lhsTokens
        rhs := rhsTokens }

/-- Check whether a goal can be solved by `rfl`, and fill in the `SearchNode.rfl?` field. -/
def compute_rfl? (n : SearchNode) : MetaM SearchNode := withMCtx n.mctx do
  if (← try? n.goal.rfl).isSome then
    pure { n with mctx := ← getMCtx, rfl? := some true }
  else
    pure { n with rfl? := some false }

/-- Fill in the `SearchNode.dist?` field with the edit distance between the two sides. -/
def compute_dist? (n : SearchNode) : SearchNode :=
  { n with dist? := some (levenshtein Levenshtein.defaultCost n.lhs n.rhs) }

/-- Construct an initial `SearchNode` from a goal. -/
def init (goal : MVarId) : MetaM (Option SearchNode) := mk #[] goal
/-- Add an additional step to the `SearchNode` history. -/
def push (n : SearchNode) (name : Name) (symm : Bool) (g : MVarId)
    (ctx : Option MetavarContext := none) : MetaM (Option SearchNode) :=
  mk (n.history.push (name, symm)) g ctx

instance : Ord SearchNode where
  compare := compareOn SearchNode.ppGoal

/-- The priority function for search is Levenshtein distance. -/
abbrev prio (n : SearchNode) : Thunk Nat :=
  Thunk.mk fun _ => (levenshtein Levenshtein.defaultCost n.lhs n.rhs)
/-- We can obtain lower bounds, and improve them, for the Levenshtein distance. -/
abbrev estimator (n : SearchNode) : Type := LevenshteinEstimator Levenshtein.defaultCost n.lhs n.rhs

/-- Given a `RewriteResult` from the `rw?` tactic, create a new `SearchNode` with the new goal. -/
def rewrite (n : SearchNode) (r : Rewrites.RewriteResult) :
    MetaM (Option SearchNode) :=
  withMCtx r.mctx do
    let goal' ← n.goal.replaceTargetEq r.result.eNew r.result.eqProof
    n.push r.name r.symm goal' (← getMCtx)

/--
Given a pair of `DiscrTree` trees
indexing all rewrite lemmas in the imported files and the current file,
try rewriting the current goal in the `SearchNode` by one of them,
returning a `MLList MetaM SearchNode`, i.e. a lazy list of next possible goals.
-/
def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (n : SearchNode) : MLList MetaM SearchNode :=
  rewritesCore lemmas n.mctx n.goal n.type |>.filterMapM fun r => do n.rewrite r

/--
Perform best first search on the graph of rewrites from the specified `SearchNode`.
-/
def search (n : SearchNode)
    (stopAtRfl := true) (stopAtDistZero := true) (maxQueued : Option Nat := none) :
    MLList MetaM SearchNode := .squash fun _ => do
  let lemmas ← rewriteLemmas.get
  -- TODO think about whether we should use `removeDuplicates := true` here (seems unhelpful)
  -- or if there are other ways we can deduplicate.
  let search := bestFirstSearchCore (maxQueued := maxQueued)
    prio estimator (rewrites lemmas) n
  let search := if stopAtRfl then
    search.mapM compute_rfl? |>.takeUpToFirst fun n => n.rfl? = some true
  else
    search
  return if stopAtDistZero then
    search.map (fun r => r.compute_dist?) |>.takeUpToFirst (fun r => r.dist? = some 0)
  else
    search

end SearchNode

open Elab Tactic

/--
`rw_search` attempts to solve an equality goal
by repeatedly rewriting using lemmas from the library.

If no solution is found,
the best sequence of rewrites found before `maxHeartbeats` elapses is returned.

The search is a best-first search, minimising the Levenshtein edit distance between
the pretty-printed expressions on either side of the equality.
(The strings are tokenized at spaces,
separating delimiters `(`, `)`, `[`, `]`, and `,` into their own tokens.)
-/
syntax "rw_search" : tactic

elab_rules : tactic |
    `(tactic| rw_search%$tk) => do
  let .some init ← SearchNode.init (← getMainGoal) | throwError "Goal is not an equality."
  let results := init.search |>.whileAtLeastHeartbeatsPercent 20
  let results ← results.force
  let min ← match results with
  | [] => failure
  | h :: t =>
    pure <| t.foldl (init := h) fun r₁ r₂ => if r₁.dist?.getD 0 ≤ r₂.dist?.getD 0 then r₁ else r₂
  setMCtx min.mctx
  replaceMainGoal [min.goal]
  let rules ← min.history.toList.mapM fun ⟨n, s⟩ => do pure (← mkConstWithFreshMVarLevels n, s)
  let type? := if min.rfl? = some true then none else some (← min.goal.getType)
  addRewriteSuggestion tk rules
    type? (origSpan? := ← getRef)
