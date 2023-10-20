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

The `rw_search` tactic will rewrite by local hypotheses,
but will not use local hypotheses to discharge side conditions.
This limitation would need to be resolved in the `rw?` tactic first.

-/

set_option autoImplicit true

namespace Lean.Expr

@[inline] def app3?' (e : Expr) (fName : Name) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity' fName 3 then
    some (e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none


@[inline] def eq?' (p : Expr) : Option (Expr × Expr × Expr) :=
  p.app3?' ``Eq

end Lean.Expr

namespace Mathlib.Tactic.RewriteSearch

open Lean Meta
open Mathlib.Tactic.Rewrites

initialize registerTraceClass `rw_search
initialize registerTraceClass `rw_search.detail

/-- Separate a string into a list of strings by pulling off initial `(` or `]` characters,
and pulling off terminal `)`, `]`, or `,` characters. -/
partial def splitDelimiters (s : String) : List String :=
  let rec /-- Pull off leading delimiters. -/ auxStart front pre :=
    let head := s.get front
    if head = '(' || head = '[' then
      auxStart (s.next front) (head.toString :: pre)
    else
      (front, pre)
  let rec /-- Pull off trailing delimiters. -/ auxEnd back suff :=
    let last := s.get back
    if last = ')' || last = ']' || last = ',' then
      auxEnd (s.prev back) (last.toString :: suff)
    else
      (back, suff)
  let (frontAfterStart, pre) := auxStart 0 []
  let (backAfterEnd, suff) := auxEnd (s.prev s.endPos) []
  pre.reverse ++ [s.extract frontAfterStart (s.next backAfterEnd)] ++ suff

/--
Tokenize a string at whitespace, and then pull off delimiters.
-/
-- `rw_search` seems to return better results if we tokenize
-- rather than just breaking the string into characters,
-- but more extensive testing would be great!
-- Tokenizing of course makes the edit distance calculations cheaper,
-- because the lists are significantly shorter.
-- On the other hand, because we currently use unweighted edit distance,
-- this makes it "cheap" to change one identifier for another.
def tokenize (e : Expr) : MetaM (List String) := do
  let s := (← ppExpr e).pretty
  return s.splitOn.map splitDelimiters |>.join

/--
Data structure containing the history of a rewrite search.
-/
structure SearchNode where mk' ::
  /-- The lemmas used so far. -/
  -- The first component is the index amongst successful rewrites at the previous node.
  history : Array (Nat × Expr × Bool)
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

def editCost : Levenshtein.Cost String String Nat := Levenshtein.stringLogLength

/-- Check whether a goal can be solved by `rfl`, and fill in the `SearchNode.rfl?` field. -/
def compute_rfl? (n : SearchNode) : MetaM SearchNode := withMCtx n.mctx do
  if (← try? n.goal.rfl).isSome then
    pure { n with mctx := ← getMCtx, rfl? := some true }
  else
    pure { n with rfl? := some false }

/-- Fill in the `SearchNode.dist?` field with the edit distance between the two sides. -/
def compute_dist? (n : SearchNode) : SearchNode :=
  match n.dist? with
  | some _ => n
  | none =>
    { n with dist? := some (levenshtein editCost n.lhs n.rhs) }

instance : ToString SearchNode where
  toString n :=
  let n := n.compute_dist?
  s!"depth: {n.history.size}\n" ++
  s!"history: {n.history.map fun p => hash p % 10000}\n" ++
  (match n.history.back? with
    | some (_, e, true) => s!"rw [← {e}]"
    | some (_, e, false) => s!"rw [{e}]"
    | none => "") ++ "\n" ++ "-- " ++ n.ppGoal ++ "\n" ++ s!"distance: {n.dist?.get!}+{n.history.size}, {n.ppGoal.length}"

/-- Construct a `SearchNode`. -/
def mk (history : Array (Nat × Expr × Bool)) (goal : MVarId) (ctx : Option MetavarContext := none) :
    MetaM (Option SearchNode) := goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  match type.eq? with
  | none => return none
  | some (_, lhs, rhs) =>
    let lhsTokens ← tokenize lhs
    let rhsTokens ← tokenize rhs
    let r :=
      { history := history
        mctx := ← ctx.getDM getMCtx
        goal := goal
        type := type
        ppGoal := (← ppExpr type).pretty
        lhs := lhsTokens
        rhs := rhsTokens }
    -- trace[rw_search] s!"{r}"
    return some r

/-- Construct an initial `SearchNode` from a goal. -/
def init (goal : MVarId) : MetaM (Option SearchNode) := mk #[] goal
/-- Add an additional step to the `SearchNode` history. -/
def push (n : SearchNode) (expr : Expr) (symm : Bool) (k : Nat) (g : MVarId)
    (ctx : Option MetavarContext := none) : MetaM (Option SearchNode) :=
  mk (n.history.push (k, expr, symm)) g ctx

def lastIdx (n : SearchNode) : Nat :=
  match n.history.back? with
  | some (k, _) => k
  | none => 0

instance : Ord SearchNode where
  compare := compareOn fun n => toLex (toLex (n.ppGoal.length, n.lastIdx), n.ppGoal)

/-- The priority function for search is Levenshtein distance. -/
abbrev prio (n : SearchNode) : Thunk Nat :=
  (Thunk.pure n.history.size) + (Thunk.mk fun _ => levenshtein editCost n.lhs n.rhs)
/-- We can obtain lower bounds, and improve them, for the Levenshtein distance. -/
abbrev estimator (n : SearchNode) : Type :=
  Estimator.trivial n.history.size × LevenshteinEstimator editCost n.lhs n.rhs

/-- Given a `RewriteResult` from the `rw?` tactic, create a new `SearchNode` with the new goal. -/
def rewrite (n : SearchNode) (r : Rewrites.RewriteResult) (k : Nat) :
    MetaM (Option SearchNode) :=
  withMCtx r.mctx do
    let goal' ← n.goal.replaceTargetEq r.result.eNew r.result.eqProof
    n.push r.expr r.symm k goal' (← getMCtx)

/--
Given a pair of `DiscrTree` trees
indexing all rewrite lemmas in the imported files and the current file,
try rewriting the current goal in the `SearchNode` by one of them,
returning a `MLList MetaM SearchNode`, i.e. a lazy list of next possible goals.
-/
def rewrites (hyps : Array (Expr × Bool × Nat))
    (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (n : SearchNode) : MLList MetaM SearchNode := .squash fun _ => do
  trace[rw_search] "searching: {n}"
  return rewritesDedup hyps lemmas n.mctx n.goal n.type |>.enum |>.filterMapM fun ⟨k, r⟩ => do n.rewrite r k

/--
Perform best first search on the graph of rewrites from the specified `SearchNode`.
-/
def search (n : SearchNode)
    (stopAtRfl := true) (stopAtDistZero := true) (maxQueued : Option Nat := none) :
    MLList MetaM SearchNode := .squash fun _ => do
  let hyps ← localHypotheses
  let lemmas ← rewriteLemmas.get
  let search := bestFirstSearchCore (maxQueued := maxQueued)
    (β := String) (removeDuplicatesBy? := some SearchNode.ppGoal)
    prio estimator (rewrites hyps lemmas) n
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
  let type? := if min.rfl? = some true then none else some (← min.goal.getType)
  addRewriteSuggestion tk (min.history.toList.map (·.2))
    type? (origSpan? := ← getRef)
