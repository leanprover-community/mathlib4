/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Meta.Tactic.Rewrites
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.EditDistance.Estimator
import Mathlib.Data.MLList.BestFirst
import Mathlib.Order.Interval.Finset.Nat
import Batteries.Data.MLList.Heartbeats

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

namespace Mathlib.Tactic.RewriteSearch

open Lean Meta
open Lean.Meta.Rewrites
open Lean.Meta.LazyDiscrTree (ModuleDiscrTreeRef)

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
  return s.splitOn.map splitDelimiters |>.flatten

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

/--
What is the cost for changing a token?
`Levenshtein.defaultCost` just uses constant cost `1` for any token.

It may be interesting to try others.
the only one I've experimented with so far is `Levenshtein.stringLogLengthCost`,
which performs quite poorly!
-/
def editCost : Levenshtein.Cost String String Nat := Levenshtein.defaultCost

/-- Check whether a goal can be solved by `rfl`, and fill in the `SearchNode.rfl?` field. -/
def compute_rfl? (n : SearchNode) : MetaM SearchNode := do
  try
    withoutModifyingState <| withMCtx n.mctx do
      -- We use `withReducible` here to follow the behaviour of `rw`.
      n.goal.refl
      pure { n with mctx := ← getMCtx, rfl? := some true }
  catch _e =>
    withMCtx n.mctx do
      if (←  try? n.goal.applyRfl).isSome then
        pure { n with mctx := ← getMCtx, rfl? := some true }
      else
        pure { n with rfl? := some false }

/-- Fill in the `SearchNode.dist?` field with the edit distance between the two sides. -/
def compute_dist? (n : SearchNode) : SearchNode :=
  match n.dist? with
  | some _ => n
  | none =>
    { n with dist? := some (levenshtein editCost n.lhs n.rhs) }

/-- Represent a search node as string, solely for debugging. -/
def toString (n : SearchNode) : MetaM String := do
  let n := n.compute_dist?
  let tac ← match n.history.back? with
  | some (_, e, true) => do let pp ← ppExpr e; pure s!"rw [← {pp}]"
  | some (_, e, false) => do let pp ← ppExpr e; pure s!"rw [{pp}]"
  | none => pure ""
  return s!"depth: {n.history.size}\n\
    history: {n.history.map fun p => hash p % 10000}\n\
    {tac}\n\
    -- {n.ppGoal}\n\
    distance: {n.dist?.get!}+{n.history.size}, {n.ppGoal.length}"

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
    return some r

/-- Construct an initial `SearchNode` from a goal. -/
def init (goal : MVarId) : MetaM (Option SearchNode) := mk #[] goal
/-- Add an additional step to the `SearchNode` history. -/
def push (n : SearchNode) (expr : Expr) (symm : Bool) (k : Nat) (g : MVarId)
    (ctx : Option MetavarContext := none) : MetaM (Option SearchNode) :=
  mk (n.history.push (k, expr, symm)) g ctx

/-- Report the index of the most recently applied lemma, in the ordering returned by `rw?`. -/
def lastIdx (n : SearchNode) : Nat :=
  match n.history.back? with
  | some (k, _) => k
  | none => 0

instance : Ord SearchNode where
  compare := compareOn fun n => toLex (toLex (n.ppGoal.length, n.lastIdx), n.ppGoal)

/--
A somewhat arbitrary penalty function.
Note that `n.lastIdx` penalizes using later lemmas from a particular call to `rw?` at a node,
but once we have moved on to the next node these penalties are "forgiven".

(You might in interpret this as encouraging
the algorithm to "trust" the ordering provided by `rw?`.)

I tried out a various (positive) linear combinations of
`.history.size`, `.lastIdx`, and `.ppGoal.length` (and also the `.log2`s of these).
* `.lastIdx.log2` is quite good, and the best coefficient is around 1.
* `.lastIdx / 10` is almost as good.
* `.history.size` makes things worse (similarly with `.log2`).
* `.ppGoal.length` makes little difference (similarly with `.log2`).
Here testing consisting of running the current `rw_search` test suite,
rejecting values for which any failed, and trying to minimize the run time reported by
```shell
lake build &&  \
time (lake env lean test/RewriteSearch/Basic.lean; \
  lake env lean test/RewriteSearch/Polynomial.lean)
```

With a larger test suite it might be worth running this minimization again,
and considering other penalty functions.

(If you do this, please choose a penalty function which is in the interior of the region
where the test suite works.
I think it would be a bad idea to optimize the run time at the expense of fragility.)
-/
def penalty (n : SearchNode) : Nat := n.lastIdx.log2 + n.ppGoal.length.log2

/-- The priority function for search is Levenshtein distance plus a penalty. -/
abbrev prio (n : SearchNode) : Thunk Nat :=
  (Thunk.pure n.penalty) + (Thunk.mk fun _ => levenshtein editCost n.lhs n.rhs)
/-- We can obtain lower bounds, and improve them, for the Levenshtein distance. -/
abbrev estimator (n : SearchNode) : Type :=
  Estimator.trivial n.penalty × LevenshteinEstimator editCost n.lhs n.rhs

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
    (lemmas : ModuleDiscrTreeRef (Name × RwDirection))
    (forbidden : NameSet := ∅) (n : SearchNode) : MLList MetaM SearchNode := .squash fun _ => do
  if ← isTracingEnabledFor `rw_search then do
    trace[rw_search] "searching:\n{← toString n}"
  let candidates ← rewriteCandidates hyps lemmas n.type forbidden
  -- Lift to a monadic list, so the caller can decide how much of the computation to run.
  return MLList.ofArray candidates
    |>.filterMapM (fun ⟨lem, symm, weight⟩ =>
        rwLemma n.mctx n.goal n.type .solveByElim lem symm weight)
    |>.enum
    |>.filterMapM fun ⟨k, r⟩ => do n.rewrite r k

/--
Perform best first search on the graph of rewrites from the specified `SearchNode`.
-/
def search (n : SearchNode)
    (stopAtRfl := true) (stopAtDistZero := true)
    (forbidden : NameSet := ∅) (maxQueued : Option Nat := none) :
    MLList MetaM SearchNode := .squash fun _ => do
  let hyps ← localHypotheses
  let moduleRef ← createModuleTreeRef
  let search := bestFirstSearchCore (maxQueued := maxQueued)
    (β := String) (removeDuplicatesBy? := some SearchNode.ppGoal)
    prio estimator (rewrites hyps moduleRef forbidden) n
  let search ←
    if ← isTracingEnabledFor `rw_search then do
      pure <| search.mapM fun n => do trace[rw_search] "{← toString n}"; pure n
    else
      pure search
  let search := if stopAtRfl then
    search.mapM compute_rfl? |>.takeUpToFirst fun n => n.rfl? = some true
  else
    search
  return if stopAtDistZero then
    search.map (fun r => r.compute_dist?) |>.takeUpToFirst (fun r => r.dist? = some 0)
  else
    search

end SearchNode

open Elab Tactic Lean.Parser.Tactic

/--
`rw_search` attempts to solve an equality goal
by repeatedly rewriting using lemmas from the library.

If no solution is found,
the best sequence of rewrites found before `maxHeartbeats` elapses is returned.

The search is a best-first search, minimising the Levenshtein edit distance between
the pretty-printed expressions on either side of the equality.
(The strings are tokenized at spaces,
separating delimiters `(`, `)`, `[`, `]`, and `,` into their own tokens.)

You can use `rw_search [-my_lemma, -my_theorem]`
to prevent `rw_search` from using the names theorems.
-/
syntax "rw_search" (rewrites_forbidden)? : tactic

open Lean.Meta.Tactic.TryThis

elab_rules : tactic |
    `(tactic| rw_search%$tk $[[ $[-$forbidden],* ]]?) => withMainContext do
  let forbidden : NameSet :=
    ((forbidden.getD #[]).map Syntax.getId).foldl (init := ∅) fun s n => s.insert n
  let .some init ← SearchNode.init (← getMainGoal) | throwError "Goal is not an equality."
  let results := init.search (forbidden := forbidden) |>.whileAtLeastHeartbeatsPercent 20
  let results ← results.force
  let min ← match results with
  | [] => failure
  | h :: t =>
      pure <| t.foldl (init := h) fun r₁ r₂ =>
        if r₁.rfl? = some true then r₁
        else if r₂.rfl? = some true then r₂
        else if r₁.dist?.getD 0 ≤ r₂.dist?.getD 0 then r₁ else r₂
  let state ← saveState
  setMCtx min.mctx
  replaceMainGoal [min.goal]
  let type? ← if min.rfl? = some true then pure none else do pure <| some (← min.goal.getType)
  addRewriteSuggestion tk (min.history.toList.map (·.2))
    type?.toLOption (origSpan? := ← getRef) (checkState? := state)

end RewriteSearch

end Mathlib.Tactic
