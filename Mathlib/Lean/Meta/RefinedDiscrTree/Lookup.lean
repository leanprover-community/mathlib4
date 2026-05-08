/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Lean.Meta.RefinedDiscrTree.Encode

/-!
# Matching with a RefinedDiscrTree

This file defines the matching procedure for the `RefinedDiscrTree`.

The main definitions are
* The structure `MatchResult`, which contains the match results, ordered by matching score.
* The (private) function `evalNode` which evaluates a node of the `RefinedDiscrTree`
* The (private) function `getMatchLoop`, which is the main function that computes the matches.
  It implements the non-deterministic computation by keeping a stack of `PartialMatch`es,
  and repeatedly processing the most recent one.
* The matching function `getMatch` that also returns an updated `RefinedDiscrTree`

To find the matches, we first encode the expression as a `List Key`. Then using this,
we find all matches with the tree. When `unify == true`, we also allow metavariables in the target
expression to be assigned.

We use a simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` (and in the target if `unify == true`), we store the assignment,
and when it is attempted to be assigned again, we check that it is the same assignment.

-/

public section

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/-- Monad for working with a `RefinedDiscrTree`. -/
private abbrev TreeM α := StateRefT (Array (Trie α)) MetaM

/-- Run a `TreeM` computation using `d : RefinedDiscrTree`, without losing the reference to `d`. -/
@[inline] private def runTreeM (d : RefinedDiscrTree α) (m : TreeM α β) :
    MetaM (β × RefinedDiscrTree α) := do
  let { tries, root } := d
  let (result, tries) ← m.run tries
  pure (result, { tries, root })

private def setTrie (i : TrieIndex) (v : Trie α) : TreeM α Unit :=
  modify (·.set! i v)

/-- Create a new trie with the given lazy entry. -/
private def newTrie (e : LazyEntry × α) : TreeM α TrieIndex := do
  modifyGet fun a => (a.size, a.push (.node #[] none {} {} #[e]))

/-- Add a lazy entry to an existing trie. -/
private def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry × α) : TreeM α Unit :=
  modify (·.modify i fun node => { node with pending := node.pending.push e })

/-- Process a specified range of pending entries.
returns the computed values and pending nodes. -/
private def processPending (pending : Array (LazyEntry × α)) (start stop : Nat) :
    MetaM (Array α × Array (Key × LazyEntry × α)) := do
  Core.checkInterrupted
  let mut values := #[]
  let mut newEntries := #[]
  for (entry, value) in pending[start...stop] do
    match ← evalLazyEntry entry true with
    | some entries =>
      for (key, entry) in entries do
        newEntries := newEntries.push (key, entry, value)
    | none =>
      values := values.push value
  return (values, newEntries)

/--
Evaluate the `Trie α` at index `trie`,
replacing it with the evaluated value,
and returning the `Trie α`.

Performance note: In the `apply` search discrimination tree, after root node `⟨Eq, 3⟩`,
there are about `150,000` entries in the `pending` array.
To deal with this smoothly, we parallellize the computation into chunks of `5000` entries.
-/
private def evalNode (trie : TrieIndex) : TreeM α (Trie α) := do
  let node := (← get)[trie]!
  if node.pending.isEmpty then
    return node
  let numTasks := node.pending.size / 5000 + 1
  Core.checkInterrupted
  let tasks ← numTasks.foldM (init := #[]) fun i _ tasks ↦ do
    return tasks.push <| ← EIO.asTask <|
      Core.withCurrHeartbeats (processPending node.pending (i * 5000) ((i + 1) * 5000))
        |>.run' (← readThe _) (← getThe _)
        |>.run' (← readThe _) (← getThe _)
  setTrie trie default -- reduce the reference count to `node` to be 1
  let mut { values, star, labelledStars, children, .. } := node
  for task in tasks do
    let (values', newEntries) ← MonadExcept.ofExcept task.get
    values := values ++ values'
    for (key, entry) in newEntries do
      match key with
      | .labelledStar label =>
        if let some trie := labelledStars[label]? then
          addLazyEntryToTrie trie entry
        else
          labelledStars := labelledStars.insert label (← newTrie entry)
      | .star =>
        if let some trie := star then
          addLazyEntryToTrie trie entry
        else
          star := some (← newTrie entry)
      | _ =>
        if let some trie := children[key]? then
          addLazyEntryToTrie trie entry
        else
          children := children.insert key (← newTrie entry)
  let node := { values, star, labelledStars, children, pending := #[] }
  setTrie trie node
  return node


/--
A match result contains the results from matching a term against
patterns in the discrimination tree.
-/
structure MatchResult (α : Type) where
  /--
  The elements in the match result.

  The `Nat` in the tree map represents the `score` of the results.
  The elements are arrays of arrays, where each sub-array corresponds to one discr tree pattern.
  -/
  elts : Std.TreeMap Nat (Array (Array α)) := {}
  deriving Inhabited

private def MatchResult.push (mr : MatchResult α) (score : Nat) (e : Array α) : MatchResult α :=
  { elts := mr.elts.alter score fun | some arr => arr.push e | none => #[e] }

/--
Convert a `MatchResult` into a `Array`, with better matches at the start of the array.
-/
def MatchResult.toArray (mr : MatchResult α) : Array α :=
  mr.elts.foldr (init := #[]) fun _ a r => a.foldl (init := r) (· ++ ·)

/--
Convert a `MatchResult` into an `Array` of `Array`s. Each `Array` corresponds to one pattern.
The better matching patterns are at the start of the outer array.
For each inner array, the entries are ordered in the order they were inserted.
-/
def MatchResult.flatten (mr : MatchResult α) : Array (Array α) :=
  mr.elts.foldr (init := #[]) (fun _ arr cand => cand ++ arr)

/-
A partial match captures the intermediate state of a match execution.

N.B. Discrimination tree matching has non-determinism due to stars,
so the matching loop maintains a stack of partial match results.
-/
private structure PartialMatch where
  /-- Remaining terms to match -/
  keys : List Key
  /-- Number of non-star matches so far -/
  score : Nat
  /-- Trie to match next -/
  trie : TrieIndex
  /-- Metavariable assignments for `.labelledStar` patterns in the discrimination tree.
  We use a `List Key`, in the reverse order. -/
  treeStars : Std.HashMap Nat (List Key) := {}
  deriving Inhabited


/--
Add to the `todo` stack all matches that result from a `.star` in the query expression.
-/
private partial def matchQueryStar (trie : TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (skip : Nat := 1) : TreeM α (Array PartialMatch) := do
  match skip with
  | skip+1 =>
    let { star, labelledStars, children, .. } ← evalNode trie
    let mut todo := todo
    if let some trie := star then
      todo ← matchQueryStar trie pMatch todo skip
    todo ← labelledStars.foldM (init := todo) fun todo _ trie =>
      matchQueryStar trie pMatch todo skip
    todo ← children.foldM (init := todo) fun todo key trie =>
      matchQueryStar trie pMatch todo (skip + key.arity)
    return todo
  | 0 =>
    return todo.push { pMatch with trie }

/-- Return every value that is indexed in the tree. -/
private def matchEverything (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let pMatches ← root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar trie { keys := [], score := 0, trie := 0 } todo key.arity
  pMatches.foldlM (init := {}) fun result pMatch => do
    let { values, .. } ← evalNode pMatch.trie
    return result.push (score := 0) values

/--
Types are counted less towards the total matching score.
The reason is that types are usually implicit arguments. For example

- If the goal is `(1 : ℕ) = 1`, we could find
  - `rfl (a : α) : a = a`.
    This gets extra points for matching `1`
  - `Nat.succ.inj (n m : ℕ) (h : n.succ = m.succ) : n = m`.
    This gets extra points for matching `ℕ`
  Clearly, `rfl` is better.
- If we rewrite `|(0 : ℝ)|`, we could find
  - `abs_zero : |(0 : α)| = 0`
    This gets extra points for matching `0`
  - `Real.norm_eq_abs : ∀ (r : ℝ), ‖r‖ = |r|`
    This gets extra points for matching `ℝ`
  Clearly, `abs_zero` is better

In both examples, matching the type (`ℕ` or `ℝ`) was not very important for how good
the match actually was.
-/
private def Key.score (key : Key) : MetaM Nat := do
  match key with
  | .const n _ =>
    if (← getConstInfo n).type.getForallBody.isSort then
      return 1
    else
      return 10
  | .fvar fvarId _ =>
    if (← fvarId.getType).getForallBody.isSort then
      return 1
    else
      return 10
  | _ => return 10

/-- Add to the `todo` stack all matches that result from a `.star _` in the discrimination tree. -/
private partial def matchTreeStars (key : Key) (node : Trie α) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (unify : Bool) : MetaM (Array PartialMatch) := do
  let { star, labelledStars, .. } := node
  if labelledStars.isEmpty && star.isNone then
    return todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    let mut todo := todo
    if let some trie := star then
      todo := todo.push { pMatch with keys, trie }
    todo ← node.labelledStars.foldM (init := todo) fun todo id trie => do
      if let some assignment := pMatch.treeStars[id]? then
        let eq lhs rhs := if unify then (isEq lhs.reverse rhs.reverse).isSome else lhs == rhs
        if eq dropped assignment then
          return todo.push { pMatch with
            keys, trie
            score := (← dropped.mapM (·.score)).foldl (· + ·) pMatch.score }
        else
          return todo
      else
        let treeStars := pMatch.treeStars.insert id dropped
        return todo.push { pMatch with keys, trie, treeStars }
    return todo
where
  /-- Drop the keys corresponding to the next `n` expressions. -/
  drop (dropped rest : List Key) (n : Nat) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n + 1 =>
      let key :: rest := rest | panic! "too few keys"
      drop (key :: dropped) rest (n + key.arity)

  isEq (lhs rhs : List Key) : Option (List Key × List Key) := do
    match lhs with
    | [] => panic! "too few keys"
    | .star :: lhs =>
      let (_, rhs) := drop [] rhs 1
      return (lhs, rhs)
    | lHead :: lhs =>
    match rhs with
    | [] => panic! "too few keys"
    | .star :: rhs =>
      let (_, lhs) := drop [] lhs 1
      return (lhs, rhs)
    | rHead :: rhs =>
      guard (lHead == rHead)
      lHead.arity.foldM (init := (lhs, rhs)) fun _ _ (lhs, rhs) => isEq lhs rhs

/-- Add to the `todo` stack the match with `key`. -/
private def matchKey (key : Key) (children : Std.HashMap Key TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if key == .opaque then todo else
  match children[key]? with
  | none      => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

/-- Return the possible `Trie α` that match with `keys`. -/
private partial def getMatchLoop (todo : Array PartialMatch) (result : MatchResult α)
    (unify : Bool) : TreeM α (MatchResult α) := do
  if h : todo.size = 0 then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let node ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) node.values) unify
    | key :: keys =>
      let pMatch := { pMatch with keys }
      match key with
      -- `key` is not a `.labelledStar`
      | .star =>
        if unify then
          let todo ← matchQueryStar pMatch.trie pMatch todo
          getMatchLoop todo result unify
        else
          let todo ← matchTreeStars key node pMatch todo unify
          getMatchLoop todo result unify
      | _ =>
        let todo ← matchTreeStars key node pMatch todo unify
        let todo := matchKey key node.children pMatch todo
        getMatchLoop todo result unify

/-- Return the results from matching the pattern `[.star]` or `[.labelledStar 0]`. -/
private def matchTreeRootStar (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α) := do
  let mut result := {}
  if let some trie := root[Key.labelledStar 0]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  if let some trie := root[Key.star]? then
    let { values, .. } ← evalNode trie
    result := result.push (score := 0) values
  return result

/--
Find values that match `e` in `d`.
* If `unify == true` then metavariables in `e` can be assigned.
* If `matchRootStar == true` then we allow metavariables at the root to unify.
  Set this to `false` to avoid getting excessively many results.
-/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) := do
  withReducible do runTreeM d do
    let (key, keys) ← encodeExpr e (labelledStars := false)
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star then
      if matchRootStar then
        if unify then
          matchEverything d.root
        else
          matchTreeRootStar d.root
      else
        return {}
    else
      let todo := matchKey key d.root pMatch #[]
      if matchRootStar then
        getMatchLoop todo (← matchTreeRootStar d.root) unify
      else
        getMatchLoop todo {} unify

end Lean.Meta.RefinedDiscrTree
