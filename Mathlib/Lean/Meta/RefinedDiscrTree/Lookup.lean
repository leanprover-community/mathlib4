/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Encode

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

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/-- Monad for working with a `RefinedDiscrTree`. -/
private abbrev TreeM α := StateRefT (Array (Trie α)) MetaM

/-- Run a `TreeM` computation using a `RefinedDiscrTree`. -/
private def runTreeM (d : RefinedDiscrTree α) (m : TreeM α β) :
    MetaM (β × RefinedDiscrTree α) := do
  let { tries, root } := d
  let (result, tries) ← withReducible <| m.run tries
  pure (result, { tries, root })

private def setTrie (i : TrieIndex) (v : Trie α) : TreeM α Unit :=
  modify (·.set! i v)

/-- Create a new trie with the given lazy entry. -/
private def newTrie (e : LazyEntry × α) : TreeM α TrieIndex := do
  modifyGet fun a => let sz := a.size; (sz, a.push (.node #[] {} {} #[e]))

/-- Add a lazy entry to an existing trie. -/
private def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry × α) : TreeM α Unit :=
  modify (·.modify i fun | .node vs star cs p => .node vs star cs (p.push e))

/-- Evaluate the `Trie α` at index `trie`,
replacing it with the evaluated value,
and returning the new `values`, `stars` and `children`. -/
private def evalNode (trie : TrieIndex) :
    TreeM α (Array α × Std.HashMap Nat TrieIndex × Std.HashMap Key TrieIndex) := do
  let .node values stars children pending := (← get)[trie]!
  if pending.isEmpty then
    return (values, stars, children)
  setTrie trie default
  let mut values := values
  let mut stars := stars
  let mut children := children
  for (entry, value) in pending do
    match ← evalLazyEntry entry with
    | none => values := values.push value
    | some xs =>
      for (key, entry) in xs do
        let entry := (entry, value)
        match star? key with
        | some id =>
          if let some idx := stars[id]? then
            addLazyEntryToTrie idx entry
          else
            stars := stars.insert id (← newTrie entry)
        | none =>
          if let some idx := children[key]? then
            addLazyEntryToTrie idx entry
          else
            children := children.insert key (← newTrie entry)

  setTrie trie <| .node values stars children #[]
  return (values, stars, children)
where
  /-- Helper function that helps reduce compilation time -/
  @[inline] star? : Key → Option Nat
    | .star id => some id
    | _ => none


/--
A match result contains the results from matching a term against
patterns in the discrimination tree.
-/
structure MatchResult (α : Type) where
  /--
  The elements in the match result.

  The top-level array represents an array from `score` values to the
  results with that score. The elements of this array are themselves
  arrays of non-empty arrays so that we can defer concatenating results until
  needed.
  -/
  elts : Array (Array (Array α)) := #[]
  deriving Inhabited
namespace MatchResult

private def push (r : MatchResult α) (score : Nat) (e : Array α) : MatchResult α :=
  if e.isEmpty then
    r
  else if score < r.elts.size then
    { elts := r.elts.modify score (·.push e) }
  else
    let rec loop (a : Array (Array (Array α))) :=
        if a.size < score then
          loop (a.push #[])
        else
          { elts := a.push #[e] }
    termination_by score - a.size
    loop r.elts

/--
Number of elements in result
-/
partial def size (mr : MatchResult α) : Nat :=
  mr.elts.foldl (fun i a => a.foldl (fun n a => n + a.size) i) 0

/--
Append results to array
-/
@[specialize]
partial def appendResults (mr : MatchResult α) (a : Array β) (f : Nat → α → β) : Array β :=
  let aa := mr.elts
  let n := aa.size
  Nat.fold (n := n) (init := a) fun i _ r =>
    let j := n-1-i
    let b := aa[j]
    b.foldl (init := r) (· ++ ·.map (f j))

/--
Convert a `MatchResult` into a `Array`, with better matches at the start of the array.
-/
def toArray (mr : MatchResult α) : Array α :=
  mr.elts.foldr (init := #[]) fun a r => a.foldl (init := r) (· ++ ·)

end MatchResult


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
  /-- Metavariable assignments for `.star` patterns in the discrimination tree.
    We use a `List Key`, in the reverse order. -/
  treeStars : Std.HashMap Nat (List Key) := {}
  /-- Metavariable assignments for `.star` patterns in the lookup expression.
    We use a `List Key`, in the reverse order. -/
  queryStars : AssocList Nat (List Key) := {}
  deriving Inhabited


/-- Add to the `todo` stack all matches that result from a `.star id` in the query expression. -/
private partial def matchQueryStar (id : Nat) (trie : TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (skip : Nat := 1) (skipped : List Key := []) :
    TreeM α (Array PartialMatch) := do
  match skip with
  | skip+1 =>
    let (_, stars, children) ← evalNode trie
    let todo ← stars.foldM (init := todo) fun todo id trie =>
      matchQueryStar id trie pMatch todo skip (.star id :: skipped)
    children.foldM (init := todo) fun todo key trie =>
      matchQueryStar id trie pMatch todo (skip + key.arity) (key :: skipped)
  | 0 =>
    match pMatch.queryStars.find? id with
    | some keys =>
      if keys == skipped then
        return todo.push { pMatch with trie, score := pMatch.score + keys.length }
      else
        return todo
    | none =>
      let queryStars := pMatch.queryStars.insert id skipped
      return todo.push { pMatch with trie, queryStars }

/-- Return every value that is indexed in the tree. -/
private def matchEverything (tree : RefinedDiscrTree α) : TreeM α (MatchResult α) := do
  let pMatches ← tree.root.foldM (init := #[]) fun todo key trie =>
    matchQueryStar 0 trie { keys := [], score := 0, trie := 0 } todo key.arity [key]
  pMatches.foldlM (init := {}) fun result pMatch => do
    let (values, _) ← evalNode pMatch.trie
    return result.push (score := 0) values

/-- Add to the `todo` stack all matches that result from a `.star _` in the discrimination tree. -/
private partial def matchTreeStars (key : Key) (stars : Std.HashMap Nat TrieIndex)
    (pMatch : PartialMatch) (todo : Array PartialMatch) : Array PartialMatch :=
  if stars.isEmpty then
    todo
  else
    let (dropped, keys) := drop [key] pMatch.keys key.arity
    stars.fold (init := todo) fun todo id trie =>
      match pMatch.treeStars[id]? with
      | some assignment =>
        if dropped == assignment then
          todo.push { pMatch with keys, trie, score := pMatch.score + dropped.length }
        else
          todo
      | none =>
        let treeStars := pMatch.treeStars.insert id dropped
        todo.push { pMatch with keys, trie, treeStars }
where
  /-- Drop the keys corresponding to the next `n` expressions. -/
  drop (dropped rest : List Key) (n : Nat) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n+1 =>
      let key :: rest := rest | panic! "too few keys"
      drop (key :: dropped) rest (n + key.arity)

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
  if todo.isEmpty then
    return result
  else
    let pMatch := todo.back!
    let todo := todo.pop
    let (values, stars, children) ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) values) unify
    | key :: keys =>
      let pMatch := { pMatch with keys }
      if let .star id := key then
        if unify then
          let todo ← matchQueryStar id pMatch.trie pMatch todo
          getMatchLoop todo result unify
        else
          let todo := matchTreeStars key stars pMatch todo
          getMatchLoop todo result unify
      else
        let todo := matchTreeStars key stars pMatch todo
        let todo := matchKey key children pMatch todo
        getMatchLoop todo result unify

/-- Return a matchResult, containing the results from the pattern `[.star 0]`. -/
private def matchTreeRootStar (root : Std.HashMap Key TrieIndex) : TreeM α (MatchResult α):= do
  match root[Key.star 0]? with
  | none => return {}
  | some trie =>
    let (values, _) ← evalNode trie
    return ({} : MatchResult α).push (score := 0) values

/-- Find values that match `e` in `d`.
if `unify == true` then metavarables in `e` can be assigned. -/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify matchRootStar : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) := do
  let (key, keys) ← encodeExpr' e
  withReducible do runTreeM d do
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key == .star 0 then
      if unify then
        if matchRootStar then
          matchEverything d
        else
          return {}
      else
        matchTreeRootStar d.root
    else
      let todo := matchKey key d.root pMatch #[]
      if matchRootStar then
        getMatchLoop todo (← matchTreeRootStar d.root) unify
      else
        getMatchLoop todo {} unify

end Lean.Meta.RefinedDiscrTree
