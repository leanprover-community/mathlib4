import Mathlib.Lean.Meta.RefinedDiscrTree.Evaluate

/-!
# Matching with a RefinedDiscrTree

This file defines the matching procedure for the `RefinedDiscrTree`.

We first encode the expression as a `List Key`. Then using this, we find all matches
with the tree. When `unify := true`, we also allow metavariables in the target
expression to be assigned.

We use a very simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` (and possibly in the target), we store the assignment, and when it is attempted
to be assigned again, we check that it is the same assignment.

Since the Discrimination tree is lazy, we also return a new `RefinedDiscrTree`.

The matching function is `getMatch`.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

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
  Nat.fold (n := n) (init := a) fun i r =>
    let j := n-1-i
    let b := aa[j]!
    b.foldl (init := r) (· ++ ·.map (f j))

end MatchResult


/-
A partial match captures the intermediate state of a match
execution.

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
  treeStars : PHashMap Nat (List Key) := {}
  /-- Metavariable assignments for `.star` patterns in the lookup expression.
    We use a `List Key`, in the reverse order. -/
  queryStars : PHashMap Nat (List Key) := {}
  deriving Inhabited



/-- Add to the stack all matches that result from a `.star id` in the query expression. -/
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


/-- Add to the stack all matches that result from a `.star _` in the discrimination tree. -/
private partial def matchTreeStars (key : Key) (stars : HashMap Nat TrieIndex)
    (pMatch : PartialMatch) (todo : Array PartialMatch) : Array PartialMatch :=
  if stars.isEmpty then
    todo
  else
    let (dropped, keys) := drop [key] pMatch.keys
    stars.fold (init := todo) fun todo id trie =>
      match pMatch.treeStars.find? id with
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
  drop (dropped rest : List Key) (n : Nat := 1) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n+1 =>
      let key :: rest := rest | panic! "too few keys"
      drop (key :: dropped) rest (n + key.arity)

/-- Add to the stack the match with `key`. -/
private def matchKey (key : Key) (children : HashMap Key TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if key matches .opaque then todo else
  match children.find? key with
  | none      => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

/-- Return the possible `Trie α` that match with `keys`. -/
private partial def getMatchLoop (todo : Array PartialMatch) (result : MatchResult α)
    (unify : Bool) : TreeM α (MatchResult α) := do
  if todo.isEmpty then
    return result
  else
    let pMatch := todo.back
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
private def matchTreeRootStar (root : HashMap Key TrieIndex) : TreeM α (MatchResult α):= do
  match root.find? (.star 0) with
  | none => return {}
  | some trie =>
    let (values, _) ← evalNode trie
    return ({} : MatchResult α).push (score := 0) values

/-- Find values that match `e` in `d`.
`unify == true` if metavarables in `e` can be assigned. -/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) := do
  let (key, keys) ← encodeExpr' e d.config
  withReducible do runTreeM d do
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key matches .star _ then
      if unify then
        return {} -- we don't want to evaluate the whole tree, as this is too expensive.
      else
        matchTreeRootStar d.root
    else
      let result ← matchTreeRootStar d.root
      let todo := matchKey key d.root pMatch #[]
      getMatchLoop todo result unify
