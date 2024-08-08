import Mathlib.Lean.Meta.RefinedDiscrTree.Encode

namespace Lean.Meta.RefinedDiscrTree

variable {α : Type} {β : Type}

private structure Context where
  unify  : Bool
  config : WhnfCoreConfig

/- Monad for finding matches while resolving deferred patterns. -/
@[reducible]
private def MatchM α := ReaderT Context (StateRefT (Array (Trie α)) MetaM)

private def runMatch (d : RefinedDiscrTree α) (unify : Bool) (m : MatchM α β) :
    MetaM (β × RefinedDiscrTree α) := do
  let { config, tries, root } := d
  let (result, tries) ← withReducible <| (m.run { unify, config }).run tries
  pure (result, { config, tries, root })

private def setTrie (i : TrieIndex) (v : Trie α) : MatchM α Unit :=
  modify (·.set! i v)

/-- Create a new trie with the given lazy entry. -/
private def newTrie (e : LazyEntry α) : MatchM α TrieIndex := do
  modifyGet fun a => let sz := a.size; (sz, a.push (.node #[] {} {} #[e]))

/-- Add a lazy entry to an existing trie. -/
private def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry α) : MatchM α Unit :=
  modify (·.modify i fun | .node vs star cs p => .node vs star cs (p.push e))

/--
This evaluates all lazy entries in a trie and updates `values`, `stars`, and `children`
accordingly.
-/
private partial def evalLazyEntries
    (values : Array α) (stars : HashMap Nat TrieIndex) (children : HashMap Key TrieIndex)
    (entries : Array (LazyEntry α)) :
    MatchM α (Array α × HashMap Nat TrieIndex × HashMap Key TrieIndex) := do
  let mut values := values
  let mut stars := stars
  let mut children := children
  for entry in entries do
    match ← evalLazyEntry entry (← read).config with
    | .inr v => values := values.push v
    | .inl xs =>
      for (key, entry) in xs do
        if let .star id := key then
           match stars.find? id with
          | none     => stars := stars.insert id (← newTrie entry)
          | some idx => addLazyEntryToTrie idx entry
        else
          match children.find? key with
          | none     => children := children.insert key (← newTrie entry)
          | some idx => addLazyEntryToTrie idx entry
  return (values, stars, children)

private def evalNode (c : TrieIndex) :
    MatchM α (Array α × HashMap Nat TrieIndex × HashMap Key TrieIndex) := do
  let .node vs stars cs pending := (← get).get! c
  if pending.size = 0 then
    pure (vs, stars, cs)
  else
    setTrie c default
    let (vs, stars, cs) ← evalLazyEntries vs stars cs pending
    setTrie c <| .node vs stars cs #[]
    pure (vs, stars, cs)

def dropKeyAux (next : Option TrieIndex) (rest : List Key) :
    MatchM α Unit := do
  let some next := next | return
  let (_, stars, children) ← evalNode next
  match rest with
  | [] =>
    setTrie next { values := #[], stars, children, pending := #[] }
  | key :: rest =>
    if let .star id := key then
      dropKeyAux (stars.find? id) rest
    else
      dropKeyAux (children.find? key) rest

/--
This drops a specific key from the lazy discrimination tree so that
all the entries matching that key exactly are removed.
-/
def dropKey (t : RefinedDiscrTree α) (path : List RefinedDiscrTree.Key) :
    MetaM (RefinedDiscrTree α) :=
  match path with
  | [] => pure t
  | rootKey :: rest => do
    let idx := t.root.find? rootKey
    Prod.snd <$> runMatch t default (dropKeyAux idx rest)

/--
A match result contains the terms formed from matching a term against
patterns in the discrimination tree.
-/
structure MatchResult (α : Type) where
  /--
  The elements in the match result.

  The top-level array represents an array from `score` values to the
  results with that score. A `score` is the number of non-star matches
  in a pattern against the term, and thus bounded by the size of the
  term being matched against. The elements of this array are themselves
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
partial def appendResultsAux (mr : MatchResult α) (a : Array β) (f : Nat → α → β) : Array β :=
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
structure PartialMatch where
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

/-

/--
Evaluate all partial matches and add resulting matches to `MatchResult`.

The partial matches are stored in an array that is used as a stack. When adding
multiple partial matches to explore next, to ensure the order of results matches
user expectations, this code must add paths we want to prioritize and return
results earlier are added last.
-/
private partial def getMatchLoop (cases : Array PartialMatch) (result : MatchResult α) : MatchM α (MatchResult α) := do
  if cases.isEmpty then
    pure result
  else do
    let ca := cases.back
    let cases := cases.pop
    let (vs, star, cs) ← evalNode ca.c
    if ca.todo.isEmpty then
      let result := result.push ca.score vs
      getMatchLoop cases result
    else if star == 0 && cs.isEmpty then
      getMatchLoop cases result
    else
      let e     := ca.todo.back
      let todo  := ca.todo.pop
      /- We must always visit `Key.star` edges since they are wildcards.
          Thus, `todo` is not used linearly when there is `Key.star` edge
          and there is an edge for `k` and `k != Key.star`. -/
      let pushStar (cases : Array PartialMatch) :=
        if star = 0 then
          cases
        else
          cases.push { todo, score := ca.score, c := star }
      let pushNonStar (k : Key) (args : Array Expr) (cases : Array PartialMatch) :=
        match cs.find? k with
        | none   => cases
        | some c => cases.push { todo := todo ++ args, score := ca.score + 1, c }
      let cases := pushStar cases
      let (k, args) ← MatchClone.getMatchKeyArgs e (root := false) (← read)
      let cases :=
        match k with
        | .star  => cases
        /-
          Note: dep-arrow vs arrow
          Recall that dependent arrows are `(Key.other, #[])`, and non-dependent arrows are
          `(Key.arrow, #[a, b])`.
          A non-dependent arrow may be an instance of a dependent arrow (stored at `DiscrTree`).
          Thus, we also visit the `Key.other` child.
        -/
        | .arrow =>
          cases |> pushNonStar .other #[]
                |> pushNonStar k args
        | _      =>
          cases |> pushNonStar k args
      getMatchLoop cases result

private def getStarResult (root : Lean.HashMap Key TrieIndex) : MatchM α (MatchResult α) :=
  match root.find? .star with
  | none =>
    pure <| {}
  | some idx => do
    let (vs, _) ← evalNode idx
    pure <| ({} : MatchResult α).push (score := 1) vs

/-
Add partial match to cases if discriminator tree root map has potential matches.
-/
private def pushRootCase (r : Lean.HashMap Key TrieIndex) (k : Key) (args : Array Expr)
    (cases : Array PartialMatch) : Array PartialMatch :=
  match r.find? k with
  | none => cases
  | some c => cases.push { todo := args, score := 1, c }

/--
  Find values that match `e` in `root`.
-/
private def getMatchCore (root : Lean.HashMap Key TrieIndex) (e : Expr) :
    MatchM α (MatchResult α) := do
  let result ← getStarResult root
  let (k, args) ← MatchClone.getMatchKeyArgs e (root := true) (← read)
  let cases :=
    match k with
    | .star  =>
      #[]
    /- See note about "dep-arrow vs arrow" at `getMatchLoop` -/
    | .arrow =>
      #[] |> pushRootCase root .other #[]
          |> pushRootCase root k args
    | _ =>
      #[] |> pushRootCase root k args
  getMatchLoop cases result

/--
  Find values that match `e` in `d`.

  The results are ordered so that the longest matches in terms of number of
  non-star keys are first with ties going to earlier operators first.
-/
def getMatch (d : RefinedDiscrTree α) (e : Expr) : MetaM (MatchResult α × RefinedDiscrTree α) :=
  withReducible <| runMatch d <| getMatchCore d.roots e
-/


/-!
### Matching with a RefinedDiscrTree

We use a very simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` and in the target, we store the assignment, and when it is assigned again,
we check that it is the same assignment.
-/

namespace GetUnify


/-- Add to the stack all matches that result from a `.star id` in the query expression. -/
partial def matchQueryStar (id : Nat) (trie : TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) (skip : Nat := 1) (skipped : List Key := []) :
    MatchM α (Array PartialMatch) := do
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
partial def matchTreeStars (key : Key) (stars : HashMap Nat TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if stars.isEmpty then
    todo
  else
    let (dropped, keys) := dropKeys [key] pMatch.keys
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
  dropKeys (dropped rest : List Key) (n : Nat := 1) : (List Key × List Key) := Id.run do
    match n with
    | 0 => (dropped, rest)
    | n+1 =>
      let key :: rest := rest | panic! "too few keys"
      dropKeys (key :: dropped) rest (n + key.arity)

/-- Add to the stack the match with `key`. -/
def matchKey (key : Key) (children : HashMap Key TrieIndex) (pMatch : PartialMatch)
    (todo : Array PartialMatch) : Array PartialMatch :=
  if let .opaque := key then todo else
  match children.find? key with
  | none      => todo
  | some trie => todo.push { pMatch with trie, score := pMatch.score + 1 }

/-- Return the possible `Trie α` that match with `keys`. -/
partial def getMatchLoop (todo : Array PartialMatch) (result : MatchResult α) : MatchM α (MatchResult α) := do
  if todo.isEmpty then
    return result
  else
    let pMatch := todo.back
    let todo := todo.pop
    let (values, stars, children) ← evalNode pMatch.trie
    match pMatch.keys with
    | [] =>
      getMatchLoop todo (result.push (score := pMatch.score) values)
    | key :: keys =>
      let pMatch := { pMatch with keys }
      if let .star id := key then
        if (← read).unify then
          let todo ← matchQueryStar id pMatch.trie pMatch todo
          getMatchLoop todo result
        else
          let todo := matchTreeStars key stars pMatch todo
          getMatchLoop todo result
      else
        let todo := matchTreeStars key stars pMatch todo
        let todo := matchKey key children pMatch todo
        getMatchLoop todo result

/-- Return a matchResult, containing the results from the pattern `[.star 0]`. -/
def matchTreeRootStar (root : HashMap Key TrieIndex) : MatchM α (MatchResult α):= do
  match root.find? (.star 0) with
  | none => return {}
  | some trie =>
    let (values, _) ← evalNode trie
    return ({} : MatchResult α).push (score := 0) values

/-- Find values that match `e` in `d`. -/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify : Bool) :
    MetaM (MatchResult α × RefinedDiscrTree α) :=
  withReducible <| runMatch d unify do
    let key :: keys ← encodeExpr' e (← read).config | panic! "RefinedDiscrTree: Empty list of keys"
    let pMatch : PartialMatch := { keys, score := 0, trie := default }
    if key matches .star _ then
      if (← read).unify then
        return {} -- we don't want to evaluate the whole tree, as this is too expensive.
      else
        matchTreeRootStar d.root
    else
      let result ← matchTreeRootStar d.root
      let todo := matchKey key d.root pMatch #[]
      getMatchLoop todo result

end GetUnify
