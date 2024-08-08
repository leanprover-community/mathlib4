/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean.Meta.DiscrTree
import Batteries.Data.List.Basic
import Mathlib.Lean.Meta.RefinedDiscrTree.Lookup

/-!
A discrimination tree for the purpose of unifying local expressions with library results.

This data structure is based on `Lean.Meta.DiscrTree`, and includes many more features.
Comparing performance with `Lean.Meta.DiscrTree`, this version is a bit slower.
However in practice this does not matter, because a lookup in a discrimination tree is always
combined with `isDefEq` unification and these unifications are significantly more expensive,
so the extra lookup cost is neglegible, while better discrimination tree indexing, and thus
less potential matches can save a significant amount of computation.

## New features

- The keys `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  matching under lambda and forall binders. `Key.lam` has arity 1 and indexes the body.
  `Key.forall` has arity 2 and indexes the domain and the body. The reason for not indexing the
  domain of a lambda expression is that it is usually already determined, for example in
  `∃ a : α, p`, which is `@Exists α fun a : α => p`, we don't want to index the domain `α` twice.
  In a forall expression it is necessary to index the domain, because in an implication `p → q`
  we need to index both `p` and `q`. `Key.bvar` works the same as `Key.fvar`, but stores the
  De Bruijn index to identify it.

  For example, this allows for more specific matching with the left hand side of
  `∑ i in range n, i = n * (n - 1) / 2`, which is indexed by
  `[⟨Finset.sum, 5⟩, ⟨Nat, 0⟩, ⟨Nat, 0⟩, *0, ⟨Finset.Range, 1⟩, *1, λ, ⟨#0, 0⟩]`.

- The key `Key.star` takes a `Nat` identifier as an argument. For example,
  the library pattern `?a + ?a` is encoded as `[⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *2]`.
  `*0` corresponds to the type of `a`, `*1` to the `HAdd` instance, and `*2` to `a`.
  This means that it will only match an expression `x + y` if `x` is definitionally equal to `y`.
  The matching algorithm requires that the same stars from the discrimination tree match with
  the same patterns in the lookup expression, and similarly requires that the same metavariables
  form the lookup expression match with the same pattern in the discrimination tree.

- The key `Key.opaque` has been introduced in order to index existential variables
  in lemmas like `Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n`,
  where the part `Prime p` gets the pattern `[⟨Nat.Prime, 1⟩, ◾]`. (◾ represents `Key.opaque`)
  When matching, `Key.opaque` can only be matched by `Key.star`.

  Using the `WhnfCoreConfig` argument, it is possible to disable β-reduction and ζ-reduction.
  As a result, we may get a lambda expression applied to an argument or a let-expression.
  Since there is no support for indexing these, they will be indexed by `Key.opaque`.

- We evaluate the matching score of a unification.
  This score represents the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 2,
  since the pattern of commutativity is [⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨HAdd.hAdd, 6⟩` gives 1 point,
  and matching `*0` after its first appearence gives another point, but the third argument is an
  outParam, so this gets ignored. Similarly, matching it with `add_assoc` gives a score of 5.

- Patterns that have the potential to be η-reduced are put into the `RefinedDiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, and one of `x₁, .., xₙ` is `x`.
  For example, the pattern `Continuous fun y => Real.exp (f y)])` is indexed by
  both `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, λ, ⟨Real.exp⟩, *3]`
  and  `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, ⟨Real.exp⟩]`
  so that it also comes up if you search with `Continuous Real.exp`.
  Similarly, `Continuous fun x => f x + g x` is indexed by
  both `[⟨Continuous, 1⟩, λ, ⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3]`
  and  `[⟨Continuous, 1⟩, ⟨HAdd.hAdd, 5⟩, *0, *0, *0, *1, *2]`.

- For sub-expressions not at the root of the original expression we have some additional reductions:
  - Any combination of `ofNat`, `Nat.zero`, `Nat.succ` and number literals
    is stored as just a number literal.
  - The expression `fun a : α => a` is stored as `@id α`.
    - This makes lemmas such as `continuous_id'` redundant, which is the same as `continuous_id`,
      with `id` replaced by `fun x => x`.
  - Lambdas in front of number literals are removed. This is because usually `n : α → β` is
    defined to be `fun _ : α => n` for a number literal `n`. So instead of `[λ, n]` we store `[n]`.
  - Any expression with head constant `+`, `*`, `-`, `/`, `⁻¹`, `+ᵥ`, `•` or `^` is normalized to
    not have a lambda in front and to always have the default amount of arguments.
    e.g. `(f + g) a` is stored as `f a + g a` and `fun x => f x + g x` is stored as `f + g`.
    - This makes lemmas such as `MeasureTheory.integral_integral_add'` redundant, which is the
      same as `MeasureTheory.integral_integral_add`, with `f a + g a` replaced by `(f + g) a`
    - it also means that a lemma like `Continuous.mul` can be stated as talking about `f * g`
      instead of `fun x => f x * g x`.
    - When trying to find `Continuous.add` with the expression `Continuous fun x => 1 + x`,
      this is possible, because we first revert the eta-reduction that happens by default,
      and then distribute the lambda. Thus this is indexed as `Continuous (1 + id)`,
      which matches with `Continuous (f + g)` from `Continuous.add`.

## Lazt computation

We encode an `Expr` as an `Array Key`. This is implemented with a lazy computation:
we start with a `LazyEntry α`, which comes with a step function of type
`LazyEntry α → MetaM (Array (Key × LazyEntry α) ⊕ α)`.


## TODO

- The unification algorithm could be made more elaborate.
  For example, when looking up the expression `?a + ?a` (for rewriting), there will be
  results like `n + n = 2 * n` or `a + b = b + a`, but not `n + 1 = n.succ`,
  even though this would still unify.

- The reason why implicit arguments are not ignored by the discrimination tree is that they provide
  important type information. Because of this it seems more natural to index the types of
  expressions instead of indexing the implicit type arguments. Then each key would additionally
  index the type of that expression. So instead of indexing `?a + ?b` as
  `[⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3]`, it would be indexed by something like
  `[(*0, ⟨HAdd.hAdd, 6⟩), _, _, _, _, (*0, *1), (*0, *2)]`.
  The advantage of this would be that there will be less duplicate indexing of types,
  because many functions index the types of their arguments and their return type
  with implicit arguments, meaning that types unnecessarily get indexed multiple times.
  This modification can be explored, but it could very well not be an improvement.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α : Type}

#exit

/-! ### Inserting intro a RefinedDiscrTree -/

/-- If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertInArray [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set ⟨i,h⟩ v
      else
        loop (i+1)
    else
      vs.push v
termination_by vs.size - i

/-- Insert the value `v` at index `keys[i:] : Array Key` in a `Trie`.
For efficiency, we don't compute `keys[i:]`. -/
partial def insertInTrie [BEq α] (keys : Array Key) (i : Nat) (v : α) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (·.1 < ·.1)
        (fun (k', s) => (k', insertInTrie keys (i+1) v s))
        (fun _ => (k, Trie.singleton keys[i+1:] v))
        (k, default)
      .node c
  | .values vs =>
      .values (insertInArray vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      let k1 := keys[i+n]!
      let k2 := ks[n]!
      if k1 != k2 then
        let shared := ks[:n]
        let rest := ks[n+1:]
        return .mkPath shared (.mkNode2 k1 (.singleton keys[i+n+1:] v) k2 (.mkPath rest c))
    return .path ks (insertInTrie keys (i + ks.size) v c)

/-- Insert the value `v` at index `keys : Array Key` in a `RefinedDiscrTree`.

Warning: to account for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertInRefinedDiscrTree [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) :
    RefinedDiscrTree α :=
  let k := keys[0]!
  match d.root.find? k with
  | none =>
    let c := .singleton keys[1:] v
    { root := d.root.insert k c }
  | some c =>
    let c := insertInTrie keys 1 v c
    { root := d.root.insert k c }

/-- Insert the value `v` at index `e : DTExpr` in a `RefinedDiscrTree`.

Warning: to account for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertKeys [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) : RefinedDiscrTree α :=
  insertInRefinedDiscrTree d keys v

/-- Insert the value `v` at index `e : Expr` in a `RefinedDiscrTree`.
The argument `fvarInContext` allows you to specify which free variables in `e` will still be
in the context when the `RefinedDiscrTree` is being used for lookup.
It should return true only if the `RefinedDiscrTree` is built and used locally.

if `onlySpecific := true`, then we filter out the patterns `*` and `Eq * * *`. -/
def insert [BEq α] (d : RefinedDiscrTree α) (e : Expr) (v : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keys ← mkKeys e config onlySpecific fvarInContext
  return keys.foldl (insertKeys · · v) d

/-- Return `true` if `s` and `t` are equal up to changing the `MVarId`s. -/
private def isPerm (t s : Expr) : Bool := match t, s with
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _   => isPerm d₁ d₂ && isPerm b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _       => isPerm d₁ d₂ && isPerm b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂         => d₁ == d₂ && isPerm e₁ e₂
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _   => isPerm t₁ t₂ && isPerm v₁ v₂ && isPerm b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂           => isPerm f₁ f₂ && isPerm a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂       => n₁ == n₂ && i₁ == i₂ && isPerm e₁ e₂
    | .mvar _           , .mvar _              => true
    | t                 , s                    => t == s


/-- Insert the value `vlhs` at index `lhs`, and if `rhs` is indexed differently, then also
insert the value `vrhs` at index `rhs`. -/
def insertEqn [BEq α] (d : RefinedDiscrTree α) (lhs rhs : Expr) (vlhs vrhs : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keysLhs ← mkKeys lhs config onlySpecific fvarInContext
  let d := keysLhs.foldl (insertKeys · · vlhs) d
  if isPerm lhs rhs then
    return d
  else
    let keysRhs ← mkKeys rhs config onlySpecific fvarInContext
    return keysRhs.foldl (insertKeys · · vrhs) d



/-!
### Matching with a RefinedDiscrTree

We use a very simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` and in the target, we store the assignment, and when it is assigned again,
we check that it is the same assignment.
-/

namespace GetUnify

/-- If `k` is a key in `children`, return the corresponding `Trie α`. Otherwise return `none`. -/
def findKey (children : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> children.binSearch (k, default) (·.1 < ·.1)

private structure Context where
  unify  : Bool
  config : WhnfCoreConfig

private structure State where
  /-- Score representing how good the match is. -/
  score : Nat := 0
  /-- Metavariable assignments for the `Key.star` patterns in the `RefinedDiscrTree`. -/
  treeAssignments : HashMap Nat (Array Key) := {}
  /-- Metavariable assignments for the `Expr.mvar` in the expression. -/
  queryAssignments : HashMap Nat (Array Key) := {}


private abbrev M := ReaderT Context $ StateListM State

/-- Return all values from `x` in an array, together with their scores. -/
private def M.run (unify : Bool) (config : WhnfCoreConfig) (x : M (Trie α)) :
    Array (Array α × Nat) :=
  ((x.run { unify, config }).run {}).toArray.map (fun (t, s) => (t.values!, s.score))

/-- Increment the score by `n`. -/
private def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }

/-- Log a metavariable assignment in the `State`, assuming it isn't assigned yet -/
private def assignTreeStar (n : Nat) (keys : Array Key) : M Unit :=
  modify fun s => { s with treeAssignments := s.treeAssignments.insert n keys }

/-- Log a metavariable assignment in the `State`. -/
private def assignQueryStar (id : Nat) (keys : Array Key) : M Unit := do
  let { queryAssignments, .. } ← get
  match queryAssignments.find? id with
  | some keys' => guard (keys == keys')
  | none =>
    modify fun s => { s with queryAssignments := s.queryAssignments.insert id keys }

/-- Return the possible `Trie α` that match with `n` metavariables. -/
partial def skipEntries (t : Trie α) (skipped : Array Key) : Nat → M (Array Key × Trie α)
  | 0      => pure (skipped, t)
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x =>
      (skipEntries c (skipped.push k) (skip + k.arity)) <|> x

/-- Return the possible `Trie α` that match with anything.
We add 1 to the matching score when the key is `.opaque`,
since this pattern is "harder" to match with. -/
def matchTargetStar (id : Nat) (t : Trie α) : M (Trie α) := do
  let (dropped, t) ← t.children!.foldr (init := failure) fun (k, c) x => (do
    if k == .opaque then
      incrementScore 1
    skipEntries c #[k] k.arity
    ) <|> x
  assignQueryStar id dropped
  return t

private partial def dropKeys (keys : List Key) : Array Key × List Key := Id.run do
  let key :: keys := keys | panic! "too few keys"
  key.arity.fold (init := (#[key], keys)) fun _ (pre, keys) =>
    let (dropped, keys) := dropKeys keys;
    (pre ++ dropped, keys)

/-- Return the possible `Trie α` that come from a `Key.star`,
while keeping track of the `Key.star` assignments. -/
def matchTreeStars (keys : List Key) (t : Trie α) : M (List Key × Trie α) := do
  let { treeAssignments, .. } ← get
  Id.run do
  let mut result := failure
  let mut getPrefixResult := none
  /- The `Key.star` are at the start of the `t.children!`,
  so this loops through all of them. -/
  for (k, c) in t.children! do
    let .star i := k | break
    let (dropped, keys') := getPrefixResult.getD <| dropKeys keys
    getPrefixResult := (dropped, keys')
    if let some assignment := treeAssignments.find? i then
      if dropped == assignment then
        result := (incrementScore dropped.size *> pure (keys', c)) <|> result
    else
      result := (assignTreeStar i dropped *> pure (keys', c)) <|> result
  result

mutual
  /-- Return the possible `Trie α` that match with `keys`. -/
  partial def matchExpr (keys : List Key) (t : Trie α) : M (List Key × Trie α) := do
    let key :: keys' := keys | panic! "too few keys"
    if let .star id := key then
      if (← read).unify then
        (keys', ·) <$> matchTargetStar id t
      else
        matchTreeStars keys t
    else
      matchTreeStars keys t <|> exactMatch keys (findKey t.children!)

  /-- Assuming that `keys` is not a metavariable, return the possible `Trie α` that
    exactly match with `keys`. -/
  @[specialize]
  partial def exactMatch (keys : List Key) (find? : Key → Option (Trie α)) :
      M (List Key × Trie α) := do
    let key :: keys := keys | panic! "too few keys"
    let some trie := find? key | failure
    match key with
      | .opaque => failure
      | .lam => pure ()
      | _ => incrementScore 1
    key.arity.foldM (init := (keys, trie)) fun _ (keys, trie) => matchExpr keys trie
end

private partial def getMatchWithScoreAux (d : RefinedDiscrTree α) (keys : Array Key) (unify : Bool)
    (config : WhnfCoreConfig) (allowRootStar : Bool := false) : Array (Array α × Nat) := (do
  if keys == #[Key.star 0] then
    guard allowRootStar
    d.root.foldl (init := failure) fun x k c => (do
      if k == Key.opaque then
        GetUnify.incrementScore 1
      let (_, t) ← GetUnify.skipEntries c #[k] k.arity
      return t) <|> x
  else
    (Prod.snd <$> GetUnify.exactMatch keys.toList d.root.find?)
    <|> do
    guard allowRootStar
    let some c := d.root.find? (.star 0) | failure
    return c
  ).run unify config

end GetUnify


#exit
/--
Return the results from the `RefinedDiscrTree` that match the given expression,
together with their matching scores, in decreasing order of score.

Each entry of type `Array α × Nat` corresponds to one pattern.

If `unify := false`, then unassigned metavariables in `e` are treated as opaque variables.
This is for when you don't want to instantiate metavariables in `e`.

If `allowRootStar := false`, then we don't allow `e` or the matched key in `d`
to be a star pattern. -/
def getMatchWithScore (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) : MetaM (Array (Array α × Nat)) := do
  let e ← mkKey e config
  let result := GetUnify.getMatchWithScoreAux d e unify config allowRootStar
  return result.qsort (·.2 > ·.2)

/-- Same as `getMatchWithScore`, but doesn't return the score. -/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) : MetaM (Array (Array α)) :=
  Array.map (·.1) <$> getMatchWithScore d e unify config allowRootStar

/-- Similar to `getMatchWithScore`, but also returns matches with prefixes of `e`.
We store the score, followed by the number of ignored arguments. -/
partial def getMatchWithScoreWithExtra (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) :
    MetaM (Array (Array α × Nat × Nat)) := do
  let result ← go e 0
  return result.qsort (·.2.1 > ·.2.1)
where
  /-- Auxiliary function for `getMatchWithScoreWithExtra` -/
  go (e : Expr) (numIgnored : Nat) : MetaM (Array (Array α × Nat × Nat)) := do
  let result ← getMatchWithScore d e unify config allowRootStar
  let result := result.map fun (a, b) => (a, b, numIgnored)
  match e with
  | .app e _ => return (← go e (numIgnored + 1)) ++ result
  | _ => return result


variable {β : Type} {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `RefinedDiscrTree`. -/
partial def Trie.mapArraysM (t : RefinedDiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (Trie β) := do
  match t with
  | .node children =>
    return .node (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))
  | .values vs =>
    return .values (← f vs)
  | .path ks c =>
    return .path ks (← c.mapArraysM f)

/-- Apply a monadic function to the array of values at each node in a `RefinedDiscrTree`. -/
def mapArraysM (d : RefinedDiscrTree α) (f : Array α → m (Array β)) : m (RefinedDiscrTree β) :=
  return { root := ← d.root.mapM (·.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `RefinedDiscrTree`. -/
def mapArrays (d : RefinedDiscrTree α) (f : Array α → Array β) : RefinedDiscrTree β :=
  d.mapArraysM (m := Id) f
