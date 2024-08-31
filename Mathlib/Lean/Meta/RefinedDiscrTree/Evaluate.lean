/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Encode

/-!
# Evaluating brnaches of a RefinedDiscrTree

`RefinedDiscrTree` is lazy, so we always first need to evaluate branches that we use.

We define the `TreeM` monad for doing computations that affect the `RefinedDiscrTree`, and
we define the function `evalNode` which evaluates a node of the `RefinedDiscrTree`.

We also define `dropKey`, which deletes the values at a specified index of the `RefinedDiscrTree`.
To do this, it first needs to evaluate this branch.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α β : Type}

/-- Monad for working with a `RefinedDiscrTree`. -/
abbrev TreeM α := ReaderT WhnfCoreConfig (StateRefT (Array (Trie α)) MetaM)

/-- Run a `TreeM` computation using a `RefinedDiscrTree`. -/
def runTreeM (d : RefinedDiscrTree α) (m : TreeM α β) :
    MetaM (β × RefinedDiscrTree α) := do
  let { config, tries, root } := d
  let (result, tries) ← withReducible <| (m.run config).run tries
  pure (result, { config, tries, root })

private def setTrie (i : TrieIndex) (v : Trie α) : TreeM α Unit :=
  modify (·.set! i v)

/-- Create a new trie with the given lazy entry. -/
private def newTrie (e : LazyEntry α) : TreeM α TrieIndex := do
  modifyGet fun a => let sz := a.size; (sz, a.push (.node #[] {} {} #[e]))

/-- Add a lazy entry to an existing trie. -/
private def addLazyEntryToTrie (i : TrieIndex) (e : LazyEntry α) : TreeM α Unit :=
  modify (·.modify i fun | .node vs star cs p => .node vs star cs (p.push e))

/-- Evaluate the `Trie α` at index `trie`,
replacing it with the evaluated value,
and returning the new `values`, `stars` and `children`. -/
def evalNode (trie : TrieIndex) :
    TreeM α (Array α × HashMap Nat TrieIndex × HashMap Key TrieIndex) := do
  let .node values stars children pending := (← get).get! trie
  if pending.size == 0 then
    return (values, stars, children)
  setTrie trie default
  let mut values := values
  let mut stars := stars
  let mut children := children
  for entry in pending do
    match ← evalLazyEntry entry (← read) with
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

  setTrie trie <| .node values stars children #[]
  return (values, stars, children)


private def dropKeyAux (next : Option TrieIndex) (rest : List Key) :
    TreeM α Unit := do
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
This drops a specific key from the `RefinedDiscrTree` so that
all the entries matching that key exactly are removed.
-/
def dropKey (t : RefinedDiscrTree α) (path : List RefinedDiscrTree.Key) :
    MetaM (RefinedDiscrTree α) :=
  match path with
  | [] => pure t
  | rootKey :: rest => do
    Prod.snd <$> runTreeM t (dropKeyAux (t.root.find? rootKey) rest)

/-- This drops a list of specific keys from the `RefinedDiscrTree` so that
all the entries matching those keys exactly are removed. -/
def dropKeys (t : RefinedDiscrTree α) (keys : List (List RefinedDiscrTree.Key)) :
    MetaM (RefinedDiscrTree α) := do
  keys.foldlM (init := t) (·.dropKey ·)
