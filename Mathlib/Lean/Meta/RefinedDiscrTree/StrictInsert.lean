/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Lean.Meta.RefinedDiscrTree.Basic

/-!
# Support for using `RefinedDiscrTree` as a Strict data structure

You can use `RefinedDiscrTree` as a strict data structure if there is a relatively small
amount of insertion, and large amount of lookup.

This file defines strict insertion of a precomputed `Array Key`.

-/

namespace Lean.Meta.RefinedDiscrTree

variable {α : Type}

private def createLoop (i : Nat) (keys : Array Key) (v : α)
    (tries : Array (Trie α)) : Array (Trie α) :=
  if h : i < keys.size then
    let key := keys[i]
    let nextTrieIdx := tries.size + 1
    if let .star id := key then
      let tries := tries.push (.node #[] (Std.HashMap.empty.insert id nextTrieIdx) {} #[])
      createLoop (i+1) keys v tries
    else
      let tries := tries.push (.node #[] {} (Std.HashMap.empty.insert key nextTrieIdx) #[])
      createLoop (i+1) keys v tries
  else
    tries.push (.node #[v] {} {} #[])

private def insertLoop (i : Nat) (keys : Array Key) (v : α)
    (trieIdx : TrieIndex) (tries : Array (Trie α)) : Array (Trie α) :=
  if h : i < keys.size then
    let key := keys[i]
    let trie := tries[trieIdx]!
    if let .star id := key then
      match trie.stars[id]? with
      | some trieIdx => insertLoop (i+1) keys v trieIdx tries
      | none =>
        let tries := tries.set! trieIdx default -- use `trie` linearly
        let tries := tries.set! trieIdx { trie with stars := trie.stars.insert id tries.size }
        createLoop (i+1) keys v tries
    else
      match trie.children[key]? with
      | some trieIdx => insertLoop (i+1) keys v trieIdx tries
      | none =>
        let tries := tries.set! trieIdx default -- use `trie` linearly
        let tries := tries.set! trieIdx { trie with children := trie.children.insert key tries.size}
        createLoop (i+1) keys v tries
  else
    tries.modify trieIdx fun (.node values s c p) => .node (values.push v) s c p

/-- Insert `keys`, `v` into `tree` in a strict way. -/
def insert (keys : Array Key) (v : α) (tree : RefinedDiscrTree α) : RefinedDiscrTree α :=
  let key := keys[0]!
  let { root, tries, .. } := tree
  match root[key]? with
  | some trieIdx => { tree with tries := insertLoop 1 keys v trieIdx tries }
  | none =>
    let trieIdx := tries.size
    { tree with root := root.insert key trieIdx, tries := createLoop 1 keys v tries }

end Lean.Meta.RefinedDiscrTree
