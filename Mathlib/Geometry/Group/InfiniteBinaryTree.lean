/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.List.Basic

/-!
# The infinite rooted binary tree

The infinite rooted binary tree has a vertex for every finite word on the alphabet `{0, 1}`.
The root is the empty word. The two children of a vertex `v` are the words `v ++ [0]` and
`v ++ [1]`.

This is the tree on which the Grigorchuk group acts; automorphisms will be introduced later.

## Main definitions

* `InfiniteBinaryTree`: vertices are lists `List (Fin 2)`.
* `InfiniteBinaryTree.root`: the empty word.
* `InfiniteBinaryTree.succ`: the child of a vertex obtained by appending a letter.

## Tags

infinite binary tree, rooted tree, geometric group theory
-/

@[expose] public section

/-- The infinite rooted binary tree: vertices are finite words on `{0, 1}`. -/
abbrev InfiniteBinaryTree := List (Fin 2)

namespace InfiniteBinaryTree

/-- The root of the infinite binary tree. -/
def root : InfiniteBinaryTree := []

/-- The child of `v` obtained by appending the letter `i`. -/
def succ (v : InfiniteBinaryTree) (i : Fin 2) : InfiniteBinaryTree := v ++ [i]

/-- The left child of `v` (append `0`). -/
def left (v : InfiniteBinaryTree) : InfiniteBinaryTree := v.succ 0

/-- The right child of `v` (append `1`). -/
def right (v : InfiniteBinaryTree) : InfiniteBinaryTree := v.succ 1

@[simp] lemma root_eq_nil : root = [] := rfl

@[simp] lemma succ_eq_append (v : InfiniteBinaryTree) (i : Fin 2) : v.succ i = v ++ [i] := rfl

@[simp] lemma left_eq (v : InfiniteBinaryTree) : v.left = v ++ [0] := rfl

@[simp] lemma right_eq (v : InfiniteBinaryTree) : v.right = v ++ [1] := rfl

@[simp] lemma length_root : root.length = 0 := rfl

@[simp] lemma length_succ (v : InfiniteBinaryTree) (i : Fin 2) : (v.succ i).length = v.length + 1 :=
  by simp [succ]

lemma isPrefix_root (v : InfiniteBinaryTree) : root <+: v :=
  List.nil_prefix

end InfiniteBinaryTree
