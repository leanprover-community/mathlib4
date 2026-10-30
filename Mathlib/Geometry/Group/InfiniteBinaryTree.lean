/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Logic.Equiv.Basic

/-!
# The infinite rooted binary tree

The infinite rooted binary tree has a vertex for every finite word on the alphabet `{0, 1}`.
The root is the empty word. The two children of a vertex `v` are the words `v ++ [0]` and
`v ++ [1]`.

This is the tree on which the Grigorchuk group acts.

## Main definitions

* `InfiniteBinaryTree`: vertices are lists `List (Fin 2)`.
* `InfiniteBinaryTree.root`: the empty word.
* `InfiniteBinaryTree.succ`: the child of a vertex obtained by appending a letter.
* `InfiniteBinaryTree.Aut`: prefix-preserving permutations of the vertices (rooted automorphisms).

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

/-- A rooted automorphism of the infinite binary tree is a permutation of the vertices that
preserves the prefix order (equivalently: a graph automorphism fixing the root). -/
structure Aut where
  /-- The underlying permutation of vertices. -/
  toEquiv : InfiniteBinaryTree ≃ InfiniteBinaryTree
  /-- The permutation preserves the prefix relation. -/
  map_isPrefix : ∀ v w, v <+: w ↔ toEquiv v <+: toEquiv w

namespace Aut

instance : CoeFun Aut fun _ ↦ InfiniteBinaryTree → InfiniteBinaryTree where
  coe f := f.toEquiv

lemma toEquiv_apply (f : Aut) (v : InfiniteBinaryTree) : f.toEquiv v = f v := rfl

lemma map_isPrefix_iff (f : Aut) {v w : InfiniteBinaryTree} : v <+: w ↔ f v <+: f w :=
  f.map_isPrefix v w

/-- The inverse of a tree automorphism is a tree automorphism. -/
def symm (f : Aut) : Aut where
  toEquiv := f.toEquiv.symm
  map_isPrefix := fun v w ↦ by
    simpa using (f.map_isPrefix (f.toEquiv.symm v) (f.toEquiv.symm w)).symm

@[simp] lemma symm_apply (f : Aut) (v : InfiniteBinaryTree) : f.symm v = f.toEquiv.symm v := rfl

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : Aut) : f root = root := by
  have h : f root <+: f (f.toEquiv.symm root) :=
    (f.map_isPrefix_iff).mp (isPrefix_root (f.toEquiv.symm root))
  rw [Equiv.apply_symm_apply] at h
  exact List.prefix_nil.mp (by simpa [root] using h)

lemma length_lt_of_prefix_ne {v w : InfiniteBinaryTree} (h : v <+: w) (hne : v ≠ w) :
    v.length < w.length :=
  Nat.lt_of_le_of_ne h.length_le fun H ↦ hne (h.eq_of_length H)

lemma length_map_take_ge (f : Aut) (v : InfiniteBinaryTree) :
    ∀ k ≤ v.length, k ≤ (f (v.take k)).length
  | 0, _ => Nat.zero_le _
  | k + 1, hk => by
    have hpref : v.take k <+: v.take (k + 1) := List.take_prefix_take_left (Nat.le_succ k)
    have hne : v.take k ≠ v.take (k + 1) := by
      intro h
      have := congrArg List.length h
      have hk' : k + 1 ≤ v.length := hk
      simp [Nat.min_eq_left (Nat.le_of_succ_le hk'), Nat.min_eq_left hk'] at this
    have hlt := length_lt_of_prefix_ne (f.map_isPrefix_iff.mp hpref) (f.toEquiv.injective.ne hne)
    have ih := f.length_map_take_ge v k (Nat.le_of_succ_le hk)
    omega

/-- A tree automorphism preserves word length (the distance to the root). -/
@[simp] lemma map_length (f : Aut) (v : InfiniteBinaryTree) : (f v).length = v.length := by
  refine Nat.le_antisymm ?_ ?_
  · have := f.symm.length_map_take_ge (f v) (f v).length le_rfl
    simpa [List.take_length] using this
  · have := f.length_map_take_ge v v.length le_rfl
    simpa [List.take_length] using this

@[ext] lemma ext {f g : Aut} (h : ∀ v, f.toEquiv v = g.toEquiv v) : f = g := by
  cases f
  cases g
  congr
  exact Equiv.ext h

end Aut

end InfiniteBinaryTree
