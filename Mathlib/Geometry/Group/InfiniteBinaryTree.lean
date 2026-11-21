/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Geometry.Group.InfiniteRegularTree

/-!
# The infinite rooted binary tree

The infinite rooted binary tree is the regular rooted tree of degree `2`: vertices are finite words
on the alphabet `Fin 2`.

This is the special case `n = 2` of `InfiniteRegularTree`, and is the tree on which the Grigorchuk
group acts.

## Main definitions

* `InfiniteBinaryTree`: abbreviation for `InfiniteRegularTree 2`.
* `InfiniteBinaryTree.TreeAut`: abbreviation for `InfiniteRegularTree.TreeAut 2`.
* The root decomposition
  `TreeAut ≃* (Fin 2 → TreeAut) ⋊ Equiv.Perm (Fin 2)`
  is `InfiniteRegularTree.TreeAut.equivSemidirect` at `n = 2`.

## Tags

infinite binary tree, rooted tree, geometric group theory
-/

@[expose] public section

/-- The infinite rooted binary tree: the regular tree of degree `2`. -/
abbrev InfiniteBinaryTree := InfiniteRegularTree 2

namespace InfiniteBinaryTree

/-- The root of the infinite binary tree. -/
abbrev root : InfiniteBinaryTree := InfiniteRegularTree.root

/-- The child of `v` obtained by appending the letter `i`. -/
abbrev succ (v : InfiniteBinaryTree) (i : Fin 2) : InfiniteBinaryTree :=
  InfiniteRegularTree.succ v i

/-- The prefix relation on vertices. -/
abbrev prefixRel : InfiniteBinaryTree → InfiniteBinaryTree → Prop :=
  InfiniteRegularTree.prefixRel 2

/-- A rooted automorphism of the infinite binary tree. -/
abbrev TreeAut := InfiniteRegularTree.TreeAut 2

namespace TreeAut

/-- Combine sections by acting independently on the two subtrees of the root. -/
abbrev combine : (Fin 2 → TreeAut) → TreeAut :=
  InfiniteRegularTree.TreeAut.combine

/-- The rooted automorphism induced by a permutation of the children of the root. -/
abbrev ofRootPerm : Equiv.Perm (Fin 2) → TreeAut :=
  InfiniteRegularTree.TreeAut.ofRootPerm

/-- The permutation of the children of the root induced by `f`. -/
noncomputable abbrev rootPerm : TreeAut → Equiv.Perm (Fin 2) :=
  InfiniteRegularTree.TreeAut.rootPerm

/-- The section of `f` at the first-level vertex `i`. -/
abbrev restrict : TreeAut → Fin 2 → TreeAut :=
  InfiniteRegularTree.TreeAut.restrict

/-- The action of `Equiv.Perm (Fin 2)` on pairs of sections. -/
abbrev permAction : Equiv.Perm (Fin 2) →* MulAut (Fin 2 → TreeAut) :=
  InfiniteRegularTree.TreeAut.permAction

/-- Root decomposition:
`TreeAut ≃* (Fin 2 → TreeAut) ⋊ Equiv.Perm (Fin 2)`. -/
noncomputable abbrev equivSemidirect :
    TreeAut ≃* (Fin 2 → TreeAut) ⋊[permAction] Equiv.Perm (Fin 2) :=
  InfiniteRegularTree.TreeAut.equivSemidirect

/-- Convenience: combine the two sections as a pair. -/
def combine₂ (f₀ f₁ : TreeAut) : TreeAut :=
  combine fun i ↦ if i = 0 then f₀ else f₁

/-- The transposition of the two children of the root. -/
def swapRoot : TreeAut :=
  ofRootPerm (Equiv.swap (0 : Fin 2) 1)

end TreeAut

end InfiniteBinaryTree
