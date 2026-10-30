/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Basic
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
* `InfiniteBinaryTree.TreeAut`: prefix-preserving permutations of the vertices (rooted
  automorphisms). This is a group under composition. The name `TreeAut` avoids a clash with
  `MulAut`, which mathlib abbreviates as `Aut`.
* `InfiniteBinaryTree.TreeAut.phi`: act independently on the two subtrees of the root.
* `InfiniteBinaryTree.TreeAut.activity`: whether the two children of a vertex are swapped.

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
structure TreeAut where
  /-- The underlying permutation of vertices. -/
  toEquiv : InfiniteBinaryTree ≃ InfiniteBinaryTree
  /-- The permutation preserves the prefix relation. -/
  map_isPrefix : ∀ v w, v <+: w ↔ toEquiv v <+: toEquiv w

namespace TreeAut

instance : CoeFun TreeAut fun _ ↦ InfiniteBinaryTree → InfiniteBinaryTree where
  coe f := f.toEquiv

lemma toEquiv_apply (f : TreeAut) (v : InfiniteBinaryTree) : f.toEquiv v = f v := rfl

lemma map_isPrefix_iff (f : TreeAut) {v w : InfiniteBinaryTree} : v <+: w ↔ f v <+: f w :=
  f.map_isPrefix v w

/-- The inverse of a tree automorphism is a tree automorphism. -/
def symm (f : TreeAut) : TreeAut where
  toEquiv := f.toEquiv.symm
  map_isPrefix := fun v w ↦ by
    simpa using (f.map_isPrefix (f.toEquiv.symm v) (f.toEquiv.symm w)).symm

@[simp] lemma symm_apply (f : TreeAut) (v : InfiniteBinaryTree) : f.symm v = f.toEquiv.symm v := rfl

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : TreeAut) : f root = root := by
  have h : f root <+: f (f.toEquiv.symm root) :=
    (f.map_isPrefix_iff).mp (isPrefix_root (f.toEquiv.symm root))
  rw [Equiv.apply_symm_apply] at h
  exact List.prefix_nil.mp (by simpa [root] using h)

lemma length_lt_of_prefix_ne {v w : InfiniteBinaryTree} (h : v <+: w) (hne : v ≠ w) :
    v.length < w.length :=
  Nat.lt_of_le_of_ne h.length_le fun H ↦ hne (h.eq_of_length H)

lemma length_map_take_ge (f : TreeAut) (v : InfiniteBinaryTree) :
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
@[simp] lemma map_length (f : TreeAut) (v : InfiniteBinaryTree) : (f v).length = v.length := by
  refine Nat.le_antisymm ?_ ?_
  · have := f.symm.length_map_take_ge (f v) (f v).length le_rfl
    simpa [List.take_length] using this
  · have := f.length_map_take_ge v v.length le_rfl
    simpa [List.take_length] using this

@[ext] lemma ext {f g : TreeAut} (h : ∀ v, f.toEquiv v = g.toEquiv v) : f = g := by
  cases f
  cases g
  congr
  exact Equiv.ext h

instance : One TreeAut where
  one := ⟨.refl _, fun _ _ ↦ Iff.rfl⟩

instance : Mul TreeAut where
  mul f g := ⟨g.toEquiv.trans f.toEquiv, fun v w ↦
    (g.map_isPrefix v w).trans (f.map_isPrefix (g.toEquiv v) (g.toEquiv w))⟩

instance : Inv TreeAut where
  inv := TreeAut.symm

@[simp] lemma one_apply (v : InfiniteBinaryTree) : (1 : TreeAut) v = v := rfl

@[simp] lemma mul_apply (f g : TreeAut) (v : InfiniteBinaryTree) : (f * g) v = f (g v) := rfl

@[simp] lemma inv_eq_symm (f : TreeAut) : f⁻¹ = f.symm := rfl

instance : Group TreeAut where
  mul_assoc f g h := TreeAut.ext fun _ ↦ rfl
  one_mul f := TreeAut.ext fun _ ↦ rfl
  mul_one f := TreeAut.ext fun _ ↦ rfl
  inv_mul_cancel f := TreeAut.ext fun v ↦ f.toEquiv.symm_apply_apply v

/-- The map underlying `phi`: apply `f₀` on the left subtree and `f₁` on the right subtree. -/
def phiFun (f₀ f₁ : TreeAut) : InfiniteBinaryTree → InfiniteBinaryTree
  | [] => []
  | i :: w => i :: bif i == 0 then f₀ w else f₁ w

lemma phiFun_nil (f₀ f₁ : TreeAut) : phiFun f₀ f₁ [] = [] := rfl

lemma phiFun_cons (f₀ f₁ : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    phiFun f₀ f₁ (i :: w) = i :: bif i == 0 then f₀ w else f₁ w :=
  rfl

lemma fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  have : i.val = 0 ∨ i.val = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ i.2)
  rcases this with h | h <;> simp [Fin.ext_iff, h]

lemma phiFun_left_inv (f₀ f₁ : TreeAut) : (phiFun f₀.symm f₁.symm).LeftInverse (phiFun f₀ f₁) := by
  intro v
  induction v with
  | nil => rfl
  | cons i w ih =>
    rcases fin2_eq_zero_or_one i with hi | hi <;> simp [phiFun_cons, hi, Equiv.symm_apply_apply]

@[simp] lemma symm_symm (f : TreeAut) : f.symm.symm = f :=
  TreeAut.ext fun v ↦ Equiv.symm_symm_apply f.toEquiv v

lemma exists_apply_succ (f : TreeAut) (v : InfiniteBinaryTree) (i : Fin 2) :
    ∃ j, f (v.succ i) = (f v).succ j := by
  have hpref : f v <+: f (v.succ i) := (f.map_isPrefix_iff).mp (List.prefix_append ..)
  obtain ⟨t, ht⟩ := hpref
  have hlen : t.length = 1 := by
    have := congrArg List.length ht
    simp [f.map_length, succ] at this
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨j, ht.symm⟩

/-- `activity f v` is `0` if `f` does not swap the children of `v`, and `1` if it does. -/
noncomputable def activity (f : TreeAut) (v : InfiniteBinaryTree) : Fin 2 :=
  (exists_apply_succ f v 0).choose

lemma apply_succ_zero (f : TreeAut) (v : InfiniteBinaryTree) :
    f (v.succ 0) = (f v).succ (activity f v) :=
  (exists_apply_succ f v 0).choose_spec

/-- Combine two tree automorphisms by acting independently on the two subtrees of the root. -/
def phi (f₀ f₁ : TreeAut) : TreeAut where
  toEquiv :=
    { toFun := phiFun f₀ f₁
      invFun := phiFun f₀.symm f₁.symm
      left_inv := phiFun_left_inv f₀ f₁
      right_inv := fun v ↦ by
        simpa [symm_symm] using phiFun_left_inv f₀.symm f₁.symm v }
  map_isPrefix := by
    intro v w
    induction v generalizing w with
    | nil => simp [phiFun, List.nil_prefix]
    | cons i a ih =>
      cases w with
      | nil => simp [phiFun]
      | cons j b =>
        change i :: a <+: j :: b ↔ phiFun f₀ f₁ (i :: a) <+: phiFun f₀ f₁ (j :: b)
        rcases fin2_eq_zero_or_one i with hi | hi <;> rcases fin2_eq_zero_or_one j with hj | hj
        · simp only [hi, hj, phiFun, List.cons_prefix_cons, true_and]
          exact f₀.map_isPrefix a b
        · simp [hi, hj, phiFun, List.cons_prefix_cons]
        · simp [hi, hj, phiFun, List.cons_prefix_cons]
        · simp only [hi, hj, phiFun, List.cons_prefix_cons, true_and]
          exact f₁.map_isPrefix a b

@[simp] lemma phi_root (f₀ f₁ : TreeAut) : phi f₀ f₁ root = root := by
  simp [root, phi, phiFun]

@[simp] lemma phi_cons (f₀ f₁ : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    phi f₀ f₁ (i :: w) = i :: bif i == 0 then f₀ w else f₁ w := by
  simp [phi, phiFun]

end TreeAut

end InfiniteBinaryTree
