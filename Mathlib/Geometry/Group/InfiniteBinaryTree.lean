/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.List.Infix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SemidirectProduct
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
* `InfiniteBinaryTree.TreeAut.equivSemidirect`: `TreeAut ≃* (TreeAut × TreeAut) ⋊ ℤ/2`.

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

lemma length_succ (v : InfiniteBinaryTree) (i : Fin 2) : (v.succ i).length = v.length + 1 :=
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

lemma map_isPrefix_iff (f : TreeAut) {v w : InfiniteBinaryTree} : v <+: w ↔ f v <+: f w :=
  f.map_isPrefix v w

/-- The inverse of a tree automorphism is a tree automorphism. -/
def symm (f : TreeAut) : TreeAut where
  toEquiv := f.toEquiv.symm
  map_isPrefix := fun v w ↦ by
    simpa using (f.map_isPrefix (f.toEquiv.symm v) (f.toEquiv.symm w)).symm

@[simp] lemma symm_apply (f : TreeAut) (v : InfiniteBinaryTree) : f.symm v = f.toEquiv.symm v := rfl

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : TreeAut) : f [] = [] := by
  have h : f [] <+: f (f.toEquiv.symm []) :=
    (f.map_isPrefix_iff).mp List.nil_prefix
  rw [Equiv.apply_symm_apply] at h
  exact List.prefix_nil.mp h

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

@[simp] lemma phi_cons (f₀ f₁ : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    phi f₀ f₁ (i :: w) = i :: bif i == 0 then f₀ w else f₁ w := by
  simp [phi, phiFun]

/-- The rooted swap of the two children of the root. This generates the `ℤ/2` factor. -/
def swapRoot : TreeAut where
  toEquiv :=
    { toFun := fun
        | [] => []
        | i :: w => (i + 1) :: w
      invFun := fun
        | [] => []
        | i :: w => (i + 1) :: w
      left_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w =>
          have : (1 + 1 : Fin 2) = 0 := rfl
          simp [add_assoc, this]
      right_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w =>
          have : (1 + 1 : Fin 2) = 0 := rfl
          simp [add_assoc, this] }
  map_isPrefix := by
    intro v w
    cases v with
    | nil => simp [List.nil_prefix]
    | cons i a =>
      cases w with
      | nil => simp
      | cons j b =>
        simp [List.cons_prefix_cons, add_left_inj]

@[simp] lemma swapRoot_root : swapRoot [] = [] := rfl

@[simp] lemma swapRoot_cons (i : Fin 2) (w : InfiniteBinaryTree) :
    swapRoot (i :: w) = (i + 1) :: w :=
  rfl

@[simp] lemma swapRoot_mul_self : swapRoot * swapRoot = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w =>
      have : (1 + 1 : Fin 2) = 0 := rfl
      simp [add_assoc, this]

lemma swapRoot_inv : swapRoot⁻¹ = swapRoot :=
  inv_eq_of_mul_eq_one_right swapRoot_mul_self

lemma apply_cons_ne_nil (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) : f (i :: w) ≠ [] := by
  intro h
  have := f.map_length (i :: w)
  simp [h] at this

/-- The first letter of `f [i]`. This is the image of the child `i` of the root. -/
def firstLetter (f : TreeAut) (i : Fin 2) : Fin 2 :=
  (f [i]).head (apply_cons_ne_nil f i [])

lemma apply_singleton (f : TreeAut) (i : Fin 2) : f [i] = [firstLetter f i] := by
  have hne := apply_cons_ne_nil f i []
  have htail : (f [i]).tail = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen := f.map_length [i]
    rw [List.length_tail, hlen]
    rfl
  conv_lhs => rw [← List.cons_head_tail hne, htail]
  rfl

/-- Action of `f` on the subtree hanging from the child `i` of the root. -/
def restrictFun (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) : InfiniteBinaryTree :=
  (f (i :: w)).tail

lemma apply_cons (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    f (i :: w) = firstLetter f i :: restrictFun f i w := by
  have hpref : f [i] <+: f (i :: w) := (f.map_isPrefix_iff).mp (by simp [List.cons_prefix_cons])
  rw [apply_singleton] at hpref
  obtain ⟨s, hs⟩ := hpref
  simp [restrictFun, ← hs]

lemma firstLetter_symm (f : TreeAut) (i : Fin 2) :
    firstLetter f.symm (firstLetter f i) = i := by
  have h : f.symm [firstLetter f i] = [i] := by
    rw [← apply_singleton f i]
    exact Equiv.symm_apply_apply f.toEquiv [i]
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

/-- Restriction of `f` to the subtree of the child `i` of the root. -/
def restrict (f : TreeAut) (i : Fin 2) : TreeAut where
  toEquiv :=
    { toFun := restrictFun f i
      invFun := restrictFun f.symm (firstLetter f i)
      left_inv := by
        intro w
        calc
          restrictFun f.symm (firstLetter f i) (restrictFun f i w)
            = (f.symm (firstLetter f i :: restrictFun f i w)).tail := rfl
          _ = (f.symm (f (i :: w))).tail := by rw [← apply_cons f i w]
          _ = w := by simp [Equiv.symm_apply_apply]
      right_inv := by
        intro w
        have h := apply_cons f.symm (firstLetter f i) w
        rw [firstLetter_symm] at h
        calc
          restrictFun f i (restrictFun f.symm (firstLetter f i) w)
            = (f (i :: restrictFun f.symm (firstLetter f i) w)).tail := rfl
          _ = (f (f.symm (firstLetter f i :: w))).tail := by rw [h]
          _ = w := by simp [Equiv.apply_symm_apply] }
  map_isPrefix := by
    intro w w'
    have h := f.map_isPrefix (i :: w) (i :: w')
    simp only [List.cons_prefix_cons, true_and] at h
    rw [apply_cons f i w, apply_cons f i w'] at h
    simpa [List.cons_prefix_cons] using h

@[simp] lemma restrict_apply (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    restrict f i w = (f (i :: w)).tail :=
  rfl

lemma firstLetter_zero (f : TreeAut) : firstLetter f 0 = activity f root := by
  have h := apply_succ_zero f []
  rw [map_root] at h
  simp only [succ_eq_append, List.nil_append] at h
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

lemma firstLetter_one (f : TreeAut) : firstLetter f 1 = activity f root + 1 := by
  have hne : firstLetter f 0 ≠ firstLetter f 1 := by
    intro hf
    have : ([0] : InfiniteBinaryTree) = [1] :=
      f.toEquiv.injective (by rw [apply_singleton, apply_singleton, hf])
    cases this
  rw [firstLetter_zero] at hne
  rcases fin2_eq_zero_or_one (activity f root) with ha | ha <;>
    rcases fin2_eq_zero_or_one (firstLetter f 1) with h1 | h1
  · cases hne (ha.trans h1.symm)
  · simpa [h1, root] using ha
  · have : (1 + 1 : Fin 2) = 0 := rfl
    rw [h1, ha, this]
  · cases hne (ha.trans h1.symm)

lemma firstLetter_eq_add_activity (f : TreeAut) (i : Fin 2) :
    firstLetter f i = i + activity f root := by
  rcases fin2_eq_zero_or_one i with hi | hi
  · simp [hi, firstLetter_zero]
  · rw [hi, firstLetter_one, add_comm]

lemma apply_cons_activity (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    f (i :: w) = (i + activity f root) :: restrict f i w := by
  rw [apply_cons, firstLetter_eq_add_activity]
  rfl

lemma phi_one : phi (1 : TreeAut) 1 = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w =>
      rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi]

lemma phi_mul (f₀ f₁ g₀ g₁ : TreeAut) :
    phi (f₀ * g₀) (f₁ * g₁) = phi f₀ f₁ * phi g₀ g₁ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w =>
      rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi]

/-- Independent action on the two subtrees of the root, as a group homomorphism. -/
def phiHom : TreeAut × TreeAut →* TreeAut where
  toFun p := phi p.1 p.2
  map_one' := phi_one
  map_mul' p q := phi_mul p.1 p.2 q.1 q.2

@[simp] lemma phiHom_apply (f₀ f₁ : TreeAut) : phiHom (f₀, f₁) = phi f₀ f₁ := rfl

lemma swapRoot_mul_phi_mul_swapRoot (f₀ f₁ : TreeAut) :
    swapRoot * phi f₀ f₁ * swapRoot = phi f₁ f₀ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil =>
      simp only [mul_apply]
      rfl
    | cons i w =>
      have : (1 + 1 : Fin 2) = 0 := rfl
      rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi, this, mul_apply, phi_cons]

/-- The automorphism of `TreeAut × TreeAut` that swaps the two factors. -/
def swapComponents : MulAut (TreeAut × TreeAut) := MulEquiv.prodComm

@[simp] lemma swapComponents_apply (p : TreeAut × TreeAut) :
    swapComponents p = (p.2, p.1) :=
  rfl

lemma swapComponents_mul_self : swapComponents * swapComponents = 1 := by
  ext <;> rfl

open Multiplicative (ofAdd toAdd)

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 :=
  fin2_eq_zero_or_one x

/-- The `ℤ/2` action on `TreeAut × TreeAut` that swaps the two factors. -/
def swapHom : Multiplicative (ZMod 2) →* MulAut (TreeAut × TreeAut) where
  toFun x := if x.toAdd = 0 then 1 else swapComponents
  map_one' := rfl
  map_mul' x y := by
    rcases zmod2_eq_zero_or_one x.toAdd with hx | hx <;>
      rcases zmod2_eq_zero_or_one y.toAdd with hy | hy
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
    · have hxy : (x * y).toAdd = 0 := by
        rw [toAdd_mul, hx, hy]
        rfl
      simp [hx, hy, hxy, swapComponents_mul_self]

/-- The embedding of `ℤ/2` into `TreeAut` sending the generator to `swapRoot`. -/
def swapRootHom : Multiplicative (ZMod 2) →* TreeAut where
  toFun x := if x.toAdd = 0 then 1 else swapRoot
  map_one' := rfl
  map_mul' x y := by
    rcases zmod2_eq_zero_or_one x.toAdd with hx | hx <;>
      rcases zmod2_eq_zero_or_one y.toAdd with hy | hy
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
    · have hxy : (x * y).toAdd = 0 := by
        rw [toAdd_mul, hx, hy]
        rfl
      simp [hx, hy, hxy, swapRoot_mul_self]

@[simp] lemma swapHom_ofAdd_zero : swapHom 1 = 1 := rfl

@[simp] lemma swapHom_ofAdd_one : swapHom (ofAdd 1) = swapComponents := rfl

@[simp] lemma swapRootHom_ofAdd_zero : swapRootHom 1 = 1 := rfl

@[simp] lemma swapRootHom_ofAdd_one : swapRootHom (ofAdd 1) = swapRoot := rfl

lemma phiHom_compat (g : Multiplicative (ZMod 2)) :
    phiHom.comp (swapHom g).toMonoidHom =
      (MulAut.conj (swapRootHom g)).toMonoidHom.comp phiHom := by
  refine MonoidHom.ext fun p ↦ TreeAut.ext fun v ↦ ?_
  rcases zmod2_eq_zero_or_one g.toAdd with h | h
  · have hg : g = 1 := by rw [← ofAdd_toAdd g, h]; rfl
    simp [hg]
  · have hg : g = ofAdd 1 := by rw [← ofAdd_toAdd g, h]
    rw [hg]
    change phi p.2 p.1 v = (swapRoot * phi p.1 p.2 * swapRoot⁻¹) v
    rw [swapRoot_inv, swapRoot_mul_phi_mul_swapRoot]

/-- The homomorphism `(TreeAut × TreeAut) ⋊ ℤ/2 →* TreeAut` sending
`⟨(f₀, f₁), ε⟩` to `phi f₀ f₁ * swapRoot^ε`. -/
def ofSemidirect : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) →* TreeAut :=
  SemidirectProduct.lift phiHom swapRootHom phiHom_compat

lemma ofSemidirect_apply (x : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2)) :
    ofSemidirect x = phi x.left.1 x.left.2 * swapRootHom x.right :=
  rfl

lemma activity_phi (f₀ f₁ : TreeAut) : activity (phi f₀ f₁) root = 0 := by
  have h : phi f₀ f₁ [0] = [0] := by
    rw [phi_cons]
    simp only [Fin.isValue, BEq.rfl, cond_eq_ite, reduceIte, List.cons.injEq, true_and]
    exact map_root f₀
  have hfl := apply_singleton (phi f₀ f₁) 0
  rw [hfl] at h
  have := (List.cons_eq_cons.mp h).1
  rw [firstLetter_zero] at this
  exact this

lemma activity_phi_mul_swapRoot (f₀ f₁ : TreeAut) :
    activity (phi f₀ f₁ * swapRoot) root = 1 := by
  have h : (phi f₀ f₁ * swapRoot) [0] = [1] := by
    rw [mul_apply, swapRoot_cons, phi_cons]
    simp only [Fin.isValue, zero_add, Fin.reduceBEq, cond_eq_ite, Bool.false_eq_true, reduceIte,
      List.cons.injEq, true_and]
    exact map_root f₁
  have hfl := apply_singleton (phi f₀ f₁ * swapRoot) 0
  rw [hfl] at h
  have := (List.cons_eq_cons.mp h).1
  rw [firstLetter_zero] at this
  exact this

lemma restrict_phi_zero (f₀ f₁ : TreeAut) : restrict (phi f₀ f₁) 0 = f₀ :=
  TreeAut.ext fun w ↦ by
    change (phi f₀ f₁ (0 :: w)).tail = f₀ w
    simp [phi_cons]

lemma restrict_phi_one (f₀ f₁ : TreeAut) : restrict (phi f₀ f₁) 1 = f₁ :=
  TreeAut.ext fun w ↦ by
    change (phi f₀ f₁ (1 :: w)).tail = f₁ w
    simp [phi_cons]

lemma restrict_phi_mul_swapRoot_zero (f₀ f₁ : TreeAut) :
    restrict (phi f₀ f₁ * swapRoot) 0 = f₁ :=
  TreeAut.ext fun w ↦ by
    change ((phi f₀ f₁ * swapRoot) (0 :: w)).tail = f₁ w
    simp [phi_cons]

lemma restrict_phi_mul_swapRoot_one (f₀ f₁ : TreeAut) :
    restrict (phi f₀ f₁ * swapRoot) 1 = f₀ :=
  TreeAut.ext fun w ↦ by
    change ((phi f₀ f₁ * swapRoot) (1 :: w)).tail = f₀ w
    simp [phi_cons]

/-- The inverse of `ofSemidirect`, recording the two restrictions and the activity at the root. -/
noncomputable def toSemidirect (f : TreeAut) :
    (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) where
  left := (restrict f (activity f root), restrict f (activity f root + 1))
  right := ofAdd (if activity f root = 0 then (0 : ZMod 2) else 1)

lemma ofSemidirect_toSemidirect (f : TreeAut) : ofSemidirect (toSemidirect f) = f :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil =>
      rw [show f [] = [] from map_root f]
      rw [show ofSemidirect (toSemidirect f) [] = [] from map_root _]
    | cons i w =>
      rcases fin2_eq_zero_or_one (activity f root) with ha | ha
      · have hf := apply_cons_activity f i w
        rw [ha, add_zero] at hf
        have hx : toSemidirect f = ⟨(restrict f 0, restrict f 1), 1⟩ := by
          simp only [toSemidirect]
          rw [ha]
          rfl
        rw [hx]
        change (phi (restrict f 0) (restrict f 1) * swapRootHom 1) (i :: w) = f (i :: w)
        rw [map_one, mul_one, phi_cons, hf]
        rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi]
      · have hf := apply_cons_activity f i w
        rw [ha] at hf
        have h11 : (1 + 1 : Fin 2) = 0 := rfl
        have hx : toSemidirect f = ⟨(restrict f 1, restrict f 0), ofAdd 1⟩ := by
          simp only [toSemidirect]
          rw [ha]
          rfl
        rw [hx]
        change (phi (restrict f 1) (restrict f 0) * swapRootHom (ofAdd 1)) (i :: w) = f (i :: w)
        rw [swapRootHom_ofAdd_one, mul_apply, swapRoot_cons, phi_cons, hf]
        rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi, h11]

lemma toSemidirect_ofSemidirect (x : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2)) :
    toSemidirect (ofSemidirect x) = x := by
  rcases x with ⟨⟨f₀, f₁⟩, ε⟩
  rcases zmod2_eq_zero_or_one ε.toAdd with h | h
  · have hε : ε = 1 := by rw [← ofAdd_toAdd ε, h]; rfl
    rw [hε, ofSemidirect_apply]
    change toSemidirect (phi f₀ f₁ * swapRootHom 1) = ⟨(f₀, f₁), 1⟩
    rw [swapRootHom_ofAdd_zero, mul_one]
    refine SemidirectProduct.ext ?_ ?_
    · change (restrict (phi f₀ f₁) (activity (phi f₀ f₁) root),
        restrict (phi f₀ f₁) (activity (phi f₀ f₁) root + 1)) = (f₀, f₁)
      rw [activity_phi, zero_add, restrict_phi_zero, restrict_phi_one]
    · change ofAdd (if activity (phi f₀ f₁) root = 0 then (0 : ZMod 2) else 1) = 1
      rw [activity_phi]
      rfl
  · have hε : ε = ofAdd 1 := by rw [← ofAdd_toAdd ε, h]
    rw [hε, ofSemidirect_apply, swapRootHom_ofAdd_one]
    refine SemidirectProduct.ext ?_ ?_
    · change (restrict (phi f₀ f₁ * swapRoot) (activity (phi f₀ f₁ * swapRoot) root),
        restrict (phi f₀ f₁ * swapRoot) (activity (phi f₀ f₁ * swapRoot) root + 1)) = (f₀, f₁)
      have h11 : (1 + 1 : Fin 2) = 0 := rfl
      rw [activity_phi_mul_swapRoot, h11, restrict_phi_mul_swapRoot_one,
        restrict_phi_mul_swapRoot_zero]
    · change ofAdd (if activity (phi f₀ f₁ * swapRoot) root = 0 then (0 : ZMod 2) else 1) = ofAdd 1
      rw [activity_phi_mul_swapRoot]
      rfl

/-- Every rooted automorphism of the infinite binary tree is uniquely `phi f₀ f₁` or
`phi f₀ f₁ * swapRoot`. Equivalently,
`TreeAut ≃* (TreeAut × TreeAut) ⋊ ℤ/2`. -/
noncomputable def equivSemidirect :
    TreeAut ≃* (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective ofSemidirect
    ⟨Function.LeftInverse.injective toSemidirect_ofSemidirect,
      Function.LeftInverse.surjective ofSemidirect_toSemidirect⟩).symm

end TreeAut

end InfiniteBinaryTree
