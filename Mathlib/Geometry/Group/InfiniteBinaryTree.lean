/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Geometry.Group.InfiniteRegularTree

/-!
# The infinite rooted binary tree

The infinite rooted binary tree is the regular rooted tree of degree `2`: vertices are finite words
on the alphabet `Fin 2`.

This is the special case `α = Fin 2` of the infinite regular rooted tree (vertices `List α`), and
is the tree on which the Grigorchuk group acts. We also keep the classical binary-tree packaging
used by Grigorchuk (`phi`, `activity`, and the `(TreeAut × TreeAut) ⋊ ℤ/2` decomposition).

## Main definitions

* `InfiniteBinaryTree`: abbreviation for `List (Fin 2)`.
* `InfiniteBinaryTree.TreeAut`: abbreviation for `InfiniteRegularTree.TreeAut (Fin 2)`.
* `InfiniteBinaryTree.TreeAut.phi`: act independently on the two subtrees of the root.
* `InfiniteBinaryTree.TreeAut.activity`: whether the two children of a vertex are swapped.
* `InfiniteBinaryTree.TreeAut.equivSemidirect`: `TreeAut ≃* (TreeAut × TreeAut) ⋊ ℤ/2`.

## Tags

infinite binary tree, rooted tree, geometric group theory
-/

@[expose] public section

/-- The infinite rooted binary tree: the regular tree on the alphabet `Fin 2`. -/
abbrev InfiniteBinaryTree := List (Fin 2)

namespace InfiniteBinaryTree

/-- The root of the infinite binary tree. -/
abbrev root : InfiniteBinaryTree := []

/-- The child of `v` obtained by appending the letter `i`. -/
abbrev succ (v : InfiniteBinaryTree) (i : Fin 2) : InfiniteBinaryTree :=
  v ++ [i]

/-- The left child of `v` (append `0`). -/
abbrev left (v : InfiniteBinaryTree) : InfiniteBinaryTree := v.succ 0

/-- The right child of `v` (append `1`). -/
abbrev right (v : InfiniteBinaryTree) : InfiniteBinaryTree := v.succ 1

@[simp] lemma root_eq_nil : root = [] := rfl

@[simp] lemma succ_eq_append (v : InfiniteBinaryTree) (i : Fin 2) : v.succ i = v ++ [i] := rfl

@[simp] lemma left_eq (v : InfiniteBinaryTree) : v.left = v ++ [0] := rfl

@[simp] lemma right_eq (v : InfiniteBinaryTree) : v.right = v ++ [1] := rfl

/-- A rooted automorphism of the infinite binary tree. -/
abbrev TreeAut := InfiniteRegularTree.TreeAut (Fin 2)

namespace TreeAut

open InfiniteRegularTree.TreeAut

export InfiniteRegularTree.TreeAut
  (map_isPrefix_iff map_root map_length inv_eq_symm restrict_apply
    apply_singleton_rootPerm apply_cons_rootPerm combine_cons ofRootPerm_cons)

lemma fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  have : i.val = 0 ∨ i.val = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ i.2)
  rcases this with h | h <;> simp [Fin.ext_iff, h]

lemma ext {f g : TreeAut} (h : ∀ v, f v = g v) : f = g :=
  RelIso.ext h

/-- Combine sections by acting independently on the two subtrees of the root. -/
abbrev combine : (Fin 2 → TreeAut) → TreeAut :=
  InfiniteRegularTree.TreeAut.combine (α := Fin 2)

/-- The rooted automorphism induced by a permutation of the children of the root. -/
abbrev ofRootPerm : Equiv.Perm (Fin 2) → TreeAut :=
  InfiniteRegularTree.TreeAut.ofRootPerm (α := Fin 2)

/-- The permutation of the children of the root induced by `f`. -/
noncomputable abbrev rootPerm : TreeAut → Equiv.Perm (Fin 2) :=
  InfiniteRegularTree.TreeAut.rootPerm (α := Fin 2)

/-- The section of `f` at the first-level vertex `i`. -/
abbrev restrict : TreeAut → Fin 2 → TreeAut :=
  InfiniteRegularTree.TreeAut.restrict (α := Fin 2)

/-- Convenience: combine the two sections as a pair. -/
def combine₂ (f₀ f₁ : TreeAut) : TreeAut :=
  combine fun i ↦ if i = 0 then f₀ else f₁

/-- Combine two tree automorphisms by acting independently on the two subtrees of the root. -/
abbrev phi (f₀ f₁ : TreeAut) : TreeAut :=
  combine₂ f₀ f₁

@[simp] lemma phi_cons (f₀ f₁ : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    phi f₀ f₁ (i :: w) = i :: bif i == 0 then f₀ w else f₁ w := by
  simp only [phi, combine₂, combine_cons]
  rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi]

/-- The transposition of the two children of the root. -/
def swapRoot : TreeAut :=
  ofRootPerm (Equiv.swap (0 : Fin 2) 1)

@[simp] lemma swapRoot_root : swapRoot [] = [] := rfl

@[simp] lemma swapRoot_cons (i : Fin 2) (w : InfiniteBinaryTree) :
    swapRoot (i :: w) = (i + 1) :: w := by
  simp only [swapRoot, ofRootPerm_cons]
  rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi]

@[simp] lemma swapRoot_mul_self : swapRoot * swapRoot = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w =>
      have : (1 + 1 : Fin 2) = 0 := rfl
      simp [RelIso.mul_apply, swapRoot_cons, add_assoc, this]

lemma swapRoot_inv : swapRoot⁻¹ = swapRoot :=
  inv_eq_of_mul_eq_one_right swapRoot_mul_self

@[simp] lemma one_apply (v : InfiniteBinaryTree) : (1 : TreeAut) v = v :=
  RelIso.one_apply v

@[simp] lemma mul_apply (f g : TreeAut) (v : InfiniteBinaryTree) : (f * g) v = f (g v) :=
  RelIso.mul_apply f g v

@[simp] lemma symm_apply (f : TreeAut) (v : InfiniteBinaryTree) :
    f.symm v = (f : InfiniteBinaryTree ≃ InfiniteBinaryTree).symm v :=
  rfl

lemma exists_apply_succ (f : TreeAut) (v : InfiniteBinaryTree) (i : Fin 2) :
    ∃ j, f (succ v i) = succ (f v) j := by
  have hpref : f v <+: f (succ v i) := (map_isPrefix_iff f).mpr (List.prefix_append ..)
  obtain ⟨t, ht⟩ := hpref
  have hlen : t.length = 1 := by
    have := congrArg List.length ht
    simp [map_length, succ] at this
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨j, ht.symm⟩

/-- `activity f v` is `0` if `f` does not swap the children of `v`, and `1` if it does. -/
noncomputable def activity (f : TreeAut) (v : InfiniteBinaryTree) : Fin 2 :=
  (exists_apply_succ f v 0).choose

lemma apply_succ_zero (f : TreeAut) (v : InfiniteBinaryTree) :
    f (succ v 0) = succ (f v) (activity f v) :=
  (exists_apply_succ f v 0).choose_spec
lemma apply_cons_ne_nil (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    f (i :: w) ≠ [] :=
  InfiniteRegularTree.TreeAut.apply_cons_ne_nil f i w

/-- The first letter of `f [i]`. This is the image of the child `i` of the root. -/
noncomputable def firstLetter (f : TreeAut) (i : Fin 2) : Fin 2 :=
  (f [i]).head (apply_cons_ne_nil f i [])

lemma apply_singleton (f : TreeAut) (i : Fin 2) : f [i] = [firstLetter f i] := by
  simp [firstLetter, apply_singleton_rootPerm]

lemma apply_cons (f : TreeAut) (i : Fin 2) (w : InfiniteBinaryTree) :
    f (i :: w) = firstLetter f i :: restrict f i w := by
  have h := apply_cons_rootPerm f i w
  simpa [firstLetter, rootPerm] using h

lemma firstLetter_zero (f : TreeAut) : firstLetter f 0 = activity f root := by
  have h := apply_succ_zero f root
  rw [map_root f] at h
  simp only [root, List.nil_append] at h
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1
lemma firstLetter_one (f : TreeAut) : firstLetter f 1 = activity f root + 1 := by
  have hne : firstLetter f 0 ≠ firstLetter f 1 := by
    intro hf
    have : ([0] : InfiniteBinaryTree) = [1] :=
      f.injective (by rw [apply_singleton, apply_singleton, hf])
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
      rcases fin2_eq_zero_or_one i with hi | hi <;> simp [hi, RelIso.mul_apply]

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
      simp only [RelIso.mul_apply]
      rfl
    | cons i w =>
      have : (1 + 1 : Fin 2) = 0 := rfl
      rcases fin2_eq_zero_or_one i with hi | hi <;>
        simp [hi, this, RelIso.mul_apply, phi_cons, swapRoot_cons]

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
    rw [RelIso.mul_apply, swapRoot_cons, phi_cons]
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
    simp [RelIso.mul_apply, phi_cons, swapRoot_cons]

lemma restrict_phi_mul_swapRoot_one (f₀ f₁ : TreeAut) :
    restrict (phi f₀ f₁ * swapRoot) 1 = f₀ :=
  TreeAut.ext fun w ↦ by
    change ((phi f₀ f₁ * swapRoot) (1 :: w)).tail = f₀ w
    simp [RelIso.mul_apply, phi_cons, swapRoot_cons]

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
        rw [swapRootHom_ofAdd_one, RelIso.mul_apply, swapRoot_cons, phi_cons, hf]
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
