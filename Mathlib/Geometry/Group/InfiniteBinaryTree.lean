/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Data.List.Infix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The infinite rooted binary tree

The infinite rooted binary tree has a vertex for every finite word on the alphabet `{false, true}`.
The root is the empty word. The two children of a vertex `v` are the words `v ++ [false]` and
`v ++ [true]`.

This is the tree on which the Grigorchuk group acts.

## Main definitions

* `InfiniteBinaryTree`: vertices are lists `List Bool`.
* `InfiniteBinaryTree.root`: the empty word.
* `InfiniteBinaryTree.succ`: the child of a vertex obtained by appending a letter.
* `InfiniteBinaryTree.TreeAut`: order isomorphisms of the prefix partial order on vertices
  (rooted automorphisms), as `RelIso` of the prefix relation. This is a group under composition.
  The name `TreeAut` avoids a clash with `MulAut`, which mathlib abbreviates as `Aut`.
* `InfiniteBinaryTree.TreeAut.combine`: act independently on the two subtrees of the root
  (Grigorchuk's φ).
* `InfiniteBinaryTree.TreeAut.activity`: whether the two children of a vertex are swapped.
* `InfiniteBinaryTree.TreeAut.equivSemidirect`: `TreeAut ≃* (TreeAut × TreeAut) ⋊ ℤ/2`.

## Tags

infinite binary tree, rooted tree, geometric group theory
-/

@[expose] public section

/-- The infinite rooted binary tree: vertices are finite words on `{false, true}`. -/
abbrev InfiniteBinaryTree := List Bool

namespace InfiniteBinaryTree

/-- The root of the infinite binary tree. -/
def root : InfiniteBinaryTree := []

/-- The child of `v` obtained by appending the letter `i`. -/
def succ (v : InfiniteBinaryTree) (i : Bool) : InfiniteBinaryTree := v ++ [i]

@[simp] lemma root_eq_nil : root = [] := rfl

@[simp] lemma succ_eq_append (v : InfiniteBinaryTree) (i : Bool) : v.succ i = v ++ [i] := rfl

@[simp] lemma length_root : root.length = 0 := rfl

lemma length_succ (v : InfiniteBinaryTree) (i : Bool) : (v.succ i).length = v.length + 1 :=
  by simp [succ]

lemma isPrefix_root (v : InfiniteBinaryTree) : root <+: v :=
  List.nil_prefix

/-- The prefix relation is a partial order on the vertices of the infinite binary tree. -/
instance : IsPartialOrder InfiniteBinaryTree (· <+: ·) := inferInstance

/-- The prefix relation on vertices. -/
@[reducible] def prefixRel : InfiniteBinaryTree → InfiniteBinaryTree → Prop := (· <+: ·)

/-- A rooted automorphism of the infinite binary tree is an order isomorphism of the prefix
partial order (equivalently: a graph automorphism fixing the root). -/
abbrev TreeAut := RelIso prefixRel prefixRel

namespace TreeAut

lemma map_isPrefix_iff (f : TreeAut) {v w : InfiniteBinaryTree} : v <+: w ↔ f v <+: f w :=
  (f.map_rel_iff).symm

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : TreeAut) : f [] = [] := by
  have h : f [] <+: f (f.symm []) := f.map_isPrefix_iff.mp List.nil_prefix
  rw [RelIso.apply_symm_apply] at h
  exact List.prefix_nil.mp h

@[ext] lemma ext {f g : TreeAut} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

@[simp] lemma inv_eq_symm (f : TreeAut) : f⁻¹ = f.symm := rfl

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
    have hlt := length_lt_of_prefix_ne (f.map_isPrefix_iff.mp hpref) (f.injective.ne hne)
    have ih := length_map_take_ge f v k (Nat.le_of_succ_le hk)
    omega

/-- A tree automorphism preserves word length (the distance to the root). -/
@[simp] lemma map_length (f : TreeAut) (v : InfiniteBinaryTree) : (f v).length = v.length := by
  refine Nat.le_antisymm ?_ ?_
  · have := length_map_take_ge f.symm (f v) (f v).length le_rfl
    simpa [List.take_length] using this
  · have := length_map_take_ge f v v.length le_rfl
    simpa [List.take_length] using this

/-- The map underlying `combine`: apply `f₀` on the `false`-subtree and `f₁` on the `true`-subtree.
-/
def combineFun (f₀ f₁ : TreeAut) : InfiniteBinaryTree → InfiniteBinaryTree
  | [] => []
  | i :: w => i :: bif i then f₁ w else f₀ w

lemma combineFun_nil (f₀ f₁ : TreeAut) : combineFun f₀ f₁ [] = [] := rfl

lemma combineFun_cons (f₀ f₁ : TreeAut) (i : Bool) (w : InfiniteBinaryTree) :
    combineFun f₀ f₁ (i :: w) = i :: bif i then f₁ w else f₀ w :=
  rfl

lemma combineFun_left_inv (f₀ f₁ : TreeAut) :
    (combineFun f₀.symm f₁.symm).LeftInverse (combineFun f₀ f₁) := by
  intro v
  induction v with
  | nil => rfl
  | cons i w ih =>
    cases i <;> simp [combineFun_cons, RelIso.symm_apply_apply]

lemma exists_apply_succ (f : TreeAut) (v : InfiniteBinaryTree) (i : Bool) :
    ∃ j, f (v.succ i) = (f v).succ j := by
  have hpref : f v <+: f (v.succ i) := (f.map_isPrefix_iff).mp (List.prefix_append ..)
  obtain ⟨t, ht⟩ := hpref
  have hlen : t.length = 1 := by
    have := congrArg List.length ht
    simp [f.map_length, succ] at this
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  exact ⟨j, ht.symm⟩

/-- `activity f v` is `false` if `f` does not swap the children of `v`, and `true` if it does. -/
noncomputable def activity (f : TreeAut) (v : InfiniteBinaryTree) : Bool :=
  (exists_apply_succ f v false).choose

lemma apply_succ_false (f : TreeAut) (v : InfiniteBinaryTree) :
    f (v.succ false) = (f v).succ (activity f v) :=
  (exists_apply_succ f v false).choose_spec

/-- Combine two tree automorphisms by acting independently on the two subtrees of the root.
In the Grigorchuk literature this map is often denoted φ. -/
def combine (f₀ f₁ : TreeAut) : TreeAut where
  toEquiv :=
    { toFun := combineFun f₀ f₁
      invFun := combineFun f₀.symm f₁.symm
      left_inv := combineFun_left_inv f₀ f₁
      right_inv := fun v ↦ by
        simpa [RelIso.symm_symm] using combineFun_left_inv f₀.symm f₁.symm v }
  map_rel_iff' := by
    intro v w
    refine Iff.symm ?_
    induction v generalizing w with
    | nil => simp [combineFun, prefixRel, List.nil_prefix]
    | cons i a ih =>
      cases w with
      | nil => simp [combineFun, prefixRel]
      | cons j b =>
        simp only [prefixRel]
        change i :: a <+: j :: b ↔ combineFun f₀ f₁ (i :: a) <+: combineFun f₀ f₁ (j :: b)
        cases i <;> cases j
        · simp only [combineFun, List.cons_prefix_cons, true_and]
          exact f₀.map_isPrefix_iff
        · simp [combineFun, List.cons_prefix_cons]
        · simp [combineFun, List.cons_prefix_cons]
        · simp only [combineFun, List.cons_prefix_cons, true_and]
          exact f₁.map_isPrefix_iff

@[simp] lemma combine_cons (f₀ f₁ : TreeAut) (i : Bool) (w : InfiniteBinaryTree) :
    combine f₀ f₁ (i :: w) = i :: bif i then f₁ w else f₀ w := by
  simp [combine, combineFun]

/-- The rooted swap of the two children of the root. This generates the `ℤ/2` factor. -/
def swapRoot : TreeAut where
  toEquiv :=
    { toFun := fun
        | [] => []
        | i :: w => (!i) :: w
      invFun := fun
        | [] => []
        | i :: w => (!i) :: w
      left_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w => cases i <;> rfl
      right_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w => cases i <;> rfl }
  map_rel_iff' := by
    intro v w
    refine Iff.symm ?_
    cases v with
    | nil => simp [prefixRel, List.nil_prefix]
    | cons i a =>
      cases w with
      | nil => simp [prefixRel]
      | cons j b =>
        cases i <;> cases j <;> simp [prefixRel, List.cons_prefix_cons]

@[simp] lemma swapRoot_root : swapRoot [] = [] := rfl

@[simp] lemma swapRoot_cons (i : Bool) (w : InfiniteBinaryTree) :
    swapRoot (i :: w) = (!i) :: w :=
  rfl

@[simp] lemma swapRoot_mul_self : swapRoot * swapRoot = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => cases i <;> rfl

lemma swapRoot_inv : swapRoot⁻¹ = swapRoot :=
  inv_eq_of_mul_eq_one_right swapRoot_mul_self

lemma apply_cons_ne_nil (f : TreeAut) (i : Bool) (w : InfiniteBinaryTree) : f (i :: w) ≠ [] := by
  intro h
  have := f.map_length (i :: w)
  simp [h] at this

/-- The first letter of `f [i]`. This is the image of the child `i` of the root. -/
def firstLetter (f : TreeAut) (i : Bool) : Bool :=
  (f [i]).head (apply_cons_ne_nil f i [])

lemma apply_singleton (f : TreeAut) (i : Bool) : f [i] = [firstLetter f i] := by
  have hne := apply_cons_ne_nil f i []
  have htail : (f [i]).tail = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen := f.map_length [i]
    rw [List.length_tail, hlen]
    rfl
  conv_lhs => rw [← List.cons_head_tail hne, htail]
  rfl

/-- Action of `f` on the subtree hanging from the child `i` of the root. -/
def restrictFun (f : TreeAut) (i : Bool) (w : InfiniteBinaryTree) : InfiniteBinaryTree :=
  (f (i :: w)).tail

lemma apply_cons (f : TreeAut) (i : Bool) (w : InfiniteBinaryTree) :
    f (i :: w) = firstLetter f i :: restrictFun f i w := by
  have hpref : f [i] <+: f (i :: w) := (f.map_isPrefix_iff).mp (by simp [List.cons_prefix_cons])
  rw [apply_singleton] at hpref
  obtain ⟨s, hs⟩ := hpref
  simp [restrictFun, ← hs]

lemma firstLetter_symm (f : TreeAut) (i : Bool) :
    firstLetter f.symm (firstLetter f i) = i := by
  have h : f.symm [firstLetter f i] = [i] := by
    rw [← apply_singleton f i]
    exact f.symm_apply_apply [i]
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

/-- Restriction of `f` to the subtree of the child `i` of the root. -/
def restrict (f : TreeAut) (i : Bool) : TreeAut where
  toEquiv :=
    { toFun := restrictFun f i
      invFun := restrictFun f.symm (firstLetter f i)
      left_inv := by
        intro w
        calc
          restrictFun f.symm (firstLetter f i) (restrictFun f i w)
            = (f.symm (firstLetter f i :: restrictFun f i w)).tail := rfl
          _ = (f.symm (f (i :: w))).tail := by rw [← apply_cons f i w]
          _ = w := by simp [RelIso.symm_apply_apply]
      right_inv := by
        intro w
        have h := apply_cons f.symm (firstLetter f i) w
        rw [firstLetter_symm] at h
        calc
          restrictFun f i (restrictFun f.symm (firstLetter f i) w)
            = (f (i :: restrictFun f.symm (firstLetter f i) w)).tail := rfl
          _ = (f (f.symm (firstLetter f i :: w))).tail := by rw [h]
          _ = w := by simp [RelIso.apply_symm_apply] }
  map_rel_iff' := by
    intro w w'
    refine Iff.symm ?_
    have h := f.map_isPrefix_iff (v := i :: w) (w := i :: w')
    simp only [List.cons_prefix_cons, true_and] at h
    rw [apply_cons f i w, apply_cons f i w'] at h
    simpa [prefixRel, List.cons_prefix_cons] using h

@[simp] lemma restrict_apply (f : TreeAut) (i : Bool) (w : InfiniteBinaryTree) :
    restrict f i w = (f (i :: w)).tail :=
  rfl

lemma firstLetter_false (f : TreeAut) : firstLetter f false = activity f root := by
  have h := apply_succ_false f []
  rw [map_root] at h
  simp only [succ_eq_append, List.nil_append] at h
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

lemma firstLetter_true (f : TreeAut) : firstLetter f true = !activity f root := by
  have hne : firstLetter f false ≠ firstLetter f true := by
    intro hf
    have : ([false] : InfiniteBinaryTree) = [true] :=
      f.injective (by rw [apply_singleton, apply_singleton, hf])
    cases this
  rw [firstLetter_false] at hne
  match hact : activity f root, hfl : firstLetter f true with
  | false, false =>
    have : False := hne (by rw [hact, hfl])
    exact this.elim
  | false, true =>
    simp
  | true, false =>
    simp
  | true, true =>
    have : False := hne (by rw [hact, hfl])
    exact this.elim

lemma firstLetter_eq_xor_activity (f : TreeAut) (i : Bool) :
    firstLetter f i = xor i (activity f root) := by
  cases i
  · simp [firstLetter_false]
  · simpa [Bool.xor_true] using firstLetter_true f

lemma apply_cons_activity (f : TreeAut) (i : Bool) (w : InfiniteBinaryTree) :
    f (i :: w) = xor i (activity f root) :: restrict f i w := by
  rw [apply_cons, firstLetter_eq_xor_activity]
  rfl

lemma combine_one : combine (1 : TreeAut) 1 = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => cases i <;> rfl

lemma combine_mul (f₀ f₁ g₀ g₁ : TreeAut) :
    combine (f₀ * g₀) (f₁ * g₁) = combine f₀ f₁ * combine g₀ g₁ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => cases i <;> rfl

/-- Independent action on the two subtrees of the root, as a group homomorphism. -/
def combineHom : TreeAut × TreeAut →* TreeAut where
  toFun p := combine p.1 p.2
  map_one' := combine_one
  map_mul' p q := combine_mul p.1 p.2 q.1 q.2

@[simp] lemma combineHom_apply (f₀ f₁ : TreeAut) : combineHom (f₀, f₁) = combine f₀ f₁ := rfl

lemma swapRoot_mul_combine_mul_swapRoot (f₀ f₁ : TreeAut) :
    swapRoot * combine f₀ f₁ * swapRoot = combine f₁ f₀ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil =>
      simp only [RelIso.mul_apply]
      rfl
    | cons i w =>
      cases i <;> simp [RelIso.mul_apply, combine_cons]

/-- The automorphism of `TreeAut × TreeAut` that swaps the two factors. -/
def swapComponents : MulAut (TreeAut × TreeAut) := MulEquiv.prodComm

@[simp] lemma swapComponents_apply (p : TreeAut × TreeAut) :
    swapComponents p = (p.2, p.1) :=
  rfl

lemma swapComponents_mul_self : swapComponents * swapComponents = 1 := by
  ext <;> rfl

open Multiplicative (ofAdd toAdd)

/-- Convert a Boolean activity bit to an element of `ZMod 2`. -/
def boolToZMod2 (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] lemma boolToZMod2_false : boolToZMod2 false = 0 := rfl
@[simp] lemma boolToZMod2_true : boolToZMod2 true = 1 := rfl

/-- The `ℤ/2` action on `TreeAut × TreeAut` that swaps the two factors. -/
def swapHom : Multiplicative (ZMod 2) →* MulAut (TreeAut × TreeAut) where
  toFun x := if x.toAdd = 0 then 1 else swapComponents
  map_one' := rfl
  map_mul' x y := by
    rcases ZMod.eq_zero_or_one x.toAdd with hx | hx <;>
      rcases ZMod.eq_zero_or_one y.toAdd with hy | hy
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
    rcases ZMod.eq_zero_or_one x.toAdd with hx | hx <;>
      rcases ZMod.eq_zero_or_one y.toAdd with hy | hy
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

lemma combineHom_compat (g : Multiplicative (ZMod 2)) :
    combineHom.comp (swapHom g).toMonoidHom =
      (MulAut.conj (swapRootHom g)).toMonoidHom.comp combineHom := by
  refine MonoidHom.ext fun p ↦ TreeAut.ext fun v ↦ ?_
  rcases ZMod.eq_zero_or_one g.toAdd with h | h
  · have hg : g = 1 := by rw [← ofAdd_toAdd g, h]; rfl
    simp [hg]
  · have hg : g = ofAdd 1 := by rw [← ofAdd_toAdd g, h]
    rw [hg]
    change combine p.2 p.1 v = (swapRoot * combine p.1 p.2 * swapRoot⁻¹) v
    rw [swapRoot_inv, swapRoot_mul_combine_mul_swapRoot]

/-- The homomorphism `(TreeAut × TreeAut) ⋊ ℤ/2 →* TreeAut` sending
`⟨(f₀, f₁), ε⟩` to `combine f₀ f₁ * swapRoot^ε`. -/
def ofSemidirect : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) →* TreeAut :=
  SemidirectProduct.lift combineHom swapRootHom combineHom_compat

lemma ofSemidirect_apply (x : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2)) :
    ofSemidirect x = combine x.left.1 x.left.2 * swapRootHom x.right :=
  rfl

lemma activity_combine (f₀ f₁ : TreeAut) : activity (combine f₀ f₁) root = false := by
  have h : combine f₀ f₁ [false] = [false] := by
    rw [combine_cons]
    simp only [Bool.cond_false, List.cons.injEq, true_and]
    exact map_root f₀
  have hfl := apply_singleton (combine f₀ f₁) false
  rw [hfl] at h
  have := (List.cons_eq_cons.mp h).1
  rw [firstLetter_false] at this
  exact this

lemma activity_combine_mul_swapRoot (f₀ f₁ : TreeAut) :
    activity (combine f₀ f₁ * swapRoot) root = true := by
  have h : (combine f₀ f₁ * swapRoot) [false] = [true] := by
    rw [RelIso.mul_apply, swapRoot_cons, combine_cons]
    simp only [Bool.not_false, Bool.cond_true, List.cons.injEq, true_and]
    exact map_root f₁
  have hfl := apply_singleton (combine f₀ f₁ * swapRoot) false
  rw [hfl] at h
  have := (List.cons_eq_cons.mp h).1
  rw [firstLetter_false] at this
  exact this

lemma restrict_combine_false (f₀ f₁ : TreeAut) : restrict (combine f₀ f₁) false = f₀ :=
  TreeAut.ext fun w ↦ by
    change (combine f₀ f₁ (false :: w)).tail = f₀ w
    simp [combine_cons]

lemma restrict_combine_true (f₀ f₁ : TreeAut) : restrict (combine f₀ f₁) true = f₁ :=
  TreeAut.ext fun w ↦ by
    change (combine f₀ f₁ (true :: w)).tail = f₁ w
    simp [combine_cons]

lemma restrict_combine_mul_swapRoot_false (f₀ f₁ : TreeAut) :
    restrict (combine f₀ f₁ * swapRoot) false = f₁ :=
  TreeAut.ext fun w ↦ by
    change ((combine f₀ f₁ * swapRoot) (false :: w)).tail = f₁ w
    simp [RelIso.mul_apply, combine_cons]

lemma restrict_combine_mul_swapRoot_true (f₀ f₁ : TreeAut) :
    restrict (combine f₀ f₁ * swapRoot) true = f₀ :=
  TreeAut.ext fun w ↦ by
    change ((combine f₀ f₁ * swapRoot) (true :: w)).tail = f₀ w
    simp [RelIso.mul_apply, combine_cons]

/-- The inverse of `ofSemidirect`, recording the two restrictions and the activity at the root. -/
noncomputable def toSemidirect (f : TreeAut) :
    (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) where
  left := (restrict f (activity f root), restrict f (!activity f root))
  right := ofAdd (boolToZMod2 (activity f root))

lemma ofSemidirect_toSemidirect (f : TreeAut) : ofSemidirect (toSemidirect f) = f :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil =>
      rw [show f [] = [] from map_root f]
      rw [show ofSemidirect (toSemidirect f) [] = [] from map_root _]
    | cons i w =>
      cases hact : activity f root
      · have hf := apply_cons_activity f i w
        rw [hact] at hf
        have hx : toSemidirect f = ⟨(restrict f false, restrict f true), 1⟩ := by
          simp only [toSemidirect, hact, boolToZMod2_false]
          rfl
        rw [hx]
        change (combine (restrict f false) (restrict f true) * swapRootHom 1) (i :: w) = f (i :: w)
        rw [map_one, mul_one, combine_cons, hf]
        cases i <;> simp
      · have hf := apply_cons_activity f i w
        rw [hact] at hf
        have hx : toSemidirect f = ⟨(restrict f true, restrict f false), ofAdd 1⟩ := by
          simp only [toSemidirect, hact, boolToZMod2_true, Bool.not_true]
        rw [hx]
        change (combine (restrict f true) (restrict f false) * swapRootHom (ofAdd 1)) (i :: w) =
          f (i :: w)
        rw [swapRootHom_ofAdd_one, RelIso.mul_apply, swapRoot_cons, combine_cons, hf]
        cases i <;> simp

lemma toSemidirect_ofSemidirect (x : (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2)) :
    toSemidirect (ofSemidirect x) = x := by
  rcases x with ⟨⟨f₀, f₁⟩, ε⟩
  rcases ZMod.eq_zero_or_one ε.toAdd with h | h
  · have hε : ε = 1 := by rw [← ofAdd_toAdd ε, h]; rfl
    rw [hε, ofSemidirect_apply]
    change toSemidirect (combine f₀ f₁ * swapRootHom 1) = ⟨(f₀, f₁), 1⟩
    rw [swapRootHom_ofAdd_zero, mul_one]
    refine SemidirectProduct.ext ?_ ?_
    · change (restrict (combine f₀ f₁) (activity (combine f₀ f₁) root),
        restrict (combine f₀ f₁) (!activity (combine f₀ f₁) root)) = (f₀, f₁)
      rw [activity_combine, Bool.not_false, restrict_combine_false, restrict_combine_true]
    · change ofAdd (boolToZMod2 (activity (combine f₀ f₁) root)) = 1
      rw [activity_combine]
      rfl
  · have hε : ε = ofAdd 1 := by rw [← ofAdd_toAdd ε, h]
    rw [hε, ofSemidirect_apply, swapRootHom_ofAdd_one]
    refine SemidirectProduct.ext ?_ ?_
    · change (restrict (combine f₀ f₁ * swapRoot)
          (activity (combine f₀ f₁ * swapRoot) root),
        restrict (combine f₀ f₁ * swapRoot)
          (!activity (combine f₀ f₁ * swapRoot) root)) = (f₀, f₁)
      rw [activity_combine_mul_swapRoot, Bool.not_true, restrict_combine_mul_swapRoot_true,
        restrict_combine_mul_swapRoot_false]
    · change ofAdd (boolToZMod2 (activity (combine f₀ f₁ * swapRoot) root)) = ofAdd 1
      rw [activity_combine_mul_swapRoot]
      rfl

/-- Every rooted automorphism of the infinite binary tree is uniquely `combine f₀ f₁` or
`combine f₀ f₁ * swapRoot`. Equivalently,
`TreeAut ≃* (TreeAut × TreeAut) ⋊ ℤ/2`. -/
noncomputable def equivSemidirect :
    TreeAut ≃* (TreeAut × TreeAut) ⋊[swapHom] Multiplicative (ZMod 2) :=
  (MulEquiv.ofBijective ofSemidirect
    ⟨Function.LeftInverse.injective toSemidirect_ofSemidirect,
      Function.LeftInverse.surjective ofSemidirect_toSemidirect⟩).symm

end TreeAut

end InfiniteBinaryTree
