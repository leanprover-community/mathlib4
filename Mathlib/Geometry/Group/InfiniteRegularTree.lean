/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Infix
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The infinite regular rooted tree

The infinite regular rooted tree on an alphabet `α` has a vertex for every finite word
`List α`. The root is the empty word. The children of a vertex `v` are the words `v ++ [a]` for
`a : α`. When `α` is finite of cardinality `n`, this is the regular rooted tree of degree `n`.

## Main definitions

* `InfiniteRegularTree α`: vertices are lists `List α`.
* `InfiniteRegularTree.TreeAut α`: rooted automorphisms, as order isomorphisms of the prefix
  partial order (`RelIso`). The name `TreeAut` avoids a clash with `MulAut`.
* `InfiniteRegularTree.TreeAut.combine`: act independently on the subtrees of the root.
* `InfiniteRegularTree.TreeAut.ofRootPerm`: the rooted automorphism induced by a permutation of
  the children of the root.
* `InfiniteRegularTree.TreeAut.rootPerm`: the permutation induced at the root.
* `InfiniteRegularTree.TreeAut.restrict`: the section of an automorphism at a first-level vertex.
* `InfiniteRegularTree.TreeAut.equivSemidirect`: the semidirect product isomorphism
  `TreeAut α ≃* (α → TreeAut α) ⋊ Equiv.Perm α`.

## References

* Nekrashevych, *Self-Similar Groups*, AMS Mathematical Surveys and Monographs 117.

## Tags

regular tree, rooted tree, geometric group theory
-/

@[expose] public section

/-- The infinite regular rooted tree on the alphabet `α`: vertices are finite words. -/
abbrev InfiniteRegularTree (α : Type*) := List α

namespace InfiniteRegularTree

variable {α : Type*}

/-- A rooted automorphism of the infinite regular tree is an order isomorphism of the prefix
partial order. -/
abbrev TreeAut (α : Type*) :=
  RelIso (fun x y : List α ↦ x <+: y) (fun x y : List α ↦ x <+: y)

namespace TreeAut

variable {α : Type*}

@[ext] lemma ext {f g : TreeAut α} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

@[simp] lemma map_isPrefix_iff (f : TreeAut α) {v w : InfiniteRegularTree α} :
    f v <+: f w ↔ v <+: w :=
  f.map_rel_iff

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : TreeAut α) : f [] = [] := by
  have h : f [] <+: f (f.symm []) := (map_isPrefix_iff f).mpr List.nil_prefix
  rw [RelIso.apply_symm_apply] at h
  exact List.prefix_nil.mp h

lemma length_map_take_ge (f : TreeAut α) (v : InfiniteRegularTree α) :
    ∀ k ≤ v.length, k ≤ (f (v.take k)).length
  | 0, _ => Nat.zero_le _
  | k + 1, hk => by
    have hpref : v.take k <+: v.take (k + 1) := List.take_prefix_take_left (Nat.le_succ k)
    have hne : v.take k ≠ v.take (k + 1) := by
      intro h
      have := congrArg List.length h
      have hk' : k + 1 ≤ v.length := hk
      simp [Nat.min_eq_left (Nat.le_of_succ_le hk'), Nat.min_eq_left hk'] at this
    have hlt := List.length_lt_of_prefix_ne ((map_isPrefix_iff f).mpr hpref) (f.injective.ne hne)
    have ih := length_map_take_ge f v k (Nat.le_of_succ_le hk)
    omega

/-- A tree automorphism preserves word length (the distance to the root). -/
@[simp] lemma map_length (f : TreeAut α) (v : InfiniteRegularTree α) : (f v).length = v.length := by
  refine Nat.le_antisymm ?_ ?_
  · have := length_map_take_ge f.symm (f v) (f v).length le_rfl
    simpa [List.take_length] using this
  · have := length_map_take_ge f v v.length le_rfl
    simpa [List.take_length] using this

lemma apply_cons_ne_nil (f : TreeAut α) (a : α) (w : InfiniteRegularTree α) :
    f (a :: w) ≠ [] := by
  intro h
  have := f.map_length (a :: w)
  simp [h] at this

/-- The first letter of `f [a]`. This is the image of the child `a` of the root. -/
def firstLetter (f : TreeAut α) (a : α) : α :=
  (f [a]).head (apply_cons_ne_nil f a [])

lemma apply_singleton (f : TreeAut α) (a : α) : f [a] = [firstLetter f a] := by
  have hne := apply_cons_ne_nil f a []
  have htail : (f [a]).tail = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen := f.map_length [a]
    rw [List.length_tail, hlen]
    rfl
  conv_lhs => rw [← List.cons_head_tail hne, htail]
  rfl

lemma firstLetter_injective (f : TreeAut α) : Function.Injective f.firstLetter := by
  intro a b h
  have : ([a] : InfiniteRegularTree α) = [b] :=
    f.injective (by rw [apply_singleton, apply_singleton, h])
  exact List.singleton_inj.mp this

lemma firstLetter_surjective [Finite α] (f : TreeAut α) : Function.Surjective f.firstLetter :=
  Finite.surjective_of_injective f.firstLetter_injective

lemma firstLetter_symm (f : TreeAut α) (a : α) :
    firstLetter f.symm (firstLetter f a) = a := by
  have h : f.symm [firstLetter f a] = [a] := by
    rw [← apply_singleton f a]
    exact f.symm_apply_apply [a]
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

/-- The permutation of the children of the root induced by `f`. -/
def rootPerm (f : TreeAut α) : Equiv.Perm α where
  toFun := firstLetter f
  invFun := firstLetter f.symm
  left_inv := firstLetter_symm f
  right_inv := firstLetter_symm f.symm

@[simp] lemma rootPerm_apply (f : TreeAut α) (a : α) : rootPerm f a = firstLetter f a :=
  rfl

/-- Action of `f` on the subtree hanging from the child `a` of the root. -/
def restrictFun (f : TreeAut α) (a : α) (w : InfiniteRegularTree α) : InfiniteRegularTree α :=
  (f (a :: w)).tail

lemma apply_cons (f : TreeAut α) (a : α) (w : InfiniteRegularTree α) :
    f (a :: w) = firstLetter f a :: restrictFun f a w := by
  have hpref : f [a] <+: f (a :: w) := (map_isPrefix_iff f).mpr (by simp [List.cons_prefix_cons])
  rw [apply_singleton] at hpref
  obtain ⟨s, hs⟩ := hpref
  simp [restrictFun, ← hs]

/-- The section of `f` at the first-level vertex `a`. -/
def restrict (f : TreeAut α) (a : α) : TreeAut α where
  toEquiv :=
    { toFun := restrictFun f a
      invFun := restrictFun f.symm (firstLetter f a)
      left_inv := by
        intro w
        calc
          restrictFun f.symm (firstLetter f a) (restrictFun f a w)
            = (f.symm (firstLetter f a :: restrictFun f a w)).tail := rfl
          _ = (f.symm (f (a :: w))).tail := by rw [← apply_cons f a w]
          _ = w := by simp [RelIso.symm_apply_apply]
      right_inv := by
        intro w
        have h := apply_cons f.symm (firstLetter f a) w
        rw [firstLetter_symm] at h
        calc
          restrictFun f a (restrictFun f.symm (firstLetter f a) w)
            = (f (a :: restrictFun f.symm (firstLetter f a) w)).tail := rfl
          _ = (f (f.symm (firstLetter f a :: w))).tail := by rw [h]
          _ = w := by simp [RelIso.apply_symm_apply] }
  map_rel_iff' := by
    intro w w'
    have h := f.map_isPrefix_iff (v := a :: w) (w := a :: w')
    simp only [List.cons_prefix_cons, true_and] at h
    rw [apply_cons f a w, apply_cons f a w'] at h
    simpa [List.cons_prefix_cons] using h

@[simp] lemma restrict_apply (f : TreeAut α) (a : α) (w : InfiniteRegularTree α) :
    restrict f a w = (f (a :: w)).tail :=
  rfl

lemma apply_cons_rootPerm (f : TreeAut α) (a : α) (w : InfiniteRegularTree α) :
    f (a :: w) = rootPerm f a :: restrict f a w :=
  apply_cons f a w

/-- The map underlying `combine`: on the subtree rooted at `a`, apply `F a`. -/
def combineFun (F : α → TreeAut α) : InfiniteRegularTree α → InfiniteRegularTree α
  | [] => []
  | a :: w => a :: F a w

lemma combineFun_left_inv (F : α → TreeAut α) :
    (combineFun fun a ↦ (F a).symm).LeftInverse (combineFun F) := by
  intro v
  induction v with
  | nil => rfl
  | cons a w ih =>
    simp [combineFun, RelIso.symm_apply_apply]

/-- Combine sections by acting independently on the subtrees of the root. -/
def combine (F : α → TreeAut α) : TreeAut α where
  toEquiv :=
    { toFun := combineFun F
      invFun := combineFun fun a ↦ (F a).symm
      left_inv := combineFun_left_inv F
      right_inv := fun v ↦ by
        simpa [RelIso.symm_symm] using
          combineFun_left_inv (fun a ↦ (F a).symm) v }
  map_rel_iff' := by
    intro v w
    refine Iff.symm ?_
    induction v generalizing w with
    | nil => simp [combineFun, List.nil_prefix]
    | cons a u ih =>
      cases w with
      | nil => simp [combineFun]
      | cons b v =>
        change a :: u <+: b :: v ↔ combineFun F (a :: u) <+: combineFun F (b :: v)
        by_cases h : a = b
        · subst h
          simp only [combineFun, List.cons_prefix_cons, true_and]
          exact (map_isPrefix_iff (F a)).symm
        · simp [combineFun, List.cons_prefix_cons, h]

@[simp] lemma combine_cons (F : α → TreeAut α) (a : α) (w : InfiniteRegularTree α) :
    combine F (a :: w) = a :: F a w :=
  rfl

lemma combine_one : combine (fun _ : α ↦ (1 : TreeAut α)) = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons a w => rfl

lemma combine_mul (F G : α → TreeAut α) :
    combine (fun a ↦ F a * G a) = combine F * combine G :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons a w => rfl

/-- Independent action on the subtrees of the root, as a group homomorphism. -/
def combineHom : (α → TreeAut α) →* TreeAut α where
  toFun := combine
  map_one' := combine_one
  map_mul' F G := combine_mul F G

@[simp] lemma combineHom_apply (F : α → TreeAut α) : combineHom F = combine F := rfl

/-- The rooted automorphism that permutes the children of the root by `σ`. -/
def ofRootPerm (σ : Equiv.Perm α) : TreeAut α where
  toEquiv :=
    { toFun := fun
        | [] => []
        | a :: w => σ a :: w
      invFun := fun
        | [] => []
        | a :: w => σ.symm a :: w
      left_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons a w => simp
      right_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons a w => simp }
  map_rel_iff' := by
    intro v w
    refine Iff.symm ?_
    cases v with
    | nil => simp [List.nil_prefix]
    | cons a u =>
      cases w with
      | nil => simp
      | cons b v =>
        simp [List.cons_prefix_cons]

@[simp] lemma ofRootPerm_root (σ : Equiv.Perm α) : ofRootPerm σ [] = [] := rfl

@[simp] lemma ofRootPerm_cons (σ : Equiv.Perm α) (a : α) (w : InfiniteRegularTree α) :
    ofRootPerm σ (a :: w) = σ a :: w :=
  rfl

lemma ofRootPerm_one : ofRootPerm (1 : Equiv.Perm α) = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons a w => rfl

lemma ofRootPerm_mul (σ τ : Equiv.Perm α) :
    ofRootPerm (σ * τ) = ofRootPerm σ * ofRootPerm τ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons a w => rfl

/-- Embedding of permutations of the alphabet as rooted automorphisms. -/
def ofRootPermHom : Equiv.Perm α →* TreeAut α where
  toFun := ofRootPerm
  map_one' := ofRootPerm_one
  map_mul' := ofRootPerm_mul

@[simp] lemma ofRootPermHom_apply (σ : Equiv.Perm α) : ofRootPermHom σ = ofRootPerm σ :=
  rfl

/-- The automorphism of the product of sections induced by permuting coordinates. -/
def permMulAut (σ : Equiv.Perm α) : MulAut (α → TreeAut α) where
  toFun F a := F (σ.symm a)
  invFun F a := F (σ a)
  left_inv F := funext fun a ↦ by simp
  right_inv F := funext fun a ↦ by simp
  map_mul' F G := rfl

/-- The natural action of `Equiv.Perm α` on sections by permuting coordinates. -/
def permAction : Equiv.Perm α →* MulAut (α → TreeAut α) where
  toFun := permMulAut
  map_one' := by
    refine MulEquiv.ext fun F ↦ funext fun a ↦ ?_
    have h : (1 : Equiv.Perm α).symm = 1 := rfl
    simp [permMulAut, h]
  map_mul' σ τ := by
    refine MulEquiv.ext fun F ↦ funext fun a ↦ ?_
    have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
      simp [← Equiv.Perm.inv_def, mul_inv_rev]
    simp [permMulAut, hsymm, Equiv.Perm.coe_mul]

@[simp] lemma permAction_apply (σ : Equiv.Perm α) (F : α → TreeAut α) (a : α) :
    permAction σ F a = F (σ.symm a) :=
  rfl

lemma ofRootPerm_mul_combine (σ : Equiv.Perm α) (F : α → TreeAut α) :
    ofRootPerm σ * combine F = combine (permAction σ F) * ofRootPerm σ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons a w =>
      simp [RelIso.mul_apply, permAction_apply]

lemma combineHom_compat (σ : Equiv.Perm α) :
    combineHom.comp (permAction σ).toMonoidHom =
      (MulAut.conj (ofRootPermHom σ)).toMonoidHom.comp combineHom := by
  refine MonoidHom.ext fun F ↦ ?_
  change combine (permAction σ F) = ofRootPerm σ * combine F * (ofRootPerm σ)⁻¹
  have h := ofRootPerm_mul_combine σ F
  calc
    combine (permAction σ F)
        = combine (permAction σ F) * ofRootPerm σ * (ofRootPerm σ)⁻¹ :=
          (mul_inv_cancel_right _ _).symm
    _ = ofRootPerm σ * combine F * (ofRootPerm σ)⁻¹ := by rw [h]

lemma rootPerm_combine (F : α → TreeAut α) : rootPerm (combine F) = 1 := by
  refine Equiv.Perm.ext fun a ↦ ?_
  have h : combine F [a] = [a] := by
    simp [combine_cons, map_root]
  have := apply_singleton (combine F) a
  rw [h] at this
  simpa [rootPerm_apply] using (List.cons_eq_cons.mp this).1.symm

lemma rootPerm_combine_mul_ofRootPerm (F : α → TreeAut α) (σ : Equiv.Perm α) :
    rootPerm (combine F * ofRootPerm σ) = σ := by
  refine Equiv.Perm.ext fun a ↦ ?_
  have h : (combine F * ofRootPerm σ) [a] = [σ a] := by
    simp [RelIso.mul_apply, combine_cons, map_root]
  have := apply_singleton (combine F * ofRootPerm σ) a
  rw [h] at this
  simpa [rootPerm_apply] using (List.cons_eq_cons.mp this).1.symm

lemma restrict_combine (F : α → TreeAut α) (a : α) : restrict (combine F) a = F a :=
  TreeAut.ext fun w ↦ by
    change (combine F (a :: w)).tail = F a w
    simp [combine_cons]

lemma restrict_combine_mul_ofRootPerm (F : α → TreeAut α) (σ : Equiv.Perm α) (a : α) :
    restrict (combine F * ofRootPerm σ) a = F (σ a) :=
  TreeAut.ext fun w ↦ by
    change ((combine F * ofRootPerm σ) (a :: w)).tail = F (σ a) w
    simp [RelIso.mul_apply, combine_cons]

/-- Every rooted automorphism of the infinite regular tree is uniquely determined by its
first-level sections and its root permutation. Equivalently, this is the semidirect product
isomorphism `TreeAut α ≃* (α → TreeAut α) ⋊ Equiv.Perm α`. -/
noncomputable def equivSemidirect :
    TreeAut α ≃* (α → TreeAut α) ⋊[permAction] Equiv.Perm α :=
  MulEquiv.symm
    { toFun := fun x : (α → TreeAut α) ⋊[permAction] Equiv.Perm α ↦
        combine x.left * ofRootPerm x.right
      invFun := fun f ↦ ⟨fun b ↦ restrict f ((rootPerm f).symm b), rootPerm f⟩
      left_inv := by
        intro x
        rcases x with ⟨F, σ⟩
        refine SemidirectProduct.ext ?_ ?_
        · funext b
          change restrict (combine F * ofRootPerm σ)
              ((rootPerm (combine F * ofRootPerm σ)).symm b) = F b
          rw [rootPerm_combine_mul_ofRootPerm, restrict_combine_mul_ofRootPerm]
          simp
        · exact rootPerm_combine_mul_ofRootPerm F σ
      right_inv := by
        intro f
        refine TreeAut.ext fun v ↦ ?_
        cases v with
        | nil =>
          rw [show f [] = [] from map_root f]
          simp [map_root]
        | cons a w =>
          have hf := apply_cons_rootPerm f a w
          change (combine (fun b ↦ restrict f ((rootPerm f).symm b)) *
              ofRootPerm (rootPerm f)) (a :: w) = f (a :: w)
          have ha : (rootPerm f).symm (rootPerm f a) = a :=
            Equiv.symm_apply_apply (rootPerm f) a
          rw [RelIso.mul_apply, ofRootPerm_cons, combine_cons, hf, ha]
      map_mul' :=
        (SemidirectProduct.lift combineHom ofRootPermHom combineHom_compat).map_mul' }

@[simp] lemma equivSemidirect_apply (f : TreeAut α) :
    equivSemidirect f =
      ⟨fun b ↦ restrict f ((rootPerm f).symm b), rootPerm f⟩ :=
  rfl

@[simp] lemma equivSemidirect_symm_apply (x : (α → TreeAut α) ⋊[permAction] Equiv.Perm α) :
    equivSemidirect.symm x = combine x.left * ofRootPerm x.right :=
  rfl

end TreeAut

end InfiniteRegularTree
