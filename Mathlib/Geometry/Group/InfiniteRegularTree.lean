/-
Copyright (c) 2026 Ezequiel Souza dos Santos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezequiel Souza dos Santos
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Data.List.Infix
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The infinite regular rooted tree

The infinite regular rooted tree of degree `n` has a vertex for every finite word on the alphabet
`Fin n`. The root is the empty word. The children of a vertex `v` are the words `v ++ [i]` for
`i : Fin n`.

## Main definitions

* `InfiniteRegularTree n`: vertices are lists `List (Fin n)`.
* `InfiniteRegularTree.root`: the empty word.
* `InfiniteRegularTree.succ`: the child of a vertex obtained by appending a letter.
* `InfiniteRegularTree.TreeAut n`: rooted automorphisms, as order isomorphisms of the prefix
  partial order (`RelIso`). The name `TreeAut` avoids a clash with `MulAut`.
* `InfiniteRegularTree.TreeAut.combine`: act independently on the `n` subtrees of the root.
* `InfiniteRegularTree.TreeAut.ofRootPerm`: the rooted automorphism induced by a permutation of
  the children of the root.
* `InfiniteRegularTree.TreeAut.rootPerm`: the permutation induced at the root.
* `InfiniteRegularTree.TreeAut.restrict`: the section of an automorphism at a first-level vertex.
* `InfiniteRegularTree.TreeAut.equivSemidirect`: the wreath recursion isomorphism
  `TreeAut n ≃* (Fin n → TreeAut n) ⋊ Equiv.Perm (Fin n)`.

## References

* Nekrashevych, *Self-Similar Groups*, AMS Mathematical Surveys and Monographs 117.

## Tags

regular tree, rooted tree, wreath product, geometric group theory
-/

@[expose] public section

/-- The infinite regular rooted tree of degree `n`: vertices are finite words on `Fin n`. -/
abbrev InfiniteRegularTree (n : ℕ) := List (Fin n)

namespace InfiniteRegularTree

variable {n : ℕ}

/-- The root of the infinite regular tree. -/
def root : InfiniteRegularTree n := []

/-- The child of `v` obtained by appending the letter `i`. -/
def succ (v : InfiniteRegularTree n) (i : Fin n) : InfiniteRegularTree n := v ++ [i]

@[simp] lemma root_eq_nil : (root : InfiniteRegularTree n) = [] := rfl

@[simp] lemma succ_eq_append (v : InfiniteRegularTree n) (i : Fin n) : v.succ i = v ++ [i] := rfl

@[simp] lemma length_root : (root : InfiniteRegularTree n).length = 0 := rfl

lemma length_succ (v : InfiniteRegularTree n) (i : Fin n) : (v.succ i).length = v.length + 1 := by
  simp [succ]

lemma isPrefix_root (v : InfiniteRegularTree n) : (root : InfiniteRegularTree n) <+: v :=
  List.nil_prefix

/-- The prefix relation on vertices. -/
def prefixRel (n : ℕ) : InfiniteRegularTree n → InfiniteRegularTree n → Prop := (· <+: ·)

/-- A rooted automorphism of the infinite regular tree is an order isomorphism of the prefix
partial order. -/
abbrev TreeAut (n : ℕ) := RelIso (prefixRel n) (prefixRel n)

namespace TreeAut

variable {n : ℕ}

lemma map_isPrefix_iff (f : TreeAut n) {v w : InfiniteRegularTree n} : v <+: w ↔ f v <+: f w :=
  (f.map_rel_iff).symm

/-- A tree automorphism fixes the root. -/
@[simp] lemma map_root (f : TreeAut n) : f [] = [] := by
  have h : f [] <+: f (f.symm []) := f.map_isPrefix_iff.mp List.nil_prefix
  rw [RelIso.apply_symm_apply] at h
  exact List.prefix_nil.mp h

@[ext] lemma ext {f g : TreeAut n} (h : ∀ v, f v = g v) : f = g :=
  DFunLike.ext f g h

@[simp] lemma inv_eq_symm (f : TreeAut n) : f⁻¹ = f.symm := rfl

lemma length_lt_of_prefix_ne {v w : InfiniteRegularTree n} (h : v <+: w) (hne : v ≠ w) :
    v.length < w.length :=
  Nat.lt_of_le_of_ne h.length_le fun H ↦ hne (h.eq_of_length H)

lemma length_map_take_ge (f : TreeAut n) (v : InfiniteRegularTree n) :
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
@[simp] lemma map_length (f : TreeAut n) (v : InfiniteRegularTree n) : (f v).length = v.length := by
  refine Nat.le_antisymm ?_ ?_
  · have := length_map_take_ge f.symm (f v) (f v).length le_rfl
    simpa [List.take_length] using this
  · have := length_map_take_ge f v v.length le_rfl
    simpa [List.take_length] using this

lemma apply_cons_ne_nil (f : TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) :
    f (i :: w) ≠ [] := by
  intro h
  have := f.map_length (i :: w)
  simp [h] at this

/-- The first letter of `f [i]`. This is the image of the child `i` of the root. -/
def firstLetter (f : TreeAut n) (i : Fin n) : Fin n :=
  (f [i]).head (apply_cons_ne_nil f i [])

lemma apply_singleton (f : TreeAut n) (i : Fin n) : f [i] = [firstLetter f i] := by
  have hne := apply_cons_ne_nil f i []
  have htail : (f [i]).tail = [] := by
    apply List.eq_nil_of_length_eq_zero
    have hlen := f.map_length [i]
    rw [List.length_tail, hlen]
    rfl
  conv_lhs => rw [← List.cons_head_tail hne, htail]
  rfl

lemma firstLetter_injective (f : TreeAut n) : Function.Injective f.firstLetter := by
  intro i j h
  have : ([i] : InfiniteRegularTree n) = [j] :=
    f.injective (by rw [apply_singleton, apply_singleton, h])
  exact List.singleton_inj.mp this

lemma firstLetter_surjective (f : TreeAut n) : Function.Surjective f.firstLetter := by
  intro j
  refine ⟨firstLetter f.symm j, ?_⟩
  have h : f.symm [j] = [firstLetter f.symm j] := apply_singleton f.symm j
  have := congrArg f h
  simp only [RelIso.apply_symm_apply] at this
  rw [apply_singleton] at this
  exact (List.cons_eq_cons.mp this).1.symm

/-- The permutation of the children of the root induced by `f`. -/
noncomputable def rootPerm (f : TreeAut n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective f.firstLetter ⟨f.firstLetter_injective, f.firstLetter_surjective⟩

@[simp] lemma rootPerm_apply (f : TreeAut n) (i : Fin n) : rootPerm f i = firstLetter f i :=
  rfl

/-- Action of `f` on the subtree hanging from the child `i` of the root. -/
def restrictFun (f : TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) : InfiniteRegularTree n :=
  (f (i :: w)).tail

lemma apply_cons (f : TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) :
    f (i :: w) = firstLetter f i :: restrictFun f i w := by
  have hpref : f [i] <+: f (i :: w) := (f.map_isPrefix_iff).mp (by simp [List.cons_prefix_cons])
  rw [apply_singleton] at hpref
  obtain ⟨s, hs⟩ := hpref
  simp [restrictFun, ← hs]

lemma firstLetter_symm (f : TreeAut n) (i : Fin n) :
    firstLetter f.symm (firstLetter f i) = i := by
  have h : f.symm [firstLetter f i] = [i] := by
    rw [← apply_singleton f i]
    exact f.symm_apply_apply [i]
  rw [apply_singleton] at h
  exact (List.cons_eq_cons.mp h).1

/-- The section of `f` at the first-level vertex `i`. -/
def restrict (f : TreeAut n) (i : Fin n) : TreeAut n where
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

@[simp] lemma restrict_apply (f : TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) :
    restrict f i w = (f (i :: w)).tail :=
  rfl

lemma apply_cons_rootPerm (f : TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) :
    f (i :: w) = rootPerm f i :: restrict f i w :=
  apply_cons f i w

/-- The map underlying `combine`: on the subtree rooted at `i`, apply `F i`. -/
def combineFun (F : Fin n → TreeAut n) : InfiniteRegularTree n → InfiniteRegularTree n
  | [] => []
  | i :: w => i :: F i w

lemma combineFun_left_inv (F : Fin n → TreeAut n) :
    (combineFun fun i ↦ (F i).symm).LeftInverse (combineFun F) := by
  intro v
  induction v with
  | nil => rfl
  | cons i w ih =>
    simp [combineFun, RelIso.symm_apply_apply]

/-- Combine sections by acting independently on the `n` subtrees of the root. -/
def combine (F : Fin n → TreeAut n) : TreeAut n where
  toEquiv :=
    { toFun := combineFun F
      invFun := combineFun fun i ↦ (F i).symm
      left_inv := combineFun_left_inv F
      right_inv := fun v ↦ by
        simpa [RelIso.symm_symm] using
          combineFun_left_inv (fun i ↦ (F i).symm) v }
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
        change i :: a <+: j :: b ↔ combineFun F (i :: a) <+: combineFun F (j :: b)
        by_cases h : i = j
        · subst h
          simp only [combineFun, List.cons_prefix_cons, true_and]
          exact (F i).map_isPrefix_iff
        · simp [combineFun, List.cons_prefix_cons, h]

@[simp] lemma combine_cons (F : Fin n → TreeAut n) (i : Fin n) (w : InfiniteRegularTree n) :
    combine F (i :: w) = i :: F i w :=
  rfl

lemma combine_one : combine (fun _ : Fin n ↦ (1 : TreeAut n)) = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => rfl

lemma combine_mul (F G : Fin n → TreeAut n) :
    combine (fun i ↦ F i * G i) = combine F * combine G :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => rfl

/-- Independent action on the subtrees of the root, as a group homomorphism. -/
def combineHom : (Fin n → TreeAut n) →* TreeAut n where
  toFun := combine
  map_one' := combine_one
  map_mul' F G := combine_mul F G

@[simp] lemma combineHom_apply (F : Fin n → TreeAut n) : combineHom F = combine F := rfl

/-- The rooted automorphism that permutes the children of the root by `σ`. -/
def ofRootPerm (σ : Equiv.Perm (Fin n)) : TreeAut n where
  toEquiv :=
    { toFun := fun
        | [] => []
        | i :: w => σ i :: w
      invFun := fun
        | [] => []
        | i :: w => σ.symm i :: w
      left_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w => simp
      right_inv := by
        intro v
        cases v with
        | nil => rfl
        | cons i w => simp }
  map_rel_iff' := by
    intro v w
    refine Iff.symm ?_
    cases v with
    | nil => simp [prefixRel, List.nil_prefix]
    | cons i a =>
      cases w with
      | nil => simp [prefixRel]
      | cons j b =>
        simp [prefixRel, List.cons_prefix_cons]

@[simp] lemma ofRootPerm_root (σ : Equiv.Perm (Fin n)) : ofRootPerm σ [] = [] := rfl

@[simp] lemma ofRootPerm_cons (σ : Equiv.Perm (Fin n)) (i : Fin n) (w : InfiniteRegularTree n) :
    ofRootPerm σ (i :: w) = σ i :: w :=
  rfl

lemma ofRootPerm_one : ofRootPerm (1 : Equiv.Perm (Fin n)) = 1 :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => rfl

lemma ofRootPerm_mul (σ τ : Equiv.Perm (Fin n)) :
    ofRootPerm (σ * τ) = ofRootPerm σ * ofRootPerm τ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w => rfl

/-- Embedding of permutations of the alphabet as rooted automorphisms. -/
def ofRootPermHom : Equiv.Perm (Fin n) →* TreeAut n where
  toFun := ofRootPerm
  map_one' := ofRootPerm_one
  map_mul' := ofRootPerm_mul

@[simp] lemma ofRootPermHom_apply (σ : Equiv.Perm (Fin n)) : ofRootPermHom σ = ofRootPerm σ :=
  rfl

/-- The automorphism of the product of sections induced by permuting coordinates. -/
def permMulAut (σ : Equiv.Perm (Fin n)) : MulAut (Fin n → TreeAut n) where
  toFun F i := F (σ.symm i)
  invFun F i := F (σ i)
  left_inv F := funext fun i ↦ by simp
  right_inv F := funext fun i ↦ by simp
  map_mul' F G := rfl

/-- The natural action of `Equiv.Perm (Fin n)` on sections by permuting coordinates. -/
def permAction : Equiv.Perm (Fin n) →* MulAut (Fin n → TreeAut n) where
  toFun := permMulAut
  map_one' := by
    refine MulEquiv.ext fun F ↦ funext fun i ↦ ?_
    have h : (1 : Equiv.Perm (Fin n)).symm = 1 := rfl
    simp [permMulAut, h]
  map_mul' σ τ := by
    refine MulEquiv.ext fun F ↦ funext fun i ↦ ?_
    have hsymm : (σ * τ).symm = τ.symm * σ.symm := by
      simp [← Equiv.Perm.inv_def, mul_inv_rev]
    simp [permMulAut, hsymm, Equiv.Perm.coe_mul]

@[simp] lemma permAction_apply (σ : Equiv.Perm (Fin n)) (F : Fin n → TreeAut n) (i : Fin n) :
    permAction σ F i = F (σ.symm i) :=
  rfl

lemma ofRootPerm_mul_combine (σ : Equiv.Perm (Fin n)) (F : Fin n → TreeAut n) :
    ofRootPerm σ * combine F = combine (permAction σ F) * ofRootPerm σ :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil => rfl
    | cons i w =>
      simp [RelIso.mul_apply, permAction_apply]

lemma combineHom_compat (σ : Equiv.Perm (Fin n)) :
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

/-- The homomorphism realizing the wreath recursion
`(Fin n → TreeAut n) ⋊ Equiv.Perm (Fin n) → TreeAut n`. -/
def ofSemidirect : (Fin n → TreeAut n) ⋊[permAction] Equiv.Perm (Fin n) →* TreeAut n :=
  SemidirectProduct.lift combineHom ofRootPermHom combineHom_compat

lemma ofSemidirect_apply (x : (Fin n → TreeAut n) ⋊[permAction] Equiv.Perm (Fin n)) :
    ofSemidirect x = combine x.left * ofRootPerm x.right :=
  rfl

lemma rootPerm_combine (F : Fin n → TreeAut n) : rootPerm (combine F) = 1 := by
  refine Equiv.Perm.ext fun i ↦ ?_
  have h : combine F [i] = [i] := by
    simp [combine_cons, map_root]
  have := apply_singleton (combine F) i
  rw [h] at this
  simpa [rootPerm_apply] using (List.cons_eq_cons.mp this).1.symm

lemma rootPerm_combine_mul_ofRootPerm (F : Fin n → TreeAut n) (σ : Equiv.Perm (Fin n)) :
    rootPerm (combine F * ofRootPerm σ) = σ := by
  refine Equiv.Perm.ext fun i ↦ ?_
  have h : (combine F * ofRootPerm σ) [i] = [σ i] := by
    simp [RelIso.mul_apply, combine_cons, map_root]
  have := apply_singleton (combine F * ofRootPerm σ) i
  rw [h] at this
  simpa [rootPerm_apply] using (List.cons_eq_cons.mp this).1.symm

lemma restrict_combine (F : Fin n → TreeAut n) (i : Fin n) : restrict (combine F) i = F i :=
  TreeAut.ext fun w ↦ by
    change (combine F (i :: w)).tail = F i w
    simp [combine_cons]

lemma restrict_combine_mul_ofRootPerm (F : Fin n → TreeAut n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    restrict (combine F * ofRootPerm σ) i = F (σ i) :=
  TreeAut.ext fun w ↦ by
    change ((combine F * ofRootPerm σ) (i :: w)).tail = F (σ i) w
    simp [RelIso.mul_apply, combine_cons]

/-- The inverse of `ofSemidirect`, recording sections and the root permutation. -/
noncomputable def toSemidirect (f : TreeAut n) :
    (Fin n → TreeAut n) ⋊[permAction] Equiv.Perm (Fin n) where
  left := fun j ↦ restrict f ((rootPerm f).symm j)
  right := rootPerm f

lemma ofSemidirect_toSemidirect (f : TreeAut n) : ofSemidirect (toSemidirect f) = f :=
  TreeAut.ext fun v ↦ by
    cases v with
    | nil =>
      rw [show f [] = [] from map_root f]
      rw [show ofSemidirect (toSemidirect f) [] = [] from map_root _]
    | cons i w =>
      have hf := apply_cons_rootPerm f i w
      change (combine (fun j ↦ restrict f ((rootPerm f).symm j)) * ofRootPerm (rootPerm f))
        (i :: w) = f (i :: w)
      have hi : (rootPerm f).symm (rootPerm f i) = i :=
        Equiv.symm_apply_apply (rootPerm f) i
      rw [RelIso.mul_apply, ofRootPerm_cons, combine_cons, hf, hi]

lemma toSemidirect_ofSemidirect (x : (Fin n → TreeAut n) ⋊[permAction] Equiv.Perm (Fin n)) :
    toSemidirect (ofSemidirect x) = x := by
  rcases x with ⟨F, σ⟩
  refine SemidirectProduct.ext ?_ ?_
  · funext j
    change restrict (combine F * ofRootPerm σ) ((rootPerm (combine F * ofRootPerm σ)).symm j) =
      F j
    rw [rootPerm_combine_mul_ofRootPerm, restrict_combine_mul_ofRootPerm]
    simp
  · exact rootPerm_combine_mul_ofRootPerm F σ

/-- Every rooted automorphism of the infinite regular tree is uniquely determined by its
first-level sections and its root permutation. Equivalently,
`TreeAut n ≃* (Fin n → TreeAut n) ⋊ Equiv.Perm (Fin n)`. -/
noncomputable def equivSemidirect :
    TreeAut n ≃* (Fin n → TreeAut n) ⋊[permAction] Equiv.Perm (Fin n) :=
  (MulEquiv.ofBijective ofSemidirect
    ⟨Function.LeftInverse.injective toSemidirect_ofSemidirect,
      Function.LeftInverse.surjective ofSemidirect_toSemidirect⟩).symm

end TreeAut

end InfiniteRegularTree