/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Basic

/-!
# Matroid Closure

A `Flat` of a matroid `M` is a combinatorial analogue of a subspace of a vector space,
and is defined to be a subset `F` of the ground set of `M` such that for each basis
`I` for `M`, every set having `I` as a basis is contained in `F`.

The *closure* of a set `X` in a matroid `M` is the intersection of all flats of `M` containing `X`.
This is a combinatorial analogue of the linear span of a set of vectors.

For `M : Matroid α`, this file defines a predicate `M.Flat : Set α → Prop` and a function
`M.cl : Set α → Set α` corresponding to these notions, and develops API for the latter.
API for `Matroid.Flat` will appear in another file; we include the definition here since
it is used in the definition of `Matroid.cl`.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.Flat F` means that `F` is a flat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.cl X` is the closure of `X` in `M`.

## Implementation details

If `X : Set α` satisfies `X ⊆ M.E`, then it is clear how `M.cl X` should be defined.
But `M.cl X` needs to be defined for all `X : Set α`, so a convention is needed for how `M.cl`
handles sets containing junk elements outside `M.E`. Ideally, this convention should minimize
the need to keep track of which sets are actually contained in the ground set.

All such choices come with tradeoffs; the definition we opt for satisfies `M.cl X = M.cl (X ∩ M.E)`.
The drawback here is that the statement `X ⊆ M.cl X` requires the assumption `X ⊆ M.E`.
But all the other properties of closure work nicely without extra assumptions;
closure is monotone, idempotent, and `M.cl X ⊆ M.E` for all `X`.
-/

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y R : Set α} {e : α}

/-- A flat is a maximal set having a given basis  -/
def Flat (M : Matroid α) (F : Set α) : Prop :=
  (∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.E

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Flat.subset_ground (hF : M.Flat F) : F ⊆ M.E :=
  hF.2

@[simp] lemma ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨fun _ _ _ ↦ Basis.subset_ground, Subset.rfl⟩

/-- The closure of `X ⊆ M.E` is the intersection of all the flats of `M` containing `X`.
A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F}

lemma cl_def (M : Matroid α) (X : Set α) : M.cl X = ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F} := rfl

lemma cl_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by
  rw [cl, inter_eq_self_of_subset_left hX]

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma cl_subset_ground (M : Matroid α) (X : Set α) : M.cl X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_flat, inter_subset_right⟩

lemma ground_subset_cl_iff : M.E ⊆ M.cl X ↔ M.cl X = M.E := by
  simp [M.cl_subset_ground X, subset_antisymm_iff]

@[simp] lemma cl_inter_ground (M : Matroid α) (X : Set α) : M.cl (X ∩ M.E) = M.cl X := by
  simp_rw [cl_def, inter_assoc, inter_self]

lemma inter_ground_subset_cl (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.cl X := by
  simp_rw [cl_def, subset_sInter_iff]; aesop

lemma mem_cl_iff_forall_mem_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [M.cl_def' X, mem_sInter, mem_setOf, and_imp]

lemma subset_cl_iff_forall_subset_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → Y ⊆ F := by
  simp_rw [M.cl_def' X, subset_sInter_iff, mem_setOf, and_imp]

lemma subset_cl (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl X := by
  simp [M.cl_def' X, subset_sInter_iff]

lemma Flat.cl (hF : M.Flat F) : M.cl F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F)

@[simp] lemma cl_ground (M : Matroid α) : M.cl M.E = M.E :=
  (M.cl_subset_ground M.E).antisymm (M.subset_cl M.E)

@[simp] lemma cl_univ (M : Matroid α) : M.cl univ = M.E := by
  rw [← cl_inter_ground, univ_inter, cl_ground]

lemma cl_subset_cl (M : Matroid α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  subset_sInter (fun _ h' ↦ sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)

lemma cl_mono (M : Matroid α) : Monotone M.cl :=
  fun _ _ ↦ M.cl_subset_cl

@[simp] lemma cl_cl (M : Matroid α) (X : Set α) : M.cl (M.cl X) = M.cl X :=
  (M.subset_cl _).antisymm' (subset_sInter
    (fun F hF ↦ (cl_subset_cl _ (sInter_subset_of_mem hF)).trans hF.1.cl.subset))

lemma cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
    (M.cl_subset_cl hXY).trans_eq (M.cl_cl Y)

lemma cl_subset_cl_iff_subset_cl (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  ⟨(M.subset_cl X).trans, cl_subset_cl_of_subset_cl⟩

lemma subset_cl_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl Y :=
  hXY.trans (M.subset_cl Y)

lemma subset_cl_of_subset' (M : Matroid α) (hXY : X ⊆ Y) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl Y := by
  rw [← cl_inter_ground]; exact M.subset_cl_of_subset (subset_inter hXY hX)

lemma exists_of_cl_ssubset (hXY : M.cl X ⊂ M.cl Y) : ∃ e ∈ Y, e ∉ M.cl X := by
  by_contra! hcon
  exact hXY.not_subset (M.cl_subset_cl_of_subset_cl hcon)

lemma mem_cl_of_mem (M : Matroid α) (h : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) : e ∈ M.cl X :=
  (M.subset_cl X) h

lemma mem_cl_of_mem' (M : Matroid α) (heX : e ∈ X) (h : e ∈ M.E := by aesop_mat) : e ∈ M.cl X := by
  rw [← cl_inter_ground]
  exact M.mem_cl_of_mem ⟨heX, h⟩

lemma not_mem_of_mem_diff_cl (he : e ∈ M.E \ M.cl X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_cl_of_mem' heX he.1

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma mem_ground_of_mem_cl (he : e ∈ M.cl X) : e ∈ M.E :=
  (M.cl_subset_ground _) he

lemma cl_iUnion_cl_eq_cl_iUnion (M : Matroid α) (Xs : ι → Set α) :
    M.cl (⋃ i, M.cl (Xs i)) = M.cl (⋃ i, Xs i) := by
  refine (M.cl_subset_cl_of_subset_cl
    (iUnion_subset (fun i ↦ M.cl_subset_cl (subset_iUnion _ _)))).antisymm ?_
  rw [← cl_inter_ground, iUnion_inter]
  refine M.cl_subset_cl (iUnion_subset (fun i ↦ (M.subset_cl _).trans ?_))
  rw [cl_inter_ground]
  exact subset_iUnion (fun i ↦ M.cl (Xs i)) i

lemma cl_iUnion_congr (Xs Ys : ι → Set α) (h : ∀ i, M.cl (Xs i) = M.cl (Ys i)) :
    M.cl (⋃ i, Xs i) = M.cl (⋃ i, Ys i) := by
  simp [h, ← M.cl_iUnion_cl_eq_cl_iUnion]

lemma cl_biUnion_cl_eq_cl_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.cl (⋃ X ∈ Xs, M.cl X) = M.cl (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion, biUnion_eq_iUnion, cl_iUnion_cl_eq_cl_iUnion]

lemma cl_biUnion_cl_eq_cl_biUnion (M : Matroid α) (Xs : ι → Set α) (A : Set ι) :
    M.cl (⋃ i ∈ A, M.cl (Xs i)) = M.cl (⋃ i ∈ A, Xs i) := by
  rw [biUnion_eq_iUnion, M.cl_iUnion_cl_eq_cl_iUnion, biUnion_eq_iUnion]

lemma cl_biUnion_congr (M : Matroid α) (Xs Ys : ι → Set α) (A : Set ι)
    (h : ∀ i ∈ A, M.cl (Xs i) = M.cl (Ys i)) : M.cl (⋃ i ∈ A, Xs i) = M.cl (⋃ i ∈ A, Ys i) := by
  rw [← cl_biUnion_cl_eq_cl_biUnion, iUnion₂_congr h, cl_biUnion_cl_eq_cl_biUnion]

lemma cl_cl_union_cl_eq_cl_union (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [eq_comm, union_eq_iUnion, ← cl_iUnion_cl_eq_cl_iUnion, union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

@[simp] lemma cl_union_cl_right_eq (M : Matroid α) (X Y : Set α) :
    M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [← cl_cl_union_cl_eq_cl_union, cl_cl, cl_cl_union_cl_eq_cl_union]

@[simp] lemma cl_union_cl_left_eq (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) := by
  rw [← cl_cl_union_cl_eq_cl_union, cl_cl, cl_cl_union_cl_eq_cl_union]

@[simp] lemma cl_insert_cl_eq_cl_insert (M : Matroid α) (e : α) (X : Set α) :
    M.cl (insert e (M.cl X)) = M.cl (insert e X) := by
  simp_rw [← singleton_union, cl_union_cl_right_eq]

@[simp] lemma cl_union_cl_empty_eq (M : Matroid α) (X : Set α) :
    M.cl X ∪ M.cl ∅ = M.cl X :=
  union_eq_self_of_subset_right (M.cl_subset_cl (empty_subset _))

@[simp] lemma cl_empty_union_cl_eq (M : Matroid α) (X : Set α) :
    M.cl ∅ ∪ M.cl X = M.cl X :=
  union_eq_self_of_subset_left (M.cl_subset_cl (empty_subset _))

lemma cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X := by
  rw [← cl_insert_cl_eq_cl_insert, insert_eq_of_mem he, cl_cl]

lemma mem_cl_self (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.cl {e} :=
  mem_cl_of_mem' M rfl
