/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Basic
import Mathlib.Order.Closure

/-!
# Matroid Closure

A `Flat` of a matroid `M` is a combinatorial analogue of a subspace of a vector space,
and is defined to be a subset `F` of the ground set of `M` such that for each basis
`I` for `M`, every set having `I` as a basis is contained in `F`.

The *closure* of a set `X` in a matroid `M` is the intersection of all flats of `M` containing `X`.
This is a combinatorial analogue of the linear span of a set of vectors.

For `M : Matroid α`, this file defines a predicate `M.Flat : Set α → Prop` and a function
`M.closure : Set α → Set α` corresponding to these notions, and develops API for the latter.
API for `Matroid.Flat` will appear in another file; we include the definition here since
it is used in the definition of `Matroid.cl`.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.Flat F` means that `F` is a flat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.closure X` is the closure of `X` in `M`.

## Implementation details

If `X : Set α` satisfies `X ⊆ M.E`, then it is clear how `M.closure X` should be defined.
But `M.closure X` needs to be defined for all `X : Set α`, so a convention is needed for how `M.cl`
handles sets containing junk elements outside `M.E`. Ideally, this convention should minimize
the need to keep track of which sets are actually contained in the ground set.

All such choices come with tradeoffs; the definition we opt for satisfies `M.closure X = M.closure (X ∩ M.E)`.
The drawback here is that the statement `X ⊆ M.closure X` requires the assumption `X ⊆ M.E`.
But all the other properties of closure work nicely without extra assumptions;
closure is monotone, idempotent, and `M.closure X ⊆ M.E` for all `X`.
-/

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y R : Set α} {e : α}

section Flat

/-- A flat is a maximal set having a given basis  -/
@[mk_iff]
structure Flat (M : Matroid α) (F : Set α) : Prop where
  subset_of_basis_of_basis : ∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F
  subset_ground : F ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] Flat.subset_ground

@[simp] lemma ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨fun _ _ _ ↦ Basis.subset_ground, Subset.rfl⟩

lemma Flat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.Flat (Fs i)) : M.Flat (⋂ i, Fs i) := by
  refine ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine' subset_union_right.trans ((hFs i).1 (X := Fs i ∪ X) hIJ _)
  convert hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

/-- The property of being a flat gives rise to a `ClosureOperator` on the subsets of `M.E`,
in which the `IsClosed` sets correspond to `Flat`s.
(We can't define such an operator on all of `Set α`,
since this would incorrectly force `univ` to always be a flat.)-/
def subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E) := by
  refine ClosureOperator.ofCompletePred (fun F ↦ M.Flat F.1) fun s hs ↦ ?_
  obtain (rfl | hne) := s.eq_empty_or_nonempty
  · simp
  have _ := hne.coe_sort
  convert Flat.iInter (M := M) (Fs := fun (F : s) ↦ F.1.1) (fun F ↦ hs F.1 F.2)
  ext
  aesop

lemma flat_iff_isClosed : M.Flat F ↔ ∃ h : F ⊆ M.E, M.subtypeClosure.IsClosed ⟨F, h⟩ := by
  simpa [subtypeClosure] using Flat.subset_ground

lemma isClosed_iff_flat {F : Iic M.E} : M.subtypeClosure.IsClosed F ↔ M.Flat F := by
  simp [subtypeClosure]

end Flat

/-- The closure of `X ⊆ M.E` is the intersection of all the flats of `M` containing `X`.
A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.closure X := M.closure (X ∩ M.E)`. -/
def closure (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F}

lemma closure_def (M : Matroid α) (X : Set α) : M.closure X = ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F} := rfl

lemma closure_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by
  rw [closure, inter_eq_self_of_subset_left hX]

lemma closure_eq_subtypeClosure (M : Matroid α) (X : Set α) :
    M.closure X = M.subtypeClosure ⟨X ∩ M.E, inter_subset_right⟩  := by
  suffices ∀ (x : α), (∀ (t : Set α), M.Flat t → X ∩ M.E ⊆ t → x ∈ t) ↔
    (x ∈ M.E ∧ ∀ a ⊆ M.E, X ∩ M.E ⊆ a → M.Flat a → x ∈ a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨h _ M.ground_flat inter_subset_right, fun F _ hXF hF ↦ h F hF hXF⟩,
    fun ⟨_, h⟩ F hF hXF ↦ h F hF.subset_ground hXF hF⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma closure_subset_ground (M : Matroid α) (X : Set α) : M.closure X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_flat, inter_subset_right⟩

lemma ground_subset_closure_iff : M.E ⊆ M.closure X ↔ M.closure X = M.E := by
  simp [M.closure_subset_ground X, subset_antisymm_iff]

@[simp] lemma closure_inter_ground (M : Matroid α) (X : Set α) :
    M.closure (X ∩ M.E) = M.closure X := by
  simp_rw [closure_def, inter_assoc, inter_self]

lemma inter_ground_subset_closure (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.closure X := by
  simp_rw [closure_def, subset_sInter_iff]; aesop

lemma mem_closure_iff_forall_mem_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [M.closure_def' X, mem_sInter, mem_setOf, and_imp]

lemma subset_closure_iff_forall_subset_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure X ↔ ∀ F, M.Flat F → X ⊆ F → Y ⊆ F := by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_setOf, and_imp]

lemma subset_closure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure X := by
  simp [M.closure_def' X, subset_sInter_iff]

lemma Flat.closure (hF : M.Flat F) : M.closure F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

@[simp] lemma closure_ground (M : Matroid α) : M.closure M.E = M.E :=
  (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)

@[simp] lemma closure_univ (M : Matroid α) : M.closure univ = M.E := by
  rw [← closure_inter_ground, univ_inter, closure_ground]

lemma closure_subset_closure (M : Matroid α) (h : X ⊆ Y) : M.closure X ⊆ M.closure Y :=
  subset_sInter (fun _ h' ↦ sInter_subset_of_mem
    ⟨h'.1, subset_trans (inter_subset_inter_left _ h) h'.2⟩)

lemma closure_mono (M : Matroid α) : Monotone M.closure :=
  fun _ _ ↦ M.closure_subset_closure

@[simp] lemma closure_closure (M : Matroid α) (X : Set α) : M.closure (M.closure X) = M.closure X :=
  (M.subset_closure _).antisymm' (subset_sInter
    (fun F hF ↦ (closure_subset_closure _ (sInter_subset_of_mem hF)).trans hF.1.closure.subset))

lemma closure_subset_closure_of_subset_closure (hXY : X ⊆ M.closure Y) :
    M.closure X ⊆ M.closure Y :=
  (M.closure_subset_closure hXY).trans_eq (M.closure_closure Y)

lemma closure_subset_closure_iff_subset_closure (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X ⊆ M.closure Y ↔ X ⊆ M.closure Y :=
  ⟨(M.subset_closure X).trans, closure_subset_closure_of_subset_closure⟩

lemma subset_closure_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure Y :=
  hXY.trans (M.subset_closure Y)

lemma subset_closure_of_subset' (M : Matroid α) (hXY : X ⊆ Y) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure Y := by
  rw [← closure_inter_ground]; exact M.subset_closure_of_subset (subset_inter hXY hX)

lemma exists_of_closure_ssubset (hXY : M.closure X ⊂ M.closure Y) : ∃ e ∈ Y, e ∉ M.closure X := by
  by_contra! hcon
  exact hXY.not_subset (M.closure_subset_closure_of_subset_closure hcon)

lemma mem_closure_of_mem (M : Matroid α) (h : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X :=
  (M.subset_closure X) h

lemma mem_closure_of_mem' (M : Matroid α) (heX : e ∈ X) (h : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure X := by
  rw [← closure_inter_ground]
  exact M.mem_closure_of_mem ⟨heX, h⟩

lemma not_mem_of_mem_diff_closure (he : e ∈ M.E \ M.closure X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_closure_of_mem' heX he.1

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma mem_ground_of_mem_closure (he : e ∈ M.closure X) : e ∈ M.E :=
  (M.closure_subset_ground _) he

lemma closure_iUnion_closure_eq_closure_iUnion (M : Matroid α) (Xs : ι → Set α) :
    M.closure (⋃ i, M.closure (Xs i)) = M.closure (⋃ i, Xs i) := by
  simp_rw [closure_eq_subtypeClosure, iUnion_inter, Subtype.coe_inj]
  convert M.subtypeClosure.closure_iSup_closure (fun i ↦ ⟨Xs i ∩ M.E, inter_subset_right⟩) <;>
  simp [← iUnion_inter, subtypeClosure]

lemma closure_iUnion_congr (Xs Ys : ι → Set α) (h : ∀ i, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i, Xs i) = M.closure (⋃ i, Ys i) := by
  simp [h, ← M.closure_iUnion_closure_eq_closure_iUnion]

lemma closure_biUnion_closure_eq_closure_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.closure (⋃ X ∈ Xs, M.closure X) = M.closure (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion, biUnion_eq_iUnion, closure_iUnion_closure_eq_closure_iUnion]

lemma closure_biUnion_closure_eq_closure_biUnion (M : Matroid α) (Xs : ι → Set α) (A : Set ι) :
    M.closure (⋃ i ∈ A, M.closure (Xs i)) = M.closure (⋃ i ∈ A, Xs i) := by
  rw [biUnion_eq_iUnion, M.closure_iUnion_closure_eq_closure_iUnion, biUnion_eq_iUnion]

lemma closure_biUnion_congr (M : Matroid α) (Xs Ys : ι → Set α) (A : Set ι)
    (h : ∀ i ∈ A, M.closure (Xs i) = M.closure (Ys i)) :
    M.closure (⋃ i ∈ A, Xs i) = M.closure (⋃ i ∈ A, Ys i) := by
  rw [← closure_biUnion_closure_eq_closure_biUnion, iUnion₂_congr h,
    closure_biUnion_closure_eq_closure_biUnion]

lemma closure_closure_union_closure_eq_closure_union (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [eq_comm, union_eq_iUnion, ← closure_iUnion_closure_eq_closure_iUnion, union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

@[simp] lemma closure_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.closure (X ∪ M.closure Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]

@[simp] lemma closure_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.closure (M.closure X ∪ Y) = M.closure (X ∪ Y) := by
  rw [← closure_closure_union_closure_eq_closure_union, closure_closure,
    closure_closure_union_closure_eq_closure_union]

@[simp] lemma closure_insert_closure_eq_closure_insert (M : Matroid α) (e : α) (X : Set α) :
    M.closure (insert e (M.closure X)) = M.closure (insert e X) := by
  simp_rw [← singleton_union, closure_union_closure_right_eq]

@[simp] lemma closure_union_closure_empty_eq (M : Matroid α) (X : Set α) :
    M.closure X ∪ M.closure ∅ = M.closure X :=
  union_eq_self_of_subset_right (M.closure_subset_closure (empty_subset _))

@[simp] lemma closure_empty_union_closure_eq (M : Matroid α) (X : Set α) :
    M.closure ∅ ∪ M.closure X = M.closure X :=
  union_eq_self_of_subset_left (M.closure_subset_closure (empty_subset _))

lemma closure_insert_eq_of_mem_closure (he : e ∈ M.closure X) :
    M.closure (insert e X) = M.closure X := by
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem he, closure_closure]

lemma mem_closure_self (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure {e} :=
  mem_closure_of_mem' M rfl
