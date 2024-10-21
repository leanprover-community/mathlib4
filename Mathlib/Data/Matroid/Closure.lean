/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Restrict
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
it is used in the definition of `Matroid.closure`.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.Flat F` means that `F` is a flat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.closure X` is the closure of `X` in `M`.
* For `M : Matroid α` and `X : ↑(Iic M.E)` (i.e. a bundled subset of `M.E`),
  `M.subtypeClosure X` is the closure of `X`, viewed as a term in `↑(Iic M.E)`.
  This is a `ClosureOperator` on `↑(Iic M.E)`.

## Implementation details

If `X : Set α` satisfies `X ⊆ M.E`, then it is clear how `M.closure X` should be defined.
But `M.closure X` also needs to be defined for all `X : Set α`,
so a convention is needed for how it handles sets containing junk elements outside `M.E`.
All such choices come with tradeoffs. Provided that `M.closure X` has already been defined
for `X ⊆ M.E`, the two best candidates for extending it to all `X` seem to be:

(1) The function for which `M.closure X = M.closure (X ∩ M.E)` for all `X : Set α`

(2) The function for which `M.closure X = M.closure (X ∩ M.E) ∪ X` for all `X : Set α`

For both options, the function `closure` is monotone and idempotent with no assumptions on `X`.

Choice (1) has the advantage that `M.closure X ⊆ M.E` holds for all `X` without the assumption
that `X ⊆ M.E`, which is very nice for `aesop_mat`. It is also fairly convenient to rewrite
`M.closure X` to `M.closure (X ∩ M.E)` when one needs to work with a subset of the ground set.
Its disadvantage is that the statement `X ⊆ M.closure X` is only true provided that `X ⊆ M.E`.

Choice (2) has the reverse property: we would have `X ⊆ M.closure X` for all `X`,
but the condition `M.closure X ⊆ M.E` requires `X ⊆ M.E` to hold.
It has a couple of other advantages too: it is actually the closure function of a matroid on `α`
with ground set `univ` (specifically, the direct sum of `M` and a free matroid on `M.Eᶜ`),
and because of this, it is an example of a `ClosureOperator` on `α`, which in turn gives access
to nice existing API for both `ClosureOperator` and `GaloisInsertion`.
This also relates to flats; `F ⊆ M.E ∧ ClosureOperator.IsClosed F` is equivalent to `M.Flat F`.
(All of this fails for choice (1), since `X ⊆ M.closure X` is required for
a `ClosureOperator`, but isn't true for non-subsets of `M.E`)

The API that choice (2) would offer is very beguiling, but after extensive experimentation in
an external repo, it seems that (1) is far less rough around the edges in practice,
so we go with (1). It may be helpful at some point to define a primed version
`Matroid.closure' : ClosureOperator (Set α)` corresponding to choice (2).
Failing that, the `ClosureOperator`/`GaloisInsertion` API is still available on
the subtype `↑(Iic M.E)` via `Matroid.SubtypeClosure`, albeit less elegantly.
-/

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y : Set α} {e f : α}

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
  refine subset_union_right.trans ((hFs i).1 (X := Fs i ∪ X) hIJ ?_)
  convert hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

/-- The property of being a flat gives rise to a `ClosureOperator` on the subsets of `M.E`,
in which the `IsClosed` sets correspond to `Flat`s.
(We can't define such an operator on all of `Set α`,
since this would incorrectly force `univ` to always be a flat.) -/
def subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E) :=
  ClosureOperator.ofCompletePred (fun F ↦ M.Flat F.1) fun s hs ↦ by
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

@[simp] lemma ground_subset_closure_iff : M.E ⊆ M.closure X ↔ M.closure X = M.E := by
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

section Indep

variable {ι : Sort*} {I J B : Set α} {x y : α}

lemma Indep.closure_eq_setOf_basis_insert (hI : M.Indep I) :
    M.closure I = {x | M.Basis I (insert x I)} := by
  set F := {x | M.Basis I (insert x I)}
  have hIF : M.Basis I F := hI.basis_setOf_insert_basis

  have hF : M.Flat F := by
    refine ⟨fun J X hJF hJX e heX ↦ show M.Basis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.basis_of_basis_of_subset_of_subset (hJX.basis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).basis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))

  rw [subset_antisymm_iff, closure_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.Basis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

lemma Indep.insert_basis_iff_mem_closure (hI : M.Indep I) :
    M.Basis I (insert e I) ↔ e ∈ M.closure I := by
  rw [hI.closure_eq_setOf_basis_insert, mem_setOf]

lemma Indep.basis_closure (hI : M.Indep I) : M.Basis I (M.closure I) := by
  rw [hI.closure_eq_setOf_basis_insert]; exact hI.basis_setOf_insert_basis

lemma Basis.closure_eq_closure (h : M.Basis I X) : M.closure I = M.closure X := by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I, h.indep.closure_eq_setOf_basis_insert]
  exact M.closure_subset_closure fun e he ↦ (h.basis_subset (subset_insert _ _)
    (insert_subset he h.subset))

lemma Basis.closure_eq_right (h : M.Basis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure

lemma Basis'.closure_eq_closure (h : M.Basis' I X) : M.closure I = M.closure X := by
  rw [← closure_inter_ground _ X, h.basis_inter_ground.closure_eq_closure]

lemma Basis.subset_closure (h : M.Basis I X) : X ⊆ M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure, h.closure_eq_closure]

lemma Basis'.basis_closure_right (h : M.Basis' I X) : M.Basis I (M.closure X) := by
  rw [← h.closure_eq_closure]; exact h.indep.basis_closure

lemma Basis.basis_closure_right (h : M.Basis I X) : M.Basis I (M.closure X) :=
  h.basis'.basis_closure_right

lemma Indep.mem_closure_iff (hI : M.Indep I) :
    x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I := by
  rwa [hI.closure_eq_setOf_basis_insert, mem_setOf, basis_insert_iff]

lemma Indep.mem_closure_iff' (hI : M.Indep I) :
    x ∈ M.closure I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I) := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground,
    imp_iff_not_or]
  have := hI.subset_ground
  aesop

lemma Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e ∈ M.closure I \ I := by
  rw [mem_diff, hI.mem_closure_iff, or_and_right, and_not_self_iff, or_false,
    iff_self_and, imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

lemma Indep.mem_closure_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.closure I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_diff, and_iff_left heI]

lemma Indep.not_mem_closure_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) :
    e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_right he,
    and_iff_left hI.subset_ground]; tauto

lemma Indep.not_mem_closure_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I)
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.closure I ↔ M.Indep (insert e I) := by
  rw [hI.not_mem_closure_iff, and_iff_left heI]

lemma Indep.insert_indep_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I := by
  rw [mem_diff, hI.mem_closure_iff_of_not_mem heI, dep_iff, not_and, not_imp_not, insert_subset_iff,
    and_iff_left hI.subset_ground]
  exact ⟨fun h ↦ ⟨h.subset_ground (mem_insert e I), fun _ ↦ h⟩, fun h ↦ h.2 h.1⟩

lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I := by
  obtain (h | h) := em (e ∈ I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_not_mem h, or_iff_left h]

lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I → e ∈ M.E \ M.closure I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI <| h.subset <| subset_insert _ _]

/-- This can be used for rewriting if the LHS is inside a binder and whether `f = e` is unknown.-/
lemma Indep.insert_diff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I := by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_diff_singleton_comm hne.symm, hI.insert_indep_iff, mem_diff_singleton,
    and_iff_left hne.symm]

lemma Indep.basis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : X ⊆ M.closure I) : M.Basis I X :=
  hI.basis_closure.basis_subset hIX hXI

lemma basis_iff_indep_subset_closure : M.Basis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h ↦ h.1.basis_of_subset_of_subset_closure h.2.1 h.2.2⟩

lemma Indep.base_of_ground_subset_closure (hI : M.Indep I) (h : M.E ⊆ M.closure I) : M.Base I := by
  rw [← basis_ground_iff]; exact hI.basis_of_subset_of_subset_closure hI.subset_ground h

lemma Base.closure_eq (hB : M.Base B) : M.closure B = M.E := by
  rw [← basis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

lemma Base.closure_of_superset (hB : M.Base B) (hBX : B ⊆ X) : M.closure X = M.E :=
  (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

lemma base_iff_indep_closure_eq : M.Base B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← basis_ground_iff, basis_iff_indep_subset_closure, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.closure_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

lemma Indep.base_iff_ground_subset_closure (hI : M.Indep I) : M.Base I ↔ M.E ⊆ M.closure I :=
  ⟨fun h ↦ h.closure_eq.symm.subset, hI.base_of_ground_subset_closure⟩

lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) :
    M.closure J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.basis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

/-- For a nonempty collection of subsets of a given independent set,
the closure of the intersection is the intersection of the closure. -/
lemma Indep.closure_sInter_eq_biInter_closure_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.closure (⋂₀ Js) = (⋂ J ∈ Js, M.closure J)  := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine ⟨ fun X hX ↦ M.closure_subset_closure (sInter_subset_of_mem hX),
    fun e he ↦ by_contra fun he' ↦ ?_⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I := by
    refine ⟨M.closure_subset_ground _ (he _ hne.some_mem), fun heI ↦ he' ?_⟩
    refine mem_closure_of_mem _ (fun X hX' ↦ ?_) hiI.subset_ground
    rw [← hI.closure_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩

  rw [hiI.not_mem_closure_iff_of_not_mem (not_mem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_basis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)

  have hIb : M.Basis I (insert e I) := by
    rw [hI.insert_basis_iff_mem_closure]
    exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)

  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_basis (hfb.basis_subset (insert_subset hfIJ.1
    (by (rw [diff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))

  refine hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ ?_))

  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_closure_iff).mp (he _ hX')
  · refine (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) ?_)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union, ← diff_subset_iff, diff_singleton_eq_self hfX] at hIs
    exact hIs.trans diff_subset
  exact heEI.2 (hIs _ hX' heX)

lemma closure_iInter_eq_iInter_closure_of_iUnion_indep [hι : Nonempty ι] (Is : ι → Set α)
    (h : M.Indep (⋃ i, Is i)) : M.closure (⋂ i, Is i) = (⋂ i, M.closure (Is i)) := by
  convert h.closure_sInter_eq_biInter_closure_of_forall_subset (range_nonempty Is)
    (by simp [subset_iUnion])
  simp

lemma closure_sInter_eq_biInter_closure_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) :  M.closure (⋂₀ Is) = (⋂ I ∈ Is, M.closure I) :=
  h.closure_sInter_eq_biInter_closure_of_forall_subset hIs (fun _ ↦ subset_sUnion_of_mem)

lemma closure_biInter_eq_biInter_closure_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι → Set α} (h : M.Indep (⋃ i ∈ A, I i)) :
    M.closure (⋂ i ∈ A, I i) = ⋂ i ∈ A, M.closure (I i) := by
  have := hA.coe_sort
  convert closure_iInter_eq_iInter_closure_of_iUnion_indep (Is := fun i : A ↦ I i) (by simpa) <;>
  simp

lemma Indep.closure_iInter_eq_biInter_closure_of_forall_subset [Nonempty ι] {Js : ι → Set α}
    (hI : M.Indep I) (hJs : ∀ i, Js i ⊆ I) : M.closure (⋂ i, Js i) = ⋂ i, M.closure (Js i) :=
  closure_iInter_eq_iInter_closure_of_iUnion_indep _ (hI.subset <| by simpa)

lemma Indep.closure_inter_eq_inter_closure (h : M.Indep (I ∪ J)) :
    M.closure (I ∩ J) = M.closure I ∩ M.closure J := by
  rw [inter_eq_iInter, closure_iInter_eq_iInter_closure_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

lemma basis_iff_basis_closure_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ M.Basis I (M.closure X) :=
  ⟨fun h ↦ h.basis_closure_right, fun h ↦ h.basis_subset hIX (M.subset_closure X hX)⟩

lemma basis_iff_basis_closure_of_subset' (hIX : I ⊆ X) :
    M.Basis I X ↔ M.Basis I (M.closure X) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.basis_closure_right, h.subset_ground⟩,
    fun h ↦ h.1.basis_subset hIX (M.subset_closure X h.2)⟩

lemma basis'_iff_basis_closure : M.Basis' I X ↔ M.Basis I (M.closure X) ∧ I ⊆ X := by
  rw [← closure_inter_ground, basis'_iff_basis_inter_ground]
  exact ⟨fun h ↦ ⟨h.basis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h ↦ h.1.basis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩

lemma exists_basis_inter_ground_basis_closure (M : Matroid α) (X : Set α) :
    ∃ I, M.Basis I (X ∩ M.E) ∧ M.Basis I (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  have hI' := hI.basis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

lemma Basis.basis_of_closure_eq_closure (hI : M.Basis I X) (hY : I ⊆ Y)
    (h : M.closure X = M.closure Y) (hYE : Y ⊆ M.E := by aesop_mat) : M.Basis I Y := by
  refine hI.indep.basis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure, h]
  exact M.subset_closure Y

lemma basis_union_iff_indep_closure : M.Basis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ ↦
    hI.basis_closure.basis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

lemma basis_iff_indep_closure : M.Basis I X ↔ M.Indep I ∧ X ⊆ M.closure I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_closure, h.subset⟩, fun h ↦
    (basis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 subset_union_right⟩

lemma Basis.eq_of_closure_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.closure J) :
    J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

@[simp] lemma empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.closure ∅ := by
  rw [basis_iff_indep_closure, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]

lemma indep_iff_forall_not_mem_closure_diff (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_diff_singleton hJ.subset heJ))

/-- An alternative version of `Matroid.indep_iff_forall_not_mem_closure_diff` where the
hypothesis that `I ⊆ M.E` is contained in the RHS rather than the hypothesis. -/
lemma indep_iff_forall_not_mem_closure_diff' :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_forall_not_mem_closure_diff h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_forall_not_mem_closure_diff h.1).mpr h.2⟩

lemma Indep.not_mem_closure_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_forall_not_mem_closure_diff'.1 hI).2 e he

lemma indep_iff_forall_closure_diff_ne :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → M.closure (I \ {e}) ≠ M.closure I := by
  rw [indep_iff_forall_not_mem_closure_diff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h heI ?_,fun e heI hin ↦ h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_diff_distrib_left,
      inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, closure_inter_ground]
  nth_rw 2 [show I = insert e (I \ {e}) by simp [heI]]
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem hin, closure_closure]

lemma Indep.closure_ssubset_closure (hI : M.Indep I) (hJI : J ⊂ I) : M.closure J ⊂ M.closure I := by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
  exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss ↦ heJ <|
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩

lemma indep_iff_forall_closure_ssubset_of_ssubset (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃J⦄, J ⊂ I → M.closure J ⊂ M.closure I := by
  refine ⟨fun h _ ↦ h.closure_ssubset_closure,
    fun h ↦ (indep_iff_forall_not_mem_closure_diff hI).2 fun e heI hecl ↦ ?_⟩
  refine (h (diff_singleton_sSubset.2 heI)).ne ?_
  rw [show I = insert e (I \ {e}) by simp [heI], ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hecl]
  simp

lemma Indep.closure_diff_ssubset (hI : M.Indep I) (hX : (I ∩ X).Nonempty) :
    M.closure (I \ X) ⊂ M.closure I := by
  refine hI.closure_ssubset_closure <| diff_subset.ssubset_of_ne fun h ↦ ?_
  rw [sdiff_eq_left, disjoint_iff_inter_eq_empty] at h
  simp [h] at hX

lemma Indep.closure_diff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
  hI.closure_ssubset_closure <| by simpa

end Indep

section insert

lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e ∈ M.closure (insert f X)) :
    f ∈ M.closure (insert e X) := by
  rw [← closure_inter_ground] at *
  have hfE : f ∈ M.E := by
    by_contra! hfE; rw [insert_inter_of_not_mem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.closure_eq_closure, hI.indep.not_mem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    closure_insert_closure_eq_closure_insert, he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm,
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_closure_iff, or_iff_right (h.not_dep), mem_insert_iff,
    or_iff_left he.2] at hef
  subst hef; apply mem_insert

lemma closure_exchange (he : e ∈ M.closure (insert f X) \ M.closure X) :
    f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf ↦ by
    rwa [closure_insert_eq_of_mem_closure hf, diff_self, iff_false_intro (not_mem_empty _)] at he⟩

lemma closure_exchange_iff :
    e ∈ M.closure (insert f X) \ M.closure X ↔ f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩

lemma closure_insert_congr (he : e ∈ M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  have hf := closure_exchange he
  rw [eq_comm, ← closure_closure, ← insert_eq_of_mem he.1, closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_closure, ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hf.1, closure_closure, closure_closure]

lemma closure_diff_eq_self (h : Y ⊆ M.closure (X \ Y)) : M.closure (X \ Y) = M.closure X := by
  rw [← diff_union_inter X Y, ← closure_union_closure_left_eq,
    union_eq_self_of_subset_right (inter_subset_right.trans h), closure_closure, diff_union_inter]

lemma closure_diff_singleton_eq_closure (h : e ∈ M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X :=
  closure_diff_eq_self (by simpa)

lemma subset_closure_diff_iff_closure_eq (h : Y ⊆ X) (hY : Y ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure (X \ Y) ↔ M.closure (X \ Y) = M.closure X :=
  ⟨closure_diff_eq_self, fun h' ↦ (M.subset_closure_of_subset' h).trans h'.symm.subset⟩

lemma mem_closure_diff_singleton_iff_closure (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X := by
  simpa using subset_closure_diff_iff_closure_eq (Y := {e}) (X := X) (by simpa)

end insert

lemma ext_closure {M₁ M₂ : Matroid α} (h : ∀ X, M₁.closure X = M₂.closure X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_forall_closure_diff_ne, h])

end Matroid
