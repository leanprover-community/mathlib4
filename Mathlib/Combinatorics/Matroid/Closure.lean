/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Order.Closure
import Mathlib.Order.CompleteLatticeIntervals

/-!
# Matroid Closure

A flat (`IsFlat`) of a matroid `M` is a combinatorial analogue of a subspace of a vector space,
and is defined to be a subset `F` of the ground set of `M` such that for each basis
`I` for `F`, every set having `I` as a basis is contained in `F`.

The *closure* of a set `X` in a matroid `M` is the intersection of all flats of `M` containing `X`.
This is a combinatorial analogue of the linear span of a set of vectors.

For `M : Matroid α`, this file defines a predicate `M.IsFlat : Set α → Prop` and a function
`M.closure : Set α → Set α` corresponding to these notions, and develops API for the latter.
API for `Matroid.IsFlat` will appear in another file; we include the definition here since
it is used in the definition of `Matroid.closure`.

We also define a predicate `Spanning`, to describe a set whose closure is the entire ground set.

## Main definitions

* For `M : Matroid α` and `F : Set α`, `M.IsFlat F` means that `F` is a isFlat of `M`.
* For `M : Matroid α` and `X : Set α`, `M.closure X` is the closure of `X` in `M`.
* For `M : Matroid α` and `X : ↑(Iic M.E)` (i.e. a bundled subset of `M.E`),
  `M.subtypeClosure X` is the closure of `X`, viewed as a term in `↑(Iic M.E)`.
  This is a `ClosureOperator` on `↑(Iic M.E)`.
* For `M : Matroid α` and `S ⊆ M.E`, `M.Spanning S` means that `S` has closure equal to `M.E`,
  or equivalently that `S` contains a isBase of `M`.

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
This also relates to flats; `F ⊆ M.E ∧ ClosureOperator.IsClosed F` is equivalent to `M.IsFlat F`.
(All of this fails for choice (1), since `X ⊆ M.closure X` is required for
a `ClosureOperator`, but isn't true for non-subsets of `M.E`)

The API that choice (2) would offer is very beguiling, but after extensive experimentation in
an external repo, it seems that (1) is far less rough around the edges in practice,
so we go with (1). It may be helpful at some point to define a primed version
`Matroid.closure' : ClosureOperator (Set α)` corresponding to choice (2).
Failing that, the `ClosureOperator`/`GaloisInsertion` API is still available on
the subtype `↑(Iic M.E)` via `Matroid.SubtypeClosure`, albeit less elegantly.

## Naming conventions

In lemma names, the words `spanning` and `isFlat` are used as suffixes,
for instance we have `ground_spanning` rather than `spanning_ground`.
-/

assert_not_exists Field

open Set
namespace Matroid

variable {ι α : Type*} {M : Matroid α} {F X Y : Set α} {e f : α}

section IsFlat

/-- A flat is a maximal set having a given basis -/
@[mk_iff]
structure IsFlat (M : Matroid α) (F : Set α) : Prop where
  subset_of_isBasis_of_isBasis : ∀ ⦃I X⦄, M.IsBasis I F → M.IsBasis I X → X ⊆ F
  subset_ground : F ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsFlat.subset_ground

@[simp] lemma ground_isFlat (M : Matroid α) : M.IsFlat M.E :=
  ⟨fun _ _ _ ↦ IsBasis.subset_ground, Subset.rfl⟩

lemma IsFlat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.IsFlat (Fs i)) : M.IsFlat (⋂ i, Fs i) := by
  refine ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ ?_,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_isBasis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine subset_union_right.trans ((hFs i).1 (X := Fs i ∪ X) hIJ ?_)
  convert hIJ.isBasis_union (hIX.isBasis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

/-- The property of being a flat gives rise to a `ClosureOperator` on the subsets of `M.E`,
in which the `IsClosed` sets correspond to flats.
(We can't define such an operator on all of `Set α`,
since this would incorrectly force `univ` to always be a flat.) -/
def subtypeClosure (M : Matroid α) : ClosureOperator (Iic M.E) :=
  ClosureOperator.ofCompletePred (fun F ↦ M.IsFlat F.1) fun s hs ↦ by
    obtain (rfl | hne) := s.eq_empty_or_nonempty
    · simp
    have _ := hne.coe_sort
    convert IsFlat.iInter (M := M) (Fs := fun (F : s) ↦ F.1.1) (fun F ↦ hs F.1 F.2)
    ext
    aesop

lemma isFlat_iff_isClosed : M.IsFlat F ↔ ∃ h : F ⊆ M.E, M.subtypeClosure.IsClosed ⟨F, h⟩ := by
  simpa [subtypeClosure] using IsFlat.subset_ground

lemma isClosed_iff_isFlat {F : Iic M.E} : M.subtypeClosure.IsClosed F ↔ M.IsFlat F := by
  simp [subtypeClosure]

end IsFlat

/-- The closure of `X ⊆ M.E` is the intersection of all the flats of `M` containing `X`.
A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.closure X := M.closure (X ∩ M.E)`. -/
def closure (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F}

lemma closure_def (M : Matroid α) (X : Set α) : M.closure X = ⋂₀ {F | M.IsFlat F ∧ X ∩ M.E ⊆ F} :=
  rfl

lemma closure_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {F | M.IsFlat F ∧ X ⊆ F} := by
  rw [closure, inter_eq_self_of_subset_left hX]

instance : Nonempty {F | M.IsFlat F ∧ X ∩ M.E ⊆ F} := ⟨M.E, M.ground_isFlat, inter_subset_right⟩

lemma closure_eq_subtypeClosure (M : Matroid α) (X : Set α) :
    M.closure X = M.subtypeClosure ⟨X ∩ M.E, inter_subset_right⟩  := by
  suffices ∀ (x : α), (∀ (t : Set α), M.IsFlat t → X ∩ M.E ⊆ t → x ∈ t) ↔
    (x ∈ M.E ∧ ∀ a ⊆ M.E, X ∩ M.E ⊆ a → M.IsFlat a → x ∈ a) by
    simpa [closure, subtypeClosure, Set.ext_iff]
  exact fun x ↦ ⟨fun h ↦ ⟨h _ M.ground_isFlat inter_subset_right, fun F _ hXF hF ↦ h F hF hXF⟩,
    fun ⟨_, h⟩ F hF hXF ↦ h F hF.subset_ground hXF hF⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma closure_subset_ground (M : Matroid α) (X : Set α) : M.closure X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_isFlat, inter_subset_right⟩

@[simp] lemma ground_subset_closure_iff : M.E ⊆ M.closure X ↔ M.closure X = M.E := by
  simp [M.closure_subset_ground X, subset_antisymm_iff]

@[simp] lemma closure_inter_ground (M : Matroid α) (X : Set α) :
    M.closure (X ∩ M.E) = M.closure X := by
  simp_rw [closure_def, inter_assoc, inter_self]

lemma inter_ground_subset_closure (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.closure X := by
  simp_rw [closure_def, subset_sInter_iff]; simp

lemma mem_closure_iff_forall_mem_isFlat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.closure X ↔ ∀ F, M.IsFlat F → X ⊆ F → e ∈ F := by
  simp_rw [M.closure_def' X, mem_sInter, mem_setOf, and_imp]

lemma subset_closure_iff_forall_subset_isFlat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.closure X ↔ ∀ F, M.IsFlat F → X ⊆ F → Y ⊆ F := by
  simp_rw [M.closure_def' X, subset_sInter_iff, mem_setOf, and_imp]

lemma subset_closure (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.closure X := by
  simp [M.closure_def' X, subset_sInter_iff]

lemma IsFlat.closure (hF : M.IsFlat F) : M.closure F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_closure F)

variable (X) in
@[simp] lemma isFlat_closure : M.IsFlat (M.closure X) := by
  rw [closure, sInter_eq_iInter]; exact .iInter (·.2.1)

lemma isFlat_iff_closure_eq : M.IsFlat F ↔ M.closure F = F := ⟨(·.closure), (· ▸ isFlat_closure F)⟩

@[simp] lemma closure_ground (M : Matroid α) : M.closure M.E = M.E :=
  (M.closure_subset_ground M.E).antisymm (M.subset_closure M.E)

@[simp] lemma closure_univ (M : Matroid α) : M.closure univ = M.E := by
  rw [← closure_inter_ground, univ_inter, closure_ground]

@[gcongr]
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

lemma notMem_of_mem_diff_closure (he : e ∈ M.E \ M.closure X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_closure_of_mem' heX he.1

@[deprecated (since := "2025-05-23")]
alias not_mem_of_mem_diff_closure := notMem_of_mem_diff_closure

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

lemma closure_union_congr_left {X' : Set α} (h : M.closure X = M.closure X') :
    M.closure (X ∪ Y) = M.closure (X' ∪ Y) := by
  rw [← M.closure_union_closure_left_eq, h, M.closure_union_closure_left_eq]

lemma closure_union_congr_right {Y' : Set α} (h : M.closure Y = M.closure Y') :
    M.closure (X ∪ Y) = M.closure (X ∪ Y') := by
  rw [← M.closure_union_closure_right_eq, h, M.closure_union_closure_right_eq]

lemma closure_insert_congr_right (h : M.closure X = M.closure Y) :
    M.closure (insert e X) = M.closure (insert e Y) := by
  simp [← union_singleton, closure_union_congr_left h]

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

variable {ι : Sort*} {I J B : Set α} {x : α}

lemma Indep.closure_eq_setOf_isBasis_insert (hI : M.Indep I) :
    M.closure I = {x | M.IsBasis I (insert x I)} := by
  set F := {x | M.IsBasis I (insert x I)}
  have hIF : M.IsBasis I F := hI.isBasis_setOf_insert_isBasis
  have hF : M.IsFlat F := by
    refine ⟨fun J X hJF hJX e heX ↦ show M.IsBasis _ _ from ?_, hIF.subset_ground⟩
    exact (hIF.isBasis_of_isBasis_of_subset_of_subset (hJX.isBasis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).isBasis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))
  rw [subset_antisymm_iff, closure_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.IsBasis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.isBasis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

lemma Indep.insert_isBasis_iff_mem_closure (hI : M.Indep I) :
    M.IsBasis I (insert e I) ↔ e ∈ M.closure I := by
  rw [hI.closure_eq_setOf_isBasis_insert, mem_setOf]

lemma Indep.isBasis_closure (hI : M.Indep I) : M.IsBasis I (M.closure I) := by
  rw [hI.closure_eq_setOf_isBasis_insert]; exact hI.isBasis_setOf_insert_isBasis

lemma IsBasis.closure_eq_closure (h : M.IsBasis I X) : M.closure I = M.closure X := by
  refine subset_antisymm (M.closure_subset_closure h.subset) ?_
  rw [← M.closure_closure I, h.indep.closure_eq_setOf_isBasis_insert]
  exact M.closure_subset_closure fun e he ↦ (h.isBasis_subset (subset_insert _ _)
    (insert_subset he h.subset))

lemma IsBasis.closure_eq_right (h : M.IsBasis I (M.closure X)) : M.closure I = M.closure X :=
  M.closure_closure X ▸ h.closure_eq_closure

lemma IsBasis'.closure_eq_closure (h : M.IsBasis' I X) : M.closure I = M.closure X := by
  rw [← closure_inter_ground _ X, h.isBasis_inter_ground.closure_eq_closure]

lemma IsBasis.subset_closure (h : M.IsBasis I X) : X ⊆ M.closure I := by
  rw [← closure_subset_closure_iff_subset_closure, h.closure_eq_closure]

lemma IsBasis'.isBasis_closure_right (h : M.IsBasis' I X) : M.IsBasis I (M.closure X) := by
  rw [← h.closure_eq_closure]; exact h.indep.isBasis_closure

lemma IsBasis.isBasis_closure_right (h : M.IsBasis I X) : M.IsBasis I (M.closure X) :=
  h.isBasis'.isBasis_closure_right

lemma Indep.mem_closure_iff (hI : M.Indep I) :
    x ∈ M.closure I ↔ M.Dep (insert x I) ∨ x ∈ I := by
  rwa [hI.closure_eq_setOf_isBasis_insert, mem_setOf, isBasis_insert_iff]

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

lemma Indep.mem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.closure I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_diff, and_iff_left heI]

@[deprecated (since := "2025-05-23")]
alias Indep.mem_closure_iff_of_not_mem := Indep.mem_closure_iff_of_notMem

lemma Indep.notMem_closure_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) :
    e ∉ M.closure I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_closure_iff, dep_iff, insert_subset_iff, and_iff_right he,
    and_iff_left hI.subset_ground]; tauto

@[deprecated (since := "2025-05-23")] alias Indep.not_mem_closure_iff := Indep.notMem_closure_iff

lemma Indep.notMem_closure_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I)
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.closure I ↔ M.Indep (insert e I) := by
  rw [hI.notMem_closure_iff, and_iff_left heI]

@[deprecated (since := "2025-05-23")]
alias Indep.not_mem_closure_iff_of_not_mem := Indep.notMem_closure_iff_of_notMem

lemma Indep.insert_indep_iff_of_notMem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I := by
  rw [mem_diff, hI.mem_closure_iff_of_notMem heI, dep_iff, not_and, not_imp_not, insert_subset_iff,
    and_iff_left hI.subset_ground]
  exact ⟨fun h ↦ ⟨h.subset_ground (mem_insert e I), fun _ ↦ h⟩, fun h ↦ h.2 h.1⟩

@[deprecated (since := "2025-05-23")]
alias Indep.insert_indep_iff_of_not_mem := Indep.insert_indep_iff_of_notMem

lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.closure I ∨ e ∈ I := by
  obtain (h | h) := em (e ∈ I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_notMem h, or_iff_left h]

lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I → e ∈ M.E \ M.closure I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI <| h.subset <| subset_insert _ _]

/-- This can be used for rewriting if the LHS is inside a binder and it is unknown
whether `f = e`. -/
lemma Indep.insert_diff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.closure (I \ {e}) ∨ f ∈ I := by
  obtain rfl | hne := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_diff_singleton_comm hne.symm, hI.insert_indep_iff, mem_diff_singleton,
    and_iff_left hne.symm]

lemma Indep.isBasis_of_subset_of_subset_closure (hI : M.Indep I) (hIX : I ⊆ X)
    (hXI : X ⊆ M.closure I) : M.IsBasis I X :=
  hI.isBasis_closure.isBasis_subset hIX hXI

lemma isBasis_iff_indep_subset_closure : M.IsBasis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_closure⟩,
    fun h ↦ h.1.isBasis_of_subset_of_subset_closure h.2.1 h.2.2⟩

lemma Indep.isBase_of_ground_subset_closure (hI : M.Indep I) (h : M.E ⊆ M.closure I) :
    M.IsBase I := by
  rw [← isBasis_ground_iff]; exact hI.isBasis_of_subset_of_subset_closure hI.subset_ground h

lemma IsBase.closure_eq (hB : M.IsBase B) : M.closure B = M.E := by
  rw [← isBasis_ground_iff] at hB; rw [hB.closure_eq_closure, closure_ground]

lemma IsBase.closure_of_superset (hB : M.IsBase B) (hBX : B ⊆ X) : M.closure X = M.E :=
  (M.closure_subset_ground _).antisymm (hB.closure_eq ▸ M.closure_subset_closure hBX)

lemma isBase_iff_indep_closure_eq : M.IsBase B ↔ M.Indep B ∧ M.closure B = M.E := by
  rw [← isBasis_ground_iff, isBasis_iff_indep_subset_closure, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.closure_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_closure B).trans_eq h, h.symm.subset⟩⟩

lemma IsBase.exchange_base_of_notMem_closure (hB : M.IsBase B) (he : e ∈ B)
    (hf : f ∉ M.closure (B \ {e})) (hfE : f ∈ M.E := by aesop_mat) :
    M.IsBase (insert f (B \ {e})) := by
  obtain rfl | hne := eq_or_ne f e
  · simpa [he]
  have ⟨hi, hfB⟩ : M.Indep (insert f (B \ {e})) ∧ f ∉ B := by
    simpa [(hB.indep.diff _).notMem_closure_iff, hne] using hf
  exact hB.exchange_isBase_of_indep hfB hi

@[deprecated (since := "2025-05-23")]
alias IsBase.exchange_base_of_not_mem_closure := IsBase.exchange_base_of_notMem_closure

lemma Indep.isBase_iff_ground_subset_closure (hI : M.Indep I) : M.IsBase I ↔ M.E ⊆ M.closure I :=
  ⟨fun h ↦ h.closure_eq.symm.subset, hI.isBase_of_ground_subset_closure⟩

lemma Indep.closure_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) :
    M.closure J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_closure _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.isBasis_closure.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

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
  rw [hiI.notMem_closure_iff_of_notMem (notMem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_isBasis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)
  have hIb : M.IsBasis I (insert e I) := by
    rw [hI.insert_isBasis_iff_mem_closure]
    exact (M.closure_subset_closure (hIs _ hne.some_mem)) (he _ hne.some_mem)
  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_isBasis (hfb.isBasis_subset (insert_subset hfIJ.1
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

lemma Indep.inter_isBasis_biInter {ι : Type*} (hI : M.Indep I) {X : ι → Set α} {A : Set ι}
    (hA : A.Nonempty) (h : ∀ i ∈ A, M.IsBasis ((X i) ∩ I) (X i)) :
    M.IsBasis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  simp_rw [← biInter_inter hA,
  closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure

lemma Indep.inter_isBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.IsBasis ((X i) ∩ I) (X i)) : M.IsBasis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  convert hI.inter_isBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i ↦ X i.down)
    (by simpa using fun (i : PLift ι) ↦ h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm

lemma Indep.inter_isBasis_sInter {Xs : Set (Set α)} (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.IsBasis (X ∩ I) X) : M.IsBasis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.inter_isBasis_biInter hXs h

lemma isBasis_iff_isBasis_closure_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) :=
  ⟨fun h ↦ h.isBasis_closure_right, fun h ↦ h.isBasis_subset hIX (M.subset_closure X hX)⟩

lemma isBasis_iff_isBasis_closure_of_subset' (hIX : I ⊆ X) :
    M.IsBasis I X ↔ M.IsBasis I (M.closure X) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.isBasis_closure_right, h.subset_ground⟩,
    fun h ↦ h.1.isBasis_subset hIX (M.subset_closure X h.2)⟩

lemma isBasis'_iff_isBasis_closure : M.IsBasis' I X ↔ M.IsBasis I (M.closure X) ∧ I ⊆ X := by
  rw [← closure_inter_ground, isBasis'_iff_isBasis_inter_ground]
  exact ⟨fun h ↦ ⟨h.isBasis_closure_right, h.subset.trans inter_subset_left⟩,
    fun h ↦ h.1.isBasis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_closure _)⟩

lemma exists_isBasis_inter_ground_isBasis_closure (M : Matroid α) (X : Set α) :
    ∃ I, M.IsBasis I (X ∩ M.E) ∧ M.IsBasis I (M.closure X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  have hI' := hI.isBasis_closure_right; rw [closure_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

lemma IsBasis.isBasis_of_closure_eq_closure (hI : M.IsBasis I X) (hY : I ⊆ Y)
    (h : M.closure X = M.closure Y) (hYE : Y ⊆ M.E := by aesop_mat) : M.IsBasis I Y := by
  refine hI.indep.isBasis_of_subset_of_subset_closure hY ?_
  rw [hI.closure_eq_closure, h]
  exact M.subset_closure Y

lemma isBasis_union_iff_indep_closure : M.IsBasis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.closure I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_closure⟩, fun ⟨hI, hXI⟩ ↦
    hI.isBasis_closure.isBasis_subset subset_union_left (union_subset (M.subset_closure I) hXI)⟩

lemma isBasis_iff_indep_closure : M.IsBasis I X ↔ M.Indep I ∧ X ⊆ M.closure I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_closure, h.subset⟩, fun h ↦
    (isBasis_union_iff_indep_closure.mpr ⟨h.1, h.2.1⟩).isBasis_subset h.2.2 subset_union_right⟩

lemma Indep.inter_isBasis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.IsBasis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I) :=
  ⟨IsBasis.subset_closure, (hI.inter_left X).isBasis_of_subset_of_subset_closure inter_subset_left⟩

lemma IsBasis.closure_inter_isBasis_closure (h : M.IsBasis (X ∩ I) X) (hI : M.Indep I) :
    M.IsBasis (M.closure X ∩ I) (M.closure X) := by
  rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

lemma IsBasis.eq_of_closure_subset (hI : M.IsBasis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.closure J) :
    J = I := by
  rw [← hI.indep.closure_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

lemma IsBasis.insert_isBasis_insert_of_notMem_closure (hIX : M.IsBasis I X) (heI : e ∉ M.closure I)
    (heE : e ∈ M.E := by aesop_mat) : M.IsBasis (insert e I) (insert e X) :=
  hIX.insert_isBasis_insert <| hIX.indep.insert_indep_iff.2 <| .inl ⟨heE, heI⟩

@[deprecated (since := "2025-05-23")]
alias IsBasis.insert_isBasis_insert_of_not_mem_closure :=
  IsBasis.insert_isBasis_insert_of_notMem_closure

@[simp] lemma empty_isBasis_iff : M.IsBasis ∅ X ↔ X ⊆ M.closure ∅ := by
  rw [isBasis_iff_indep_closure, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]

lemma indep_iff_forall_notMem_closure_diff (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_isBasis I
  convert hJ.indep
  refine hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_diff_singleton hJ.subset heJ))

@[deprecated (since := "2025-05-23")]
alias indep_iff_forall_not_mem_closure_diff := indep_iff_forall_notMem_closure_diff

/-- An alternative version of `Matroid.indep_iff_forall_notMem_closure_diff` where the
hypothesis that `I ⊆ M.E` is contained in the RHS rather than the hypothesis. -/
lemma indep_iff_forall_notMem_closure_diff' :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_forall_notMem_closure_diff h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_forall_notMem_closure_diff h.1).mpr h.2⟩

@[deprecated (since := "2025-05-23")]
alias indep_iff_forall_not_mem_closure_diff' := indep_iff_forall_notMem_closure_diff'

lemma Indep.notMem_closure_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_forall_notMem_closure_diff'.1 hI).2 e he

@[deprecated (since := "2025-05-23")]
alias Indep.not_mem_closure_diff_of_mem := Indep.notMem_closure_diff_of_mem

lemma indep_iff_forall_closure_diff_ne :
    M.Indep I ↔ ∀ ⦃e⦄, e ∈ I → M.closure (I \ {e}) ≠ M.closure I := by
  rw [indep_iff_forall_notMem_closure_diff']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h heI ?_,fun e heI hin ↦ h heI ?_⟩⟩
  · rw [← closure_inter_ground, inter_comm, inter_diff_distrib_left,
      inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, closure_inter_ground]
  nth_rw 2 [show I = insert e (I \ {e}) by simp [heI]]
  rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem hin, closure_closure]

lemma Indep.union_indep_iff_forall_notMem_closure_right (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I ∪ J) ↔ ∀ e ∈ J \ I, e ∉ M.closure (I ∪ (J \ {e})) := by
  refine ⟨fun h e heJ hecl ↦ h.notMem_closure_diff_of_mem (.inr heJ.1) ?_, fun h ↦ ?_⟩
  · rwa [union_diff_distrib, diff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_isBasis_of_subset (show I ⊆ I ∪ J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_ssubset
  · exact hKIJ.indep
  exfalso
  obtain ⟨e, heI, heK⟩ := exists_of_ssubset hssu
  have heJI : e ∈ J \ I := by
    rw [← union_diff_right, union_comm]
    exact ⟨heI, notMem_subset hK heK⟩
  refine h _ heJI ?_
  rw [← diff_singleton_eq_self heJI.2, ← union_diff_distrib]
  exact M.closure_subset_closure (subset_diff_singleton hKIJ.subset heK) <| hKIJ.subset_closure heI

@[deprecated (since := "2025-05-23")]
alias Indep.union_indep_iff_forall_not_mem_closure_right :=
  Indep.union_indep_iff_forall_notMem_closure_right

lemma Indep.union_indep_iff_forall_notMem_closure_left (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I ∪ J) ↔ ∀ e ∈ I \ J, e ∉ M.closure ((I \ {e}) ∪ J) := by
  simp_rw [union_comm I J, hJ.union_indep_iff_forall_notMem_closure_right hI, union_comm]

@[deprecated (since := "2025-05-23")]
alias Indep.union_indep_iff_forall_not_mem_closure_left :=
  Indep.union_indep_iff_forall_notMem_closure_left

lemma Indep.closure_ssubset_closure (hI : M.Indep I) (hJI : J ⊂ I) : M.closure J ⊂ M.closure I := by
  obtain ⟨e, heI, heJ⟩ := exists_of_ssubset hJI
  exact (M.closure_subset_closure hJI.subset).ssubset_of_not_subset fun hss ↦ heJ <|
    (hI.closure_inter_eq_self_of_subset hJI.subset).subset ⟨hss (M.mem_closure_of_mem heI), heI⟩

lemma indep_iff_forall_closure_ssubset_of_ssubset (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ ⦃J⦄, J ⊂ I → M.closure J ⊂ M.closure I := by
  refine ⟨fun h _ ↦ h.closure_ssubset_closure,
    fun h ↦ (indep_iff_forall_notMem_closure_diff hI).2 fun e heI hecl ↦ ?_⟩
  refine (h (diff_singleton_ssubset.2 heI)).ne ?_
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
    by_contra! hfE; rw [insert_inter_of_notMem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ M.E)
  rw [← hI.closure_eq_closure, hI.indep.notMem_closure_iff] at he
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
    rwa [closure_insert_eq_of_mem_closure hf, diff_self, iff_false_intro (notMem_empty _)] at he⟩

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
  ext_indep (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_forall_closure_diff_ne, h])


section Spanning

variable {S T I B : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
a base of `M`. -/
@[mk_iff]
structure Spanning (M : Matroid α) (S : Set α) : Prop where
  closure_eq : M.closure S = M.E
  subset_ground : S ⊆ M.E

attribute [aesop unsafe 10% (rule_sets := [Matroid])] Spanning.subset_ground

lemma spanning_iff_closure_eq (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.closure S = M.E := by
  rw [spanning_iff, and_iff_left hS]

@[simp] lemma closure_spanning_iff (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure_eq, closure_closure, ← spanning_iff_closure_eq]

lemma spanning_iff_ground_subset_closure (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.closure S := by
  rw [spanning_iff_closure_eq, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]

lemma not_spanning_iff_closure_ssubset (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure_eq, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

lemma Spanning.closure_eq_of_superset (hS : M.Spanning S) (hST : S ⊆ T) : M.closure T = M.E := by
  rw [← closure_inter_ground, ← spanning_iff_closure_eq]
  exact hS.superset (subset_inter hST hS.subset_ground)

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) : M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma IsBase.spanning (hB : M.IsBase B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩

lemma IsBase.spanning_of_superset (hB : M.IsBase B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

/-- A version of `Matroid.spanning_iff_exists_isBase_subset` in which the `S ⊆ M.E` condition
appears in the RHS of the equivalence rather than as a hypothesis. -/
lemma spanning_iff_exists_isBase_subset' : M.Spanning S ↔ (∃ B, M.IsBase B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine ⟨fun h ↦ ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_isBasis S
  have hB' := hB.isBasis_closure_right
  rw [h.closure_eq, isBasis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

lemma spanning_iff_exists_isBase_subset (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.IsBase B ∧ B ⊆ S := by
  rw [spanning_iff_exists_isBase_subset', and_iff_left hS]

lemma Spanning.exists_isBase_subset (hS : M.Spanning S) : ∃ B, M.IsBase B ∧ B ⊆ S := by
  rwa [spanning_iff_exists_isBase_subset] at hS

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_exists_isBase_subset]

lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, diff_diff_cancel_left hS]

lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

lemma coindep_iff_closure_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_closure_eq]

lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

lemma Indep.isBase_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.IsBase I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_isBase_subset; rwa [← hB.eq_of_subset_indep hI hBI]

lemma Spanning.isBase_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.IsBase I :=
  hI.isBase_of_spanning hIs

lemma Indep.eq_of_spanning_subset (hI : M.Indep I) (hS : M.Spanning S) (hSI : S ⊆ I) : S = I :=
  ((hI.subset hSI).isBase_of_spanning hS).eq_of_subset_indep hI hSI

lemma IsBasis.spanning_iff_spanning (hIX : M.IsBasis I X) : M.Spanning I ↔ M.Spanning X := by
  rw [spanning_iff_closure_eq, spanning_iff_closure_eq, hIX.closure_eq_closure]

lemma Spanning.isBase_restrict_iff (hS : M.Spanning S) : (M ↾ S).IsBase B ↔ M.IsBase B ∧ B ⊆ S := by
  rw [isBase_restrict_iff', isBasis'_iff_isBasis]
  refine ⟨fun h ↦ ⟨?_, h.subset⟩, fun h ↦ h.1.indep.isBasis_of_subset_of_subset_closure h.2 ?_⟩
  · exact h.indep.isBase_of_spanning <| by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground

lemma Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.E \ S) := by
  rwa [← spanning_iff_compl_coindep]

lemma IsBasis.isBase_of_spanning (hIX : M.IsBasis I X) (hX : M.Spanning X) : M.IsBase I :=
  hIX.indep.isBase_of_spanning <| by rwa [hIX.spanning_iff_spanning]

lemma Indep.exists_isBase_subset_spanning (hI : M.Indep I) (hS : M.Spanning S) (hIS : I ⊆ S) :
    ∃ B, M.IsBase B ∧ I ⊆ B ∧ B ⊆ S := by
  obtain ⟨B, hB⟩ := hI.subset_isBasis_of_subset hIS
  exact ⟨B, hB.1.isBase_of_spanning hS, hB.2, hB.1.subset⟩

lemma Restriction.isBase_iff_of_spanning {N : Matroid α} (hR : N ≤r M) (hN : M.Spanning N.E) :
    N.IsBase B ↔ (M.IsBase B ∧ B ⊆ N.E) := by
  obtain ⟨R, hR : R ⊆ M.E, rfl⟩ := hR
  rw [Spanning.isBase_restrict_iff (show M.Spanning R from hN), restrict_ground_eq]

lemma ext_spanning {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S)) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE] )
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, ext_iff_indep, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]

lemma IsBase.eq_of_superset_spanning (hB : M.IsBase B) (hX : M.Spanning X) (hXB : X ⊆ B) : B = X :=
  have ⟨B', hB', hB'X⟩ := hX.exists_isBase_subset
  subset_antisymm (by rwa [← hB'.eq_of_subset_isBase hB (hB'X.trans hXB)]) hXB

theorem isBase_iff_minimal_spanning : M.IsBase B ↔ Minimal M.Spanning B := by
  rw [minimal_subset_iff]
  refine ⟨fun h ↦ ⟨h.spanning, fun _ ↦ h.eq_of_superset_spanning⟩, fun ⟨h, h'⟩ ↦ ?_⟩
  obtain ⟨B', hB', hBB'⟩ := h.exists_isBase_subset
  rwa [h' hB'.spanning hBB']

theorem Spanning.isBase_of_minimal (hX : M.Spanning X) (h : ∀ ⦃Y⦄, M.Spanning Y → Y ⊆ X → X = Y) :
    M.IsBase X := by
  rwa [isBase_iff_minimal_spanning, minimal_subset_iff, and_iff_right hX]

end Spanning

section Constructions

variable {R S : Set α}

@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_isBasis' X
  obtain ⟨hI', hIR⟩ := isBasis'_restrict_iff.1 hI
  ext e
  rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, hI.indep.mem_closure_iff', mem_union,
    mem_inter_iff, hI'.indep.mem_closure_iff', restrict_ground_eq, restrict_indep_iff, mem_diff]
  by_cases he : M.Indep (insert e I)
  · simp [he, and_comm, insert_subset_iff, hIR, (he.subset_ground (mem_insert ..)), imp_or]
  tauto

lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', diff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ :=
  (closure_subset_ground ..).antisymm <| empty_subset _

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E := by
  simp [loopyOn, restrict_closure_eq']

@[simp] lemma loopyOn_spanning_iff {E : Set α} : (loopyOn E).Spanning X ↔ X ⊆ E := by
  rw [spanning_iff, loopyOn_closure_eq, loopyOn_ground, and_iff_right rfl]

@[simp] lemma freeOn_closure_eq (E X : Set α) : (freeOn E).closure X = X ∩ E := by
  simp +contextual [← closure_inter_ground _ X, Set.ext_iff, and_comm,
    insert_subset_iff, freeOn_indep_iff, (freeOn_indep inter_subset_right).mem_closure_iff']

@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X ∩ I ∩ E) ∪ (E \ I) := by
  rw [uniqueBaseOn, restrict_closure_eq', freeOn_closure_eq, inter_right_comm,
    inter_assoc (c := E), inter_self, inter_right_comm, freeOn_ground]

lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure ?_, fun h ↦ by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq, ← h]
  exact M.closure_mono (empty_subset _)

@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  -- Use a choice of basis and extensionality to change the goal to a statement about independence.
  obtain ⟨I, hI⟩ := (M.comap f).exists_isBasis' X
  obtain ⟨hI', hIinj, -⟩ := comap_isBasis'_iff.1 hI
  simp_rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, Set.ext_iff,
    hI.indep.mem_closure_iff', comap_ground_eq, mem_preimage, hI'.indep.mem_closure_iff',
    comap_indep_iff, and_imp, mem_image, and_congr_right_iff, ← image_insert_eq]
  -- the lemma now easily follows by considering elements/non-elements of `I` separately.
  intro x hxE
  by_cases hxI : x ∈ I
  · simp [hxI, show ∃ y ∈ I, f y = f x from ⟨x, hxI, rfl⟩]
  simp [hxI, injOn_insert hxI, hIinj]

@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  -- It is enough to prove that `map` and `closure` commute for `M`-independent sets.
  suffices aux : ∀ ⦃I⦄, M.Indep I → (M.map f hf).closure (f '' I) = f '' (M.closure I) by
    obtain ⟨I, hI⟩ := M.exists_isBasis (f ⁻¹' X ∩ M.E)
    rw [← closure_inter_ground, map_ground, ← M.closure_inter_ground, ← hI.closure_eq_closure,
      ← aux hI.indep, ← image_preimage_inter, ← (hI.map hf).closure_eq_closure]
  -- Let `I` be independent, and transform the goal using closure/independence lemmas
  refine fun I hI ↦ Set.ext fun e ↦ ?_
  simp only [(hI.map f hf).mem_closure_iff', map_ground, mem_image, map_indep_iff,
    forall_exists_index, and_imp, hI.mem_closure_iff']
  -- The goal now easily follows from the invariance of independence under maps.
  constructor
  · rintro ⟨⟨x, hxE, rfl⟩, h2⟩
    refine ⟨x, ⟨hxE, fun hI' ↦ ?_⟩, rfl⟩
    obtain ⟨y, hyI, hfy⟩ := h2 _ hI' image_insert_eq.symm
    rw [hf.eq_iff (hI.subset_ground hyI) hxE] at hfy
    rwa [← hfy]
  rintro ⟨x, ⟨hxE, hxi⟩, rfl⟩
  refine ⟨⟨x, hxE, rfl⟩, fun J hJ hJI ↦ ⟨x, hxi ?_, rfl⟩⟩
  replace hJ := hJ.map f hf
  have hrw := image_insert_eq ▸ hJI
  rwa [← hrw, map_image_indep_iff (insert_subset hxE hI.subset_ground)] at hJ

lemma restrict_spanning_iff (hSR : S ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Spanning S ↔ R ⊆ M.closure S := by
  rw [spanning_iff, restrict_ground_eq, and_iff_left hSR, restrict_closure_eq _ hSR, inter_eq_right]

lemma restrict_spanning_iff' : (M ↾ R).Spanning S ↔ R ∩ M.E ⊆ M.closure S ∧ S ⊆ R := by
  rw [spanning_iff, restrict_closure_eq', restrict_ground_eq, and_congr_left_iff,
    diff_eq_compl_inter, ← union_inter_distrib_right, inter_eq_right, union_comm,
    ← diff_subset_iff, diff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

end Constructions

end Matroid
