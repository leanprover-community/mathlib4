/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Circuit

/-!

# Matroid Loops

A 'loop' of a matroid `M` is an element `e` satisfying one of the following equivalent conditions:
* `e ∈ M.closure ∅`;
* `{e}` is dependent in `M`;
* `{e}` is a circuit of `M`;
* no base of `M` contains `e`.
In many mathematical contexts, loops can be thought of as 'trivial' or 'zero' elements;
For linearly representable matroids, they correspond to the zero vector,
and for graphic matroids, they correspond to edges incident with just one vertex (aka 'loops').

As trivial as they are, loops can be created from matroids with no loops by taking minors or duals,
so in many contexts it is unreasonable to simply forbid loops from appearing.
This file defines loops, and provides API for interacting with them.

# Main Declarations

* For `M : Matroid α` and `e : α`, `M.IsLoop e` means that `e` is a loop of `M`,
  defined as the statement `e ∈ M.closure ∅`.

# Terminology

The set `M.closure ∅ = {e | M.IsLoop e}` appears frequently in statements about loops.
To avoid favouring one term such as `setOf_isLoop` or `closure_empty`,
we instead refer to it in lemma names by the shorter term `loops`.
-/

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set
open scoped symmDiff

namespace Matroid

/-- A 'loop' is a member of the closure of the empty set -/
def IsLoop (M : Matroid α) (e : α) : Prop :=
  e ∈ M.closure ∅

lemma isLoop_iff : M.IsLoop e ↔ e ∈ M.closure ∅ := Iff.rfl

lemma closure_empty_eq_loops (M : Matroid α) : M.closure ∅ = {e | M.IsLoop e} := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsLoop.mem_ground (he : M.IsLoop e) : e ∈ M.E :=
  closure_subset_ground M ∅ he

@[simp] lemma singleton_dep : M.Dep {e} ↔ M.IsLoop e := by
  rw [isLoop_iff, M.empty_indep.mem_closure_iff_of_not_mem (not_mem_empty e), insert_emptyc_eq]

@[simp] lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬M.Indep {e} ↔ M.IsLoop e :=
  by rw [← singleton_dep, ← not_indep_iff]

lemma IsLoop.dep (he : M.IsLoop e) : M.Dep {e} :=
  singleton_dep.2 he

lemma singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e := by
  simp [← singleton_dep, isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]

lemma isLoop_iff_not_mem_isBase_forall (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ ∀ B, M.IsBase B → e ∉ B := by
  rw [← singleton_dep, ← not_indep_iff, not_iff_comm, not_forall]
  simp_rw [_root_.not_imp, not_not, ← singleton_subset_iff, indep_iff]

lemma IsLoop.isCircuit (he : M.IsLoop e) : M.IsCircuit {e} :=
  singleton_isCircuit.mpr he

lemma IsLoop.mem_closure (he : M.IsLoop e) (X : Set α) : e ∈ M.closure X :=
  M.closure_mono (empty_subset _) he

lemma IsLoop.mem_isFlat (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F) : e ∈ F := by
  have := he.mem_closure F; rwa [hF.closure] at this

lemma IsFlat.loops_subset (hF : M.IsFlat F) : M.closure ∅ ⊆ F := fun _ he ↦ IsLoop.mem_isFlat he hF

lemma IsLoop.dep_of_mem (he : M.IsLoop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

lemma IsLoop.not_indep_of_mem (he : M.IsLoop e) (h : e ∈ X) : ¬M.Indep X := fun hX ↦
  he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

lemma IsLoop.not_mem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I := fun h ↦
  he.not_indep_of_mem h hI

lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e ∈ C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I (M.closure ∅) :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.not_mem_of_indep he hI heI

lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.closure ∅) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun _ he ↦ IsLoop.not_mem_of_indep (h he) hI he

@[simp] lemma isBasis_loops_iff : M.IsBasis I (M.closure ∅) ↔ I = ∅ := by
  refine ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset, ?_⟩
  rintro rfl
  exact M.empty_indep.isBasis_closure

lemma closure_eq_loops_of_subset (h : X ⊆ M.closure ∅) : M.closure X = M.closure ∅ :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

lemma isBasis_iff_empty_of_subset_loops (hX : X ⊆ M.closure ∅) : M.IsBasis I X ↔ I = ∅ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simpa⟩
  replace h := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using h

lemma IsLoop.closure (he : M.IsLoop e) : M.closure {e} = M.closure ∅ :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma isLoop_iff_closure_eq_loops' :
    M.IsLoop e ↔ M.closure {e} = M.closure ∅ ∧ e ∈ M.E := by
  wlog he : e ∈ M.E
  · simp [he, show ¬ M.IsLoop e from fun h ↦ he h.mem_ground]
  rw [isLoop_iff, and_iff_left he, subset_antisymm_iff,
    and_iff_left (M.closure_subset_closure (empty_subset {e})),
    closure_subset_closure_iff_subset_closure (by simpa), singleton_subset_iff]

lemma isLoop_iff_closure_eq_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.closure ∅ := by
  rw [isLoop_iff_closure_eq_loops', and_iff_left he]

lemma isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ ∀ B, M.IsBase B → e ∈ M.E \ B := by
  refine ⟨fun h B hB ↦ mem_of_mem_of_subset h ?_, fun h ↦ ?_⟩
  · rw [subset_diff, and_iff_right (closure_subset_ground _ _), disjoint_iff_inter_eq_empty,
      hB.indep.closure_inter_eq_self_of_subset (empty_subset B)]
  have he : e ∈ M.E := M.exists_isBase.elim (fun B hB ↦ (h B hB).1)
  rw [← singleton_dep, ← not_indep_iff]
  intro hei
  obtain ⟨B, hB, heB⟩ := hei.exists_isBase_superset
  exact (h B hB).2 (singleton_subset_iff.mp heB)

@[simp] lemma restrict_isLoop_iff {R : Set α} :
    (M ↾ R).IsLoop e ↔ e ∈ R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  rw [← singleton_dep, restrict_dep_iff, singleton_subset_iff, ← singleton_dep, and_comm,
    and_congr_right_iff, Dep, and_or_right, singleton_subset_iff, and_iff_left or_not,
    or_iff_left_of_imp (fun he hi ↦ he (singleton_subset_iff.1 hi.subset_ground))]
  simp only [singleton_subset_iff, implies_true]

lemma isRestriction_isLoop_iff (hNM : N ≤r M) :
    N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim

lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N ≤r M) : M.IsLoop e :=
  ((isRestriction_isLoop_iff hNM).1 he).2

lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.IsLoop e :=
  (isRestriction_isLoop_iff hNM).2 ⟨heN, he⟩

@[simp] lemma comap_isLoop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  rw [← singleton_dep, comap_dep_iff]
  simp

@[simp] lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e ∈ E := by
  simp [IsLoop]

end Matroid
