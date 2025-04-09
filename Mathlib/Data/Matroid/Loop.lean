/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Circuit
import Mathlib.Tactic.TFAE

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
* For `M : Matroid α`, `M.loops` is the set `M.closure ∅`.
* For `M : Matroid α` and `e : α`, `M.IsLoop e` means that `e` is a loop of `M`,
  defined as the statement `e ∈ M.loops`.
-/

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

/-- `Matroid.loops M` is the closure of the empty set. -/
abbrev loops (M : Matroid α) := M.closure ∅

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma loops_subset_ground (M : Matroid α) : M.loops ⊆ M.E :=
  M.closure_subset_ground ∅

/-- A 'loop' is a member of the closure of the empty set -/
def IsLoop (M : Matroid α) (e : α) : Prop := e ∈ M.loops

lemma isLoop_iff : M.IsLoop e ↔ e ∈ M.loops := Iff.rfl

lemma closure_empty (M : Matroid α) : M.closure ∅ = M.loops := rfl

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsLoop.mem_ground (he : M.IsLoop e) : e ∈ M.E :=
  closure_subset_ground M ∅ he

lemma isLoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsLoop e,
    e ∈ M.closure ∅,
    M.IsCircuit {e},
    M.Dep {e},
    ∀ ⦃B⦄, M.IsBase B → e ∈ M.E \ B] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_not_mem (not_mem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_not_mem (not_mem_empty e)]
  tfae_have 4 ↔ 5 := by
    simp only [dep_iff, singleton_subset_iff, mem_diff, forall_and]
    refine ⟨fun h ↦ ⟨fun _ _ ↦ h.2, fun B hB heB ↦ h.1 (hB.indep.subset (by simpa))⟩,
      fun h ↦ ⟨fun hi ↦ ?_, h.1 _ M.exists_isBase.choose_spec⟩⟩
    obtain ⟨B, hB, heB⟩ := hi.exists_isBase_superset
    exact h.2 _ hB (by simpa using heB)
  tfae_finish

@[simp]
lemma singleton_dep : M.Dep {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 3 0

alias ⟨_, IsLoop.dep⟩ := singleton_dep

@[simp]
lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬M.Indep {e} ↔ M.IsLoop e :=
  by rw [← singleton_dep, ← not_indep_iff]

@[simp]
lemma singleton_isCircuit : M.IsCircuit {e} ↔ M.IsLoop e :=
  (M.isLoop_tfae e).out 2 0

alias ⟨_, IsLoop.isCircuit⟩ := singleton_isCircuit

lemma isLoop_iff_forall_mem_compl_isBase : M.IsLoop e ↔ ∀ B, M.IsBase B → e ∈ M.E \ B :=
  (M.isLoop_tfae e).out 0 4

lemma isLoop_iff_forall_not_mem_isBase (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ ∀ B, M.IsBase B → e ∉ B := by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_diff, and_iff_right he]

lemma IsLoop.mem_closure (he : M.IsLoop e) (X : Set α) : e ∈ M.closure X :=
  M.closure_mono (empty_subset _) he

lemma IsLoop.mem_of_isFlat (he : M.IsLoop e) {F : Set α} (hF : M.IsFlat F) : e ∈ F :=
  hF.closure ▸ he.mem_closure F

lemma IsFlat.loops_subset (hF : M.IsFlat F) : M.loops ⊆ F :=
  fun _ he ↦ IsLoop.mem_of_isFlat he hF

lemma IsLoop.dep_of_mem (he : M.IsLoop e) (h : e ∈ X) (hXE : X ⊆ M.E := by aesop_mat) : M.Dep X :=
  he.dep.superset (singleton_subset_iff.mpr h) hXE

lemma IsLoop.not_indep_of_mem (he : M.IsLoop e) (h : e ∈ X) : ¬M.Indep X :=
  fun hX ↦ he.dep.not_indep (hX.subset (singleton_subset_iff.mpr h))

lemma IsLoop.not_mem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I :=
  fun h ↦ he.not_indep_of_mem h hI

lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e ∈ C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I M.loops :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.not_mem_of_indep he hI heI

lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.loops) : I = ∅ :=
  eq_empty_iff_forall_not_mem.mpr fun _ he ↦ IsLoop.not_mem_of_indep (h he) hI he

@[simp]
lemma isBasis_loops_iff : M.IsBasis I M.loops ↔ I = ∅ :=
  ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [M.empty_indep.isBasis_closure]⟩

lemma closure_eq_loops_of_subset (h : X ⊆ M.loops) : M.closure X = M.loops :=
  (closure_subset_closure_of_subset_closure h).antisymm (M.closure_mono (empty_subset _))

lemma isBasis_iff_empty_of_subset_loops (hX : X ⊆ M.loops) : M.IsBasis I X ↔ I = ∅ := by
  refine ⟨fun h ↦ ?_, by rintro rfl; simpa⟩
  have := (closure_eq_loops_of_subset hX) ▸ h.isBasis_closure_right
  simpa using this

lemma IsLoop.closure (he : M.IsLoop e) : M.closure {e} = M.loops :=
  closure_eq_loops_of_subset (singleton_subset_iff.mpr he)

lemma isLoop_iff_closure_eq_loops_and_mem_ground :
    M.IsLoop e ↔ M.closure {e} = M.loops ∧ e ∈ M.E where
  mp h := ⟨h.closure, h.mem_ground⟩
  mpr h := by
    rw [isLoop_iff, ← singleton_subset_iff, ← closure_subset_closure_iff_subset_closure, h.1]

lemma isLoop_iff_closure_eq_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.loops := by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground, and_iff_left he]

/-- A version of `restrict_loops_eq` without the hypothesis that `R ⊆ M.E` -/
lemma restrict_loops_eq' (M : Matroid α) (R : Set α) :
    (M ↾ R).loops = (M.loops ∩ R) ∪ (R \ M.E) := by
  rw [loops, restrict_closure_eq', empty_inter]

lemma restrict_loops_eq {R : Set α} (hR : R ⊆ M.E) : (M ↾ R).loops = M.loops ∩ R := by
  rw [restrict_loops_eq', diff_eq_empty.2 hR, union_empty]

@[simp]
lemma restrict_isLoop_iff {R : Set α} : (M ↾ R).IsLoop e ↔ e ∈ R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_diff]
  tauto

lemma IsRestriction.isLoop_iff (hNM : N ≤r M) : N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim

lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N ≤r M) : M.IsLoop e :=
  ((hNM.isLoop_iff).1 he).2

lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.IsLoop e :=
  (hNM.isLoop_iff).2 ⟨heN, he⟩

lemma map_loops {f : α → β} {hf : InjOn f M.E} : (M.map f hf).loops = f '' M.loops := by
  simp

@[simp]
lemma map_isLoop_iff {f : α → β} {hf : InjOn f M.E} (he : e ∈ M.E := by aesop_mat) :
    (M.map f hf).IsLoop (f e) ↔ M.IsLoop e := by
  rw [isLoop_iff, map_loops, hf.mem_image_iff M.loops_subset_ground he, isLoop_iff]

@[simp]
lemma mapEmbedding_isLoop_iff {f : α ↪ β} : (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e := by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty]

lemma comap_loops {M : Matroid β} {f : α → β} : (M.comap f).loops = f ⁻¹' M.loops := by
   rw [loops, comap_closure_eq, image_empty]

@[simp]
lemma comap_isLoop_iff {M : Matroid β} {f : α → β} : (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  simp [isLoop_iff]

@[simp]
lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e ∈ E := by
  simp [isLoop_iff]

@[simp]
lemma freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e := by
  simp [isLoop_iff]

@[simp]
lemma uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e ∈ E \ I := by
  simp [isLoop_iff]

end Matroid
