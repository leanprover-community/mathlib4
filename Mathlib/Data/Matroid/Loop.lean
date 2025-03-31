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
For `M : Matroid α`, this file defines a set `Matroid.loops M : Set α`,
as well as predicates `Matroid.IsLoop M : α → Prop` and `Matroid.IsNonloop M : α → Prop`,
and provides API for interacting with them.

# Main Declarations
For `M` : Matroid `α`:
* `M.loops` is the set `M.closure ∅`.
* `M.IsLoop e` means that `e : α` is a loop of `M`, defined as the statement `e ∈ M.loops`.
* `M.IsNonloop e` means that `e ∈ M.E`, but `e` is not a loop of `M`.
-/

variable {α β : Type*} {M N : Matroid α} {e f : α} {F X C I : Set α}

open Set

namespace Matroid

/-- `Matroid.loops M` is the closure of the empty set. -/
def loops (M : Matroid α) := M.closure ∅

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

lemma singleton_not_indep (he : e ∈ M.E := by aesop_mat) : ¬ M.Indep {e} ↔ M.IsLoop e := by
  rw [← singleton_dep, ← not_indep_iff]

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
    by simp +contextual [closure_empty, M.empty_indep.isBasis_closure]⟩

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
    rw [isLoop_iff, ← closure_empty, ← singleton_subset_iff,
      ← closure_subset_closure_iff_subset_closure, h.1]
    rfl

lemma isLoop_iff_closure_eq_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ M.closure {e} = M.loops := by
  rw [isLoop_iff_closure_eq_loops_and_mem_ground, and_iff_left he]

@[simp]
lemma closure_loops (M : Matroid α) : M.closure M.loops = M.loops :=
  M.closure_closure ∅

@[simp]
lemma closure_union_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.loops) = M.closure X := by
  rw [← closure_empty, closure_union_closure_right_eq, union_empty]

@[simp]
lemma closure_loops_union_eq (M : Matroid α) (X : Set α) :
    M.closure (M.loops ∪ X) = M.closure X := by
  simp [union_comm]

@[simp] lemma closure_diff_loops_eq (M : Matroid α) (X : Set α) :
    M.closure (X \ M.loops) = M.closure X := by
  rw [← M.closure_union_loops_eq (X \ M.loops), diff_union_self, ← closure_empty,
    closure_union_closure_right_eq, union_empty]

/-- A version of `restrict_loops_eq` without the hypothesis that `R ⊆ M.E` -/
lemma restrict_loops_eq' (M : Matroid α) (R : Set α) :
    (M ↾ R).loops = (M.loops ∩ R) ∪ (R \ M.E) := by
  rw [← closure_empty, ← closure_empty, restrict_closure_eq', empty_inter]

lemma restrict_loops_eq {R : Set α} (hR : R ⊆ M.E) : (M ↾ R).loops = M.loops ∩ R := by
  rw [restrict_loops_eq', diff_eq_empty.2 hR, union_empty]

@[simp]
lemma restrict_isLoop_iff {R : Set α} : (M ↾ R).IsLoop e ↔ e ∈ R ∧ (M.IsLoop e ∨ e ∉ M.E) := by
  simp only [isLoop_iff, restrict_closure_eq', empty_inter, mem_union, mem_inter_iff, mem_diff,
    ← closure_empty]
  tauto

lemma IsRestriction.isLoop_iff (hNM : N ≤r M) : N.IsLoop e ↔ e ∈ N.E ∧ M.IsLoop e := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp only [restrict_isLoop_iff, restrict_ground_eq, and_congr_right_iff, or_iff_left_iff_imp]
  exact fun heR heE ↦ (heE (hR heR)).elim

lemma IsLoop.of_isRestriction (he : N.IsLoop e) (hNM : N ≤r M) : M.IsLoop e :=
  ((hNM.isLoop_iff).1 he).2

lemma IsLoop.isLoop_isRestriction (he : M.IsLoop e) (hNM : N ≤r M) (heN : e ∈ N.E) : N.IsLoop e :=
  (hNM.isLoop_iff).2 ⟨heN, he⟩

@[simp]
lemma map_loops {f : α → β} {hf : InjOn f M.E} : (M.map f hf).loops = f '' M.loops := by
  simp [loops]

@[simp]
lemma map_isLoop_iff {f : α → β} {hf : InjOn f M.E} (he : e ∈ M.E := by aesop_mat) :
    (M.map f hf).IsLoop (f e) ↔ M.IsLoop e := by
  rw [isLoop_iff, map_loops, hf.mem_image_iff M.loops_subset_ground he, isLoop_iff]

@[simp]
lemma mapEmbedding_isLoop_iff {f : α ↪ β} : (M.mapEmbedding f).IsLoop (f e) ↔ M.IsLoop e := by
  simp [mapEmbedding, isLoop_iff, isLoop_iff, map_closure_eq, preimage_empty, ← closure_empty]

@[simp]
lemma comap_loops {M : Matroid β} {f : α → β} : (M.comap f).loops = f ⁻¹' M.loops := by
   rw [loops, comap_closure_eq, image_empty, loops]

@[simp]
lemma comap_isLoop_iff {M : Matroid β} {f : α → β} : (M.comap f).IsLoop e ↔ M.IsLoop (f e) := by
  simp [isLoop_iff]

@[simp]
lemma loopyOn_isLoop_iff {E : Set α} : (loopyOn E).IsLoop e ↔ e ∈ E := by
  simp [isLoop_iff, loops]

@[simp]
lemma freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e := by
  simp [isLoop_iff, loops]

@[simp]
lemma uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e ∈ E \ I := by
  simp [isLoop_iff, loops]

section IsNonloop

/-- `M.IsNonloop e` means that `e` is an element of `M.E` but not a loop of `M`. -/
@[mk_iff]
structure IsNonloop (M : Matroid α) (e : α) : Prop where
  not_isLoop : ¬ M.IsLoop e
  mem_ground : e ∈ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsNonloop.mem_ground

lemma IsLoop.not_isNonloop (he : M.IsLoop e) : ¬M.IsNonloop e :=
  fun h ↦ h.not_isLoop he

lemma isNonloop_of_not_isLoop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsLoop e) : M.IsNonloop e :=
  ⟨h,he⟩

lemma isLoop_of_not_isNonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsNonloop e) : M.IsLoop e :=
  by rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp] lemma not_isLoop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsLoop e ↔ M.IsNonloop e :=
  ⟨fun h ↦ ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp] lemma not_isNonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsNonloop e ↔ M.IsLoop e := by
  rw [← not_isLoop_iff, not_not]

lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e ∈ M.E \ M.loops := by
  rw [isNonloop_iff, IsLoop, and_comm, mem_diff]

lemma setOf_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loops :=
  Set.ext (fun _ ↦ isNonloop_iff_mem_compl_loops)

lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops := by
  by_cases he : e ∈ M.E
  · simp [IsNonloop, isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h ↦ he h.mem_ground)]

lemma isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ∨ M.IsNonloop e := by
  rw [isNonloop_iff, and_iff_left he]; apply em

@[simp] lemma indep_singleton : M.Indep {e} ↔ M.IsNonloop e := by
  rw [isNonloop_iff, ← singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

lemma Indep.isNonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he ↦ (he.not_mem_of_indep hI) h

lemma IsNonloop.exists_mem_isBase (he : M.IsNonloop e) : ∃ B, M.IsBase B ∧ e ∈ B := by
  simpa using (indep_singleton.2 he).exists_isBase_superset

lemma IsCocircuit.isNonloop_of_mem {K : Set α} (hK : M.IsCocircuit K) (he : e ∈ K) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff (hK.subset_ground he), ← singleton_isCircuit]
  intro he'
  obtain ⟨f, ⟨rfl, -⟩, hfe⟩ := (he'.isCocircuit_inter_nontrivial hK ⟨e, by simp [he]⟩).exists_ne e
  exact hfe rfl

lemma IsCircuit.isNonloop_of_mem (hC : M.IsCircuit C) (hC' : C.Nontrivial) (he : e ∈ C) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop (hC.subset_ground he)
    (fun hL ↦ by simp [hL.eq_of_isCircuit_mem hC he] at hC')

lemma IsCircuit.isNonloop_of_mem_of_one_lt_card (hC : M.IsCircuit C) (h : 1 < C.encard)
    (he : e ∈ C) : M.IsNonloop e := by
  refine isNonloop_of_not_isLoop (hC.subset_ground he) (fun hlp ↦ ?_)
  rw [hlp.eq_of_isCircuit_mem hC he, encard_singleton] at h
  exact h.ne rfl

lemma isNonloop_of_not_mem_closure (h : e ∉ M.closure X) (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop he (fun hel ↦ h (hel.mem_closure X))

lemma isNonloop_iff_not_mem_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.loops := by
  rw [isNonloop_iff, isLoop_iff, and_iff_left he]

lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_not_mem_loops he.mem_ground).1 he⟩).1

lemma IsNonloop.mem_closure_comm (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    f ∈ M.closure {e} ↔ e ∈ M.closure {f} :=
  ⟨hf.mem_closure_singleton, he.mem_closure_singleton⟩

lemma IsNonloop.isNonloop_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.IsNonloop f := by
  rw [isNonloop_iff, and_comm]
  by_contra! h; apply he.not_isLoop
  rw [isLoop_iff] at *; convert hef using 1
  obtain (hf | hf) := em (f ∈ M.E)
  · rw [← closure_loops, ← insert_eq_of_mem (h hf), closure_insert_congr_right M.closure_loops,
      insert_empty_eq]
  rw [eq_comm, ← closure_inter_ground, inter_comm, inter_singleton_eq_empty.mpr hf, loops]

lemma IsNonloop.closure_eq_of_mem_closure (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    M.closure {e} = M.closure {f} := by
  rw [← closure_closure _ {f}, ← insert_eq_of_mem hef, closure_insert_closure_eq_closure_insert,
    ← closure_closure _ {e}, ← insert_eq_of_mem (he.mem_closure_singleton hef),
    closure_insert_closure_eq_closure_insert, pair_comm]

/-- Two distinct nonloops with the same closure form a circuit. -/
lemma IsNonloop.closure_eq_closure_iff_isCircuit_of_ne (he : M.IsNonloop e) (hef : e ≠ f) :
    M.closure {e} = M.closure {f} ↔ M.IsCircuit {e, f} := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := he.isNonloop_of_mem_closure (by rw [← h]; exact M.mem_closure_self e)
    rw [isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff,
      and_iff_right he.mem_ground, singleton_subset_iff, and_iff_left hf.mem_ground]
    suffices ¬ M.Indep {e, f} by simpa [pair_diff_left hef, hf, pair_diff_right hef, he]
    rw [Indep.insert_indep_iff_of_not_mem (by simpa) (by simpa)]
    simp [← h, mem_closure_self _ _ he.mem_ground]
  have hclosure := (h.closure_diff_singleton_eq e).trans
    (h.closure_diff_singleton_eq f).symm
  rwa [pair_diff_left hef, pair_diff_right hef, eq_comm] at hclosure

lemma IsNonloop.closure_eq_closure_iff_eq_or_dep (he : M.IsNonloop e) (hf : M.IsNonloop f) :
    M.closure {e} = M.closure {f} ↔ e = f ∨ ¬M.Indep {e, f} := by
  obtain (rfl | hne) := eq_or_ne e f
  · exact iff_of_true rfl (Or.inl rfl)
  simp_rw [he.closure_eq_closure_iff_isCircuit_of_ne hne, or_iff_right hne,
    isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff, insert_subset_iff, singleton_subset_iff,
    and_iff_left hf.mem_ground, and_iff_left he.mem_ground, and_iff_left_iff_imp]
  rintro hi x (rfl | rfl)
  · rwa [pair_diff_left hne, indep_singleton]
  rwa [pair_diff_right hne, indep_singleton]

lemma exists_isNonloop (M : Matroid α) [RankPos M] : ∃ e, M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  ⟨_, hB.indep.isNonloop_of_mem hB.nonempty.some_mem⟩

lemma IsNonloop.rankPos (h : M.IsNonloop e) : M.RankPos :=
  h.indep.rankPos_of_nonempty (singleton_nonempty e)

@[simp] lemma restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]

lemma IsNonloop.of_restrict {R : Set α} (h : (M ↾ R).IsNonloop e) : M.IsNonloop e :=
  (restrict_isNonloop_iff.1 h).1

lemma IsNonloop.of_isRestriction (h : N.IsNonloop e) (hNM : N ≤r M) : M.IsNonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

lemma isNonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) :
    M.IsNonloop e ↔ (M ↾ R).IsNonloop e :=
  ⟨fun h ↦ restrict_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp] lemma comap_isNonloop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsNonloop e ↔ M.IsNonloop (f e) := by
  rw [← indep_singleton, comap_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

@[simp] lemma freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e ∈ E := by
  rw [← indep_singleton, freeOn_indep_iff, singleton_subset_iff]

@[simp] lemma uniqueBaseOn_isNonloop_iff {I E : Set α} :
    (uniqueBaseOn I E).IsNonloop e ↔ e ∈ I ∩ E := by
  rw [← indep_singleton, uniqueBaseOn_indep_iff', singleton_subset_iff]

lemma IsNonloop.exists_mem_isCocircuit (he : M.IsNonloop e) : ∃ K, M.IsCocircuit K ∧ e ∈ K := by
  obtain ⟨B, hB, heB⟩ := he.exists_mem_isBase
  exact ⟨_, fundCocircuit_isCocircuit heB hB, mem_fundCocircuit M e B⟩

@[simp]
lemma closure_inter_setOf_isNonloop_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∩ {e | M.IsNonloop e}) = M.closure X := by
  rw [setOf_isNonloop_eq, ← inter_diff_assoc, closure_diff_loops_eq, closure_inter_ground]

end IsNonloop

end Matroid
