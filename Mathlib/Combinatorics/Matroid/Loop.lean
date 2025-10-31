/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Tactic.TFAE

/-!
# Matroid loops and coloops

## Loops
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

## Coloops
The dual notion of a loop is a 'coloop'. Geometrically, these can be thought of elements that are
skew to the remainder of the matroid. Coloops in graphic matroids are 'bridge' edges of the graph,
and coloops in linearly representable matroids are vectors not spanned by the other vectors
in the matroid.
Coloops also have many equivalent definitions in abstract matroid language;
a coloop is an element of `M.E` if any of the following equivalent conditions holds :
* `e` is a loop of `M✶`;
* `{e}` is a cocircuit of `M`;
* `e` is in no circuit of `M`;
* `e` is in every base of `M`;
* for all `X ⊆ M.E`, `e ∈ X ↔ e ∈ M.closure X`,
* `M.E \ {e}` is nonspanning.

## Main Declarations
For `M` : Matroid `α`:
* `M.loops` is the set `M.closure ∅`.
* `M.IsLoop e` means that `e : α` is a loop of `M`, defined as the statement `e ∈ M.loops`.
* `M.isLoop_tfae` gives a number of properties that are equivalent to `IsLoop`.
* `M.IsNonloop e` means that `e ∈ M.E`, but `e` is not a loop of `M`.
* `M.IsColoop e ` means that `e` is a loop of `M✶`.
* `M.coloops` is the set of coloops of `M✶`.
* `M.isColoop_tfae` gives a number of properties that are equivalent to `IsColoop`.
* `M.Loopless` is a typeclass meaning `M` has no loops.
* `M.removeLoops` is the matroid obtained from `M` by restricting to its set of nonloop elements.
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
  tfae_have 2 ↔ 3 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e),
    isCircuit_def, minimal_iff_forall_ssubset, ssubset_singleton_iff]
  tfae_have 2 ↔ 4 := by simp [M.empty_indep.mem_closure_iff_of_notMem (notMem_empty e)]
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

lemma isLoop_iff_forall_notMem_isBase (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ↔ ∀ B, M.IsBase B → e ∉ B := by
  simp_rw [isLoop_iff_forall_mem_compl_isBase, mem_diff, and_iff_right he]

@[deprecated (since := "2025-05-23")]
alias isLoop_iff_forall_not_mem_isBase := isLoop_iff_forall_notMem_isBase

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

lemma IsLoop.notMem_of_indep (he : M.IsLoop e) (hI : M.Indep I) : e ∉ I :=
  fun h ↦ he.not_indep_of_mem h hI

@[deprecated (since := "2025-05-23")] alias IsLoop.not_mem_of_indep := IsLoop.notMem_of_indep

lemma IsLoop.eq_of_isCircuit_mem (he : M.IsLoop e) (hC : M.IsCircuit C) (h : e ∈ C) : C = {e} := by
  rw [he.isCircuit.eq_of_subset_isCircuit hC (singleton_subset_iff.mpr h)]

lemma Indep.disjoint_loops (hI : M.Indep I) : Disjoint I M.loops :=
  by_contra fun h ↦
    let ⟨_, ⟨heI, he⟩⟩ := not_disjoint_iff.mp h
    IsLoop.notMem_of_indep he hI heI

lemma Indep.eq_empty_of_subset_loops (hI : M.Indep I) (h : I ⊆ M.loops) : I = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ he ↦ IsLoop.notMem_of_indep (h he) hI he

@[simp]
lemma isBasis_loops_iff : M.IsBasis I M.loops ↔ I = ∅ :=
  ⟨fun h ↦ h.indep.eq_empty_of_subset_loops h.subset,
    by simp +contextual [closure_empty]⟩

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
      ← closure_subset_closure_iff_subset_closure, h.1, loops]

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

lemma eq_loopyOn_iff_loops {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E where
  mp h := by rw [h, loops]; simp
  mpr | ⟨h, h'⟩ => by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']

lemma restrict_subset_loops_eq (hX : X ⊆ M.loops) : M ↾ X = loopyOn X := by
  rw [eq_loopyOn_iff_loops, restrict_loops_eq', inter_eq_self_of_subset_right hX,
    union_eq_self_of_subset_right diff_subset, and_iff_left M.restrict_ground_eq]

@[simp]
lemma freeOn_not_isLoop (E : Set α) (e : α) : ¬ (freeOn E).IsLoop e := by
  simp [isLoop_iff, loops]

@[simp]
lemma uniqueBaseOn_isLoop_iff {I E : Set α} : (uniqueBaseOn I E).IsLoop e ↔ e ∈ E \ I := by
  simp [isLoop_iff, loops]

lemma eq_loopyOn_iff_loops_eq {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E :=
  ⟨fun h ↦ by simp [h, loops],
  fun ⟨h, h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

section IsNonloop

/-- `M.IsNonloop e` means that `e` is an element of `M.E` but not a loop of `M`. -/
@[mk_iff]
structure IsNonloop (M : Matroid α) (e : α) : Prop where
  not_isLoop : ¬ M.IsLoop e
  mem_ground : e ∈ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsNonloop.mem_ground

lemma IsLoop.not_isNonloop (he : M.IsLoop e) : ¬M.IsNonloop e :=
  fun h ↦ h.not_isLoop he

lemma compl_loops_eq (M : Matroid α) : M.E \ M.loops = {e | M.IsNonloop e} := by
  simp [Set.ext_iff, isNonloop_iff, and_comm, isLoop_iff]

lemma isNonloop_of_not_isLoop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsLoop e) : M.IsNonloop e :=
  ⟨h,he⟩

lemma isLoop_of_not_isNonloop (he : e ∈ M.E := by aesop_mat) (h : ¬ M.IsNonloop e) : M.IsLoop e :=
  by rwa [isNonloop_iff, and_iff_left he, not_not] at h

@[simp]
lemma not_isLoop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsLoop e ↔ M.IsNonloop e :=
  ⟨fun h ↦ ⟨h, he⟩, IsNonloop.not_isLoop⟩

@[simp]
lemma not_isNonloop_iff (he : e ∈ M.E := by aesop_mat) : ¬M.IsNonloop e ↔ M.IsLoop e := by
  rw [← not_isLoop_iff, not_not]

lemma isNonloop_iff_mem_compl_loops : M.IsNonloop e ↔ e ∈ M.E \ M.loops := by
  rw [isNonloop_iff, IsLoop, and_comm, mem_diff]

lemma setOf_isNonloop_eq (M : Matroid α) : {e | M.IsNonloop e} = M.E \ M.loops :=
  Set.ext (fun _ ↦ isNonloop_iff_mem_compl_loops)

lemma not_isNonloop_iff_closure : ¬ M.IsNonloop e ↔ M.closure {e} = M.loops := by
  by_cases he : e ∈ M.E
  · simp [isLoop_iff_closure_eq_loops_and_mem_ground, he]
  simp [← closure_inter_ground, singleton_inter_eq_empty.2 he, loops,
    (show ¬ M.IsNonloop e from fun h ↦ he h.mem_ground)]

lemma isLoop_or_isNonloop (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) :
    M.IsLoop e ∨ M.IsNonloop e := by
  rw [isNonloop_iff, and_iff_left he]; apply em

@[simp]
lemma indep_singleton : M.Indep {e} ↔ M.IsNonloop e := by
  rw [isNonloop_iff, ← singleton_dep, dep_iff, not_and, not_imp_not, singleton_subset_iff]
  exact ⟨fun h ↦ ⟨fun _ ↦ h, singleton_subset_iff.mp h.subset_ground⟩, fun h ↦ h.1 h.2⟩

alias ⟨Indep.isNonloop, IsNonloop.indep⟩ := indep_singleton

lemma Indep.isNonloop_of_mem (hI : M.Indep I) (h : e ∈ I) : M.IsNonloop e := by
  rw [← not_isLoop_iff (hI.subset_ground h)]; exact fun he ↦ (he.notMem_of_indep hI) h

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

lemma isNonloop_of_notMem_closure (h : e ∉ M.closure X) (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e :=
  isNonloop_of_not_isLoop he (fun hel ↦ h (hel.mem_closure X))

@[deprecated (since := "2025-05-23")]
alias isNonloop_of_not_mem_closure := isNonloop_of_notMem_closure

lemma isNonloop_iff_notMem_loops (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e ↔ e ∉ M.loops := by
  rw [isNonloop_iff, isLoop_iff, and_iff_left he]

@[deprecated (since := "2025-05-23")]
alias isNonloop_iff_not_mem_loops := isNonloop_iff_notMem_loops

lemma IsNonloop.mem_closure_singleton (he : M.IsNonloop e) (hef : e ∈ M.closure {f}) :
    f ∈ M.closure {e} := by
  rw [← union_empty {_}, singleton_union] at *
  exact (M.closure_exchange (X := ∅)
    ⟨hef, (isNonloop_iff_notMem_loops he.mem_ground).1 he⟩).1

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
    rw [Indep.insert_indep_iff_of_notMem (by simpa) (by simpa)]
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

@[simp]
lemma restrict_isNonloop_iff {R : Set α} : (M ↾ R).IsNonloop e ↔ M.IsNonloop e ∧ e ∈ R := by
  rw [← indep_singleton, restrict_indep_iff, singleton_subset_iff, indep_singleton]

lemma IsNonloop.of_restrict {R : Set α} (h : (M ↾ R).IsNonloop e) : M.IsNonloop e :=
  (restrict_isNonloop_iff.1 h).1

lemma IsNonloop.of_isRestriction (h : N.IsNonloop e) (hNM : N ≤r M) : M.IsNonloop e := by
  obtain ⟨R, -, rfl⟩ := hNM; exact h.of_restrict

lemma isNonloop_iff_restrict_of_mem {R : Set α} (he : e ∈ R) :
    M.IsNonloop e ↔ (M ↾ R).IsNonloop e :=
  ⟨fun h ↦ restrict_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_restrict⟩

@[simp]
lemma comap_isNonloop_iff {M : Matroid β} {f : α → β} :
    (M.comap f).IsNonloop e ↔ M.IsNonloop (f e) := by
  rw [← indep_singleton, comap_indep_iff, image_singleton, indep_singleton,
    and_iff_left (injOn_singleton _ _)]

@[simp]
lemma freeOn_isNonloop_iff {E : Set α} : (freeOn E).IsNonloop e ↔ e ∈ E := by
  rw [← indep_singleton, freeOn_indep_iff, singleton_subset_iff]

@[simp]
lemma uniqueBaseOn_isNonloop_iff {I E : Set α} :
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

section IsColoop

variable {B K : Set α}

/-- A coloop is a loop of the dual matroid.
See `Matroid.isColoop_tfae` for a number of equivalent definitions. -/
def IsColoop (M : Matroid α) (e : α) : Prop := M✶.IsLoop e

/-- `M.coloops` is the set of coloops of `M`. -/
def coloops (M : Matroid α) := M✶.loops

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsColoop.mem_ground (he : M.IsColoop e) : e ∈ M.E :=
  @IsLoop.mem_ground α (M✶) e he

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma coloops_subset_ground (M : Matroid α) : M.coloops ⊆ M.E :=
  fun _ ↦ IsColoop.mem_ground

lemma isColoop_iff_mem_coloops : M.IsColoop e ↔ e ∈ M.coloops := Iff.rfl

@[simp]
lemma dual_loops : M✶.loops = M.coloops := rfl

@[simp]
lemma dual_coloops : M✶.coloops = M.loops := by
  rw [coloops, dual_dual]

lemma IsColoop.dual_isLoop (he : M.IsColoop e) : M✶.IsLoop e :=
  he

lemma IsColoop.isCocircuit (he : M.IsColoop e) : M.IsCocircuit {e} :=
  IsLoop.isCircuit he

lemma IsLoop.dual_isColoop (he : M.IsLoop e) : M✶.IsColoop e :=
  by rwa [IsColoop, dual_dual]

@[simp]
lemma dual_isColoop_iff_isLoop : M✶.IsColoop e ↔ M.IsLoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isLoop, IsLoop.dual_isColoop⟩

@[simp]
lemma dual_isLoop_iff_isColoop : M✶.IsLoop e ↔ M.IsColoop e :=
  ⟨fun h ↦ by rw [← dual_dual M]; exact h.dual_isColoop, IsColoop.dual_isLoop⟩

lemma singleton_isCocircuit : M.IsCocircuit {e} ↔ M.IsColoop e := by
  simp

lemma isColoop_tfae (M : Matroid α) (e : α) : List.TFAE [
    M.IsColoop e,
    e ∈ M.coloops,
    M.IsCocircuit {e},
    ∀ ⦃B⦄, M.IsBase B → e ∈ B,
    (∀ ⦃C⦄, M.IsCircuit C → e ∉ C) ∧ e ∈ M.E,
    ∀ X, e ∈ M.closure X ↔ e ∈ X,
    ¬ M.Spanning (M.E \ {e}) ] := by
  tfae_have 1 <-> 2 := Iff.rfl
  tfae_have 1 <-> 3 := singleton_isCocircuit.symm
  tfae_have 1 <-> 4 := by
    simp_rw [← dual_isLoop_iff_isColoop, isLoop_iff_forall_mem_compl_isBase]
    refine ⟨fun h B hB ↦ ?_, fun h B hB ↦ h hB.compl_isBase_of_dual⟩
    obtain ⟨-, heB : e ∈ B⟩ := by simpa using h (M.E \ B) hB.compl_isBase_dual
    assumption
  tfae_have 3 -> 5 := fun h ↦
    ⟨fun C hC heC ↦ hC.inter_isCocircuit_ne_singleton h (e := e) (by simpa), h.subset_ground rfl⟩
  tfae_have 5 -> 4 := by
    refine fun ⟨h, heE⟩ B hB ↦ by_contra fun heB ↦ ?_
    rw [← hB.closure_eq] at heE
    obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heB).1 heE
    exact h hC heC
  tfae_have 5 <-> 6 := by
    refine ⟨fun h X ↦ ⟨fun heX ↦ by_contra fun heX' ↦ ?_, fun heX ↦ M.mem_closure_of_mem' heX h.2⟩,
      fun h ↦ ⟨fun C hC heC ↦ ?_, M.closure_subset_ground _ <| (h {e}).2 rfl⟩⟩
    · obtain ⟨C, -, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heX').1 heX
      exact h.1 hC heC
    · simpa [hC.mem_closure_diff_singleton_of_mem heC] using h (C \ {e})
  tfae_have 1 <-> 7 := by
    wlog he : e ∈ M.E
    · exact iff_of_false (fun h ↦ he h.mem_ground) <| by simp [he, M.ground_spanning]
    rw [spanning_iff_compl_coindep diff_subset, ← dual_isLoop_iff_isColoop, ← singleton_dep,
      diff_diff_cancel_left (by simpa), ← not_indep_iff (by simpa)]
  tfae_finish

lemma isColoop_iff_forall_mem_isBase : M.IsColoop e ↔ ∀ ⦃B⦄, M.IsBase B → e ∈ B :=
  (M.isColoop_tfae e).out 0 3

lemma IsBase.mem_of_isColoop (hB : M.IsBase B) (he : M.IsColoop e) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB

lemma IsColoop.mem_of_isBase (he : M.IsColoop e) (hB : M.IsBase B) : e ∈ B :=
  isColoop_iff_forall_mem_isBase.mp he hB

lemma IsBase.coloops_subset (hB : M.IsBase B) : M.coloops ⊆ B :=
  fun _ he ↦ IsColoop.mem_of_isBase he hB

lemma IsColoop.isNonloop (h : M.IsColoop e) : M.IsNonloop e :=
  let ⟨_, hB⟩ := M.exists_isBase
  hB.indep.isNonloop_of_mem ((isColoop_iff_forall_mem_isBase.mp h) hB)

lemma IsLoop.not_isColoop (h : M.IsLoop e) : ¬M.IsColoop e := by
  rw [← dual_isLoop_iff_isColoop]; rw [← dual_dual M, dual_isLoop_iff_isColoop] at h
  exact h.isNonloop.not_isLoop

lemma IsColoop.notMem_isCircuit (he : M.IsColoop e) (hC : M.IsCircuit C) : e ∉ C :=
  fun h ↦ (hC.isCocircuit.isNonloop_of_mem h).not_isLoop he

@[deprecated (since := "2025-05-23")] alias IsColoop.not_mem_isCircuit := IsColoop.notMem_isCircuit

lemma IsCircuit.disjoint_coloops (hC : M.IsCircuit C) : Disjoint C M.coloops :=
  disjoint_right.2 <| fun _ he ↦ IsColoop.notMem_isCircuit he hC

lemma isColoop_iff_forall_notMem_isCircuit (he : e ∈ M.E := by aesop_mat) :
    M.IsColoop e ↔ ∀ ⦃C⦄, M.IsCircuit C → e ∉ C := by
  simp_rw [(M.isColoop_tfae e).out 0 4, and_iff_left he]

@[deprecated (since := "2025-05-23")]
alias isColoop_iff_forall_not_mem_isCircuit := isColoop_iff_forall_notMem_isCircuit

lemma isColoop_iff_forall_mem_compl_isCircuit [RankPos M✶] :
    M.IsColoop e ↔ ∀ C, M.IsCircuit C → e ∈ M.E \ C := by
  by_cases he : e ∈ M.E
  · simp [isColoop_iff_forall_notMem_isCircuit, he]
  obtain ⟨C, hC⟩ := M.exists_isCircuit
  exact iff_of_false (fun h ↦ he h.mem_ground) fun h ↦ he (h C hC).1

lemma IsCircuit.not_isColoop_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) : ¬ M.IsColoop e :=
  fun h ↦ h.notMem_isCircuit hC heC

lemma isColoop_iff_forall_mem_closure_iff_mem : M.IsColoop e ↔ (∀ X, e ∈ M.closure X ↔ e ∈ X) :=
  (M.isColoop_tfae e).out 0 5

/-- A version of `Matroid.isColoop_iff_forall_mem_closure_iff_mem` where we only quantify
over subsets of the ground set. -/
lemma isColoop_iff_forall_mem_closure_iff_mem' :
    M.IsColoop e ↔ (∀ X, X ⊆ M.E → (e ∈ M.closure X ↔ e ∈ X)) ∧ e ∈ M.E := by
  refine ⟨fun h ↦ ⟨fun X _ ↦ isColoop_iff_forall_mem_closure_iff_mem.1 h X, h.mem_ground⟩,
    fun ⟨h, he⟩ ↦ isColoop_iff_forall_mem_closure_iff_mem.2 fun X ↦ ?_⟩
  rw [← closure_inter_ground, h _ inter_subset_right, mem_inter_iff, and_iff_left he]

lemma IsColoop.mem_closure_iff_mem (he : M.IsColoop e) : e ∈ M.closure X ↔ e ∈ X :=
  (isColoop_iff_forall_mem_closure_iff_mem.1 he) X

lemma IsColoop.mem_of_mem_closure (he : M.IsColoop e) (heX : e ∈ M.closure X) : e ∈ X :=
  he.mem_closure_iff_mem.1 heX

lemma isColoop_iff_diff_not_spanning : M.IsColoop e ↔ ¬ M.Spanning (M.E \ {e}) :=
  (M.isColoop_tfae e).out 0 6

alias ⟨IsColoop.diff_not_spanning, _⟩ := isColoop_iff_diff_not_spanning

lemma isColoop_iff_diff_closure : M.IsColoop e ↔ M.closure (M.E \ {e}) ≠ M.E := by
  rw [isColoop_iff_diff_not_spanning, spanning_iff_closure_eq]

lemma isColoop_iff_notMem_closure_compl (he : e ∈ M.E := by aesop_mat) :
    M.IsColoop e ↔ e ∉ M.closure (M.E \ {e}) := by
  rw [isColoop_iff_diff_closure, not_iff_not]
  refine ⟨fun h ↦ by rwa [h], fun h ↦ (M.closure_subset_ground _).antisymm fun x hx ↦ ?_⟩
  obtain (rfl | hne) := eq_or_ne x e
  · assumption
  exact M.subset_closure (M.E \ {e}) diff_subset (show x ∈ M.E \ {e} from ⟨hx, hne⟩)

@[deprecated (since := "2025-05-23")]
alias isColoop_iff_not_mem_closure_compl := isColoop_iff_notMem_closure_compl

lemma IsBase.isColoop_iff_forall_notMem_fundCircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsColoop e ↔ ∀ x ∈ M.E \ B, e ∉ M.fundCircuit x B := by
  refine ⟨fun h x hx heC ↦ (h.notMem_isCircuit <| hB.fundCircuit_isCircuit hx.1 hx.2) heC,
    fun h ↦ ?_⟩
  have h' : M.E \ {e} ⊆ M.closure (B \ {e}) := by
    rintro x ⟨hxE, hne : x ≠ e⟩
    obtain (hx | hx) := em (x ∈ B)
    · exact M.subset_closure (B \ {e}) (diff_subset.trans hB.subset_ground) ⟨hx, hne⟩
    have h_cct := (hB.fundCircuit_isCircuit hxE hx).mem_closure_diff_singleton_of_mem
      (M.mem_fundCircuit x B)
    refine (M.closure_subset_closure (subset_diff_singleton ?_ ?_)) h_cct
    · simpa using fundCircuit_subset_insert ..
    simp [hne.symm, h x ⟨hxE, hx⟩]
  rw [isColoop_iff_notMem_closure_compl (hB.subset_ground he)]
  exact notMem_subset (M.closure_subset_closure_of_subset_closure h') <|
    hB.indep.notMem_closure_diff_of_mem he

@[deprecated (since := "2025-05-23")]
alias IsBase.isColoop_iff_forall_not_mem_fundCircuit :=
  IsBase.isColoop_iff_forall_notMem_fundCircuit

lemma IsBasis'.inter_coloops_subset (hIX : M.IsBasis' I X) : X ∩ M.coloops ⊆ I := by
  intro e ⟨heX, (heI : M.IsColoop e)⟩
  rwa [← heI.mem_closure_iff_mem, hIX.isBasis_closure_right.closure_eq_right,
    heI.mem_closure_iff_mem]

lemma IsBasis.inter_coloops_subset (hIX : M.IsBasis I X) : X ∩ M.coloops ⊆ I :=
  hIX.isBasis'.inter_coloops_subset

lemma exists_mem_isCircuit_of_not_isColoop (heE : e ∈ M.E) (he : ¬ M.IsColoop e) :
    ∃ C, M.IsCircuit C ∧ e ∈ C := by
  simp only [isColoop_iff_forall_mem_isBase, not_forall, exists_prop] at he
  obtain ⟨B, hB, heB⟩ := he
  exact ⟨M.fundCircuit e B, hB.fundCircuit_isCircuit heE heB, .inl rfl⟩

@[simp]
lemma closure_inter_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure X ∩ M.coloops = X ∩ M.coloops := by
  simp_rw [Set.ext_iff, mem_inter_iff, ← isColoop_iff_mem_coloops, and_congr_left_iff]
  intro e he
  rw [he.mem_closure_iff_mem]

lemma closure_inter_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
     M.closure X ∩ K = X ∩ K := by
  nth_rw 1 [← inter_eq_self_of_subset_right hK]
  rw [← inter_assoc, closure_inter_coloops_eq, inter_assoc, inter_eq_self_of_subset_right hK]

lemma closure_union_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.closure (X ∪ K) = M.closure X ∪ K := by
  rw [← closure_union_closure_left_eq, subset_antisymm_iff, and_iff_left (M.subset_closure _),
    ← diff_eq_empty, eq_empty_iff_forall_notMem]
  refine fun e ⟨hecl, he⟩ ↦ he (.inl ?_)
  obtain ⟨C, hCss, hC, heC⟩ := (mem_closure_iff_exists_isCircuit he).1 hecl
  rw [← singleton_union, ← union_assoc, union_comm, ← diff_subset_iff,
    (hC.disjoint_coloops.mono_right hK).sdiff_eq_left, singleton_union] at hCss
  exact M.closure_subset_closure_of_subset_closure (by simpa) <|
    hC.mem_closure_diff_singleton_of_mem heC

lemma closure_insert_isColoop_eq (X : Set α) (he : M.IsColoop e) :
    M.closure (insert e X) = insert e (M.closure X) := by
  rw [← union_singleton, closure_union_eq_of_subset_coloops _ (by simpa), union_singleton]

lemma closure_eq_of_subset_coloops (hK : K ⊆ M.coloops) : M.closure K = K ∪ M.loops := by
  rw [← empty_union K, closure_union_eq_of_subset_coloops _ hK, empty_union, union_comm,
    closure_empty]

lemma closure_diff_eq_of_subset_coloops (X : Set α) (hK : K ⊆ M.coloops) :
    M.closure (X \ K) = M.closure X \ K := by
  nth_rw 2 [← inter_union_diff X K]
  rw [union_comm, closure_union_eq_of_subset_coloops _ (inter_subset_right.trans hK),
    union_diff_distrib, diff_eq_empty.mpr inter_subset_right, union_empty, eq_comm,
    sdiff_eq_self_iff_disjoint, disjoint_iff_forall_ne]
  rintro e heK _ heX rfl
  rw [IsColoop.mem_closure_iff_mem (hK heK)] at heX
  exact heX.2 heK

lemma closure_disjoint_of_disjoint_of_subset_coloops (hXK : Disjoint X K) (hK : K ⊆ M.coloops) :
    Disjoint (M.closure X) K := by
  rwa [disjoint_iff_inter_eq_empty, closure_inter_eq_of_subset_coloops X hK,
    ← disjoint_iff_inter_eq_empty]

lemma closure_disjoint_coloops_of_disjoint_coloops (hX : Disjoint X (M.coloops)) :
    Disjoint (M.closure X) M.coloops :=
  closure_disjoint_of_disjoint_of_subset_coloops hX Subset.rfl

lemma closure_union_coloops_eq (M : Matroid α) (X : Set α) :
    M.closure (X ∪ M.coloops) = M.closure X ∪ M.coloops :=
  closure_union_eq_of_subset_coloops _ Subset.rfl

lemma IsColoop.notMem_closure_of_notMem (he : M.IsColoop e) (hX : e ∉ X) : e ∉ M.closure X :=
  mt he.mem_closure_iff_mem.mp hX

@[deprecated (since := "2025-05-23")]
alias IsColoop.not_mem_closure_of_not_mem := IsColoop.notMem_closure_of_notMem

lemma IsColoop.insert_indep_of_indep (he : M.IsColoop e) (hI : M.Indep I) :
    M.Indep (insert e I) := by
  refine (em (e ∈ I)).elim (fun h ↦ by rwa [insert_eq_of_mem h]) fun h ↦ ?_
  rw [← hI.notMem_closure_iff_of_notMem h]
  exact he.notMem_closure_of_notMem h

lemma union_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I ∪ K) ↔ M.Indep I := by
  refine ⟨fun h ↦ h.subset subset_union_left, fun h ↦ ?_⟩
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  exact hB.indep.subset (union_subset hIB (hK.trans fun e he ↦ IsColoop.mem_of_isBase he hB))

lemma diff_indep_iff_indep_of_subset_coloops (hK : K ⊆ M.coloops) :
    M.Indep (I \ K) ↔ M.Indep I := by
  rw [← union_indep_iff_indep_of_subset_coloops hK, diff_union_self,
    union_indep_iff_indep_of_subset_coloops hK]

@[simp]
lemma union_coloops_indep_iff : M.Indep (I ∪ M.coloops) ↔ M.Indep I :=
  union_indep_iff_indep_of_subset_coloops Subset.rfl

@[simp]
lemma diff_coloops_indep_iff : M.Indep (I \ M.coloops) ↔ M.Indep I :=
  diff_indep_iff_indep_of_subset_coloops Subset.rfl

lemma coloops_indep (M : Matroid α) : M.Indep M.coloops := by
  rw [← empty_union M.coloops, union_coloops_indep_iff]
  exact M.empty_indep

lemma restrict_isColoop_iff {R : Set α} (hRE : R ⊆ M.E) :
    (M ↾ R).IsColoop e ↔ e ∉ M.closure (R \ {e}) ∧ e ∈ R := by
  wlog heR : e ∈ R
  · exact iff_of_false (fun h ↦ heR h.mem_ground) fun h ↦ heR h.2
  rw [isColoop_iff_forall_notMem_isCircuit heR, mem_closure_iff_exists_isCircuit (by simp)]
  simp only [restrict_isCircuit_iff hRE, insert_diff_singleton]
  aesop

/-- If two matroids agree on loops and coloops, and have the same independent sets after
  loops/coloops are removed, they are equal. -/
lemma ext_indep_disjoint_loops_coloops {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hl : M₁.loops = M₂.loops) (hc : M₁.coloops = M₂.coloops)
    (h : ∀ I, I ⊆ M₁.E → Disjoint I (M₁.loops ∪ M₁.coloops) → (M₁.Indep I ↔ M₂.Indep I)) :
    M₁ = M₂ := by
  refine ext_indep hE fun I hI ↦ ?_
  rw [← diff_coloops_indep_iff, ← @diff_coloops_indep_iff _ M₂, ← hc]
  obtain hdj | hndj := em (Disjoint I (M₁.loops))
  · rw [h _ (diff_subset.trans hI)]
    rw [disjoint_union_right]
    exact ⟨disjoint_of_subset_left diff_subset hdj, disjoint_sdiff_left⟩
  obtain ⟨e, heI, hel : M₁.IsLoop e⟩ := not_disjoint_iff_nonempty_inter.mp hndj
  refine iff_of_false (hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩) ?_
  rw [isLoop_iff, hl, ← isLoop_iff] at hel
  rw [hc]
  exact hel.not_indep_of_mem ⟨heI, hel.not_isColoop⟩

end IsColoop

section Loopless

/-- A Matroid is `Loopless` if it has no loop -/
@[mk_iff]
class Loopless (M : Matroid α) : Prop where
  loops_eq_empty : M.loops = ∅

@[simp]
lemma loops_eq_empty (M : Matroid α) [Loopless M] : M.loops = ∅ :=
  ‹Loopless M›.loops_eq_empty

lemma isNonloop_of_loopless [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.IsNonloop e := by
  rw [← not_isLoop_iff, isLoop_iff, loops_eq_empty]
  exact notMem_empty _

lemma subsingleton_indep [M.Loopless] (hI : I.Subsingleton) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  obtain rfl | ⟨x, rfl⟩ := hI.eq_empty_or_singleton
  · simp
  simpa using M.isNonloop_of_loopless

lemma not_isLoop (M : Matroid α) [Loopless M] (e : α) : ¬ M.IsLoop e :=
  fun h ↦ (isNonloop_of_loopless (e := e)).not_isLoop h

lemma loopless_iff_forall_isNonloop : M.Loopless ↔ ∀ e ∈ M.E, M.IsNonloop e :=
  ⟨fun _ _ he ↦ isNonloop_of_loopless he,
    fun h ↦ ⟨subset_empty_iff.1 (fun e (he : M.IsLoop e) ↦ (h e he.mem_ground).not_isLoop he)⟩⟩

lemma loopless_iff_forall_not_isLoop : M.Loopless ↔ ∀ e ∈ M.E, ¬ M.IsLoop e :=
  ⟨fun _ e _ ↦ M.not_isLoop e,
    fun h ↦ loopless_iff_forall_isNonloop.2 fun e he ↦ (not_isLoop_iff he).1 (h e he)⟩

lemma loopless_iff_forall_isCircuit : M.Loopless ↔ ∀ C, M.IsCircuit C → C.Nontrivial := by
  suffices (∃ x ∈ M.E, M.IsLoop x) ↔ ∃ x, M.IsCircuit x ∧ x.Subsingleton by
    simpa [loopless_iff_forall_not_isLoop, ← not_iff_not (a := ∀ _, _)]
  refine ⟨fun ⟨e, _, he⟩ ↦ ⟨{e}, he.isCircuit, by simp⟩, fun ⟨C, hC, hCs⟩ ↦ ?_⟩
  obtain (rfl | ⟨e, rfl⟩) := hCs.eq_empty_or_singleton
  · simpa using hC.nonempty
  exact ⟨e, (singleton_isCircuit.1 hC).mem_ground, singleton_isCircuit.1 hC⟩

lemma Loopless.ground_eq (M : Matroid α) [Loopless M] : M.E = {e | M.IsNonloop e} :=
  Set.ext fun _ ↦  ⟨fun he ↦ isNonloop_of_loopless he, IsNonloop.mem_ground⟩

lemma IsRestriction.loopless [M.Loopless] (hR : N ≤r M) : N.Loopless := by
  obtain ⟨R, hR, rfl⟩ := hR
  rw [loopless_iff, restrict_loops_eq hR, M.loops_eq_empty, empty_inter]

instance {M : Matroid α} [M.Nonempty] [Loopless M] : RankPos M :=
  M.ground_nonempty.elim fun _ he ↦ (isNonloop_of_loopless he).rankPos

@[simp] lemma loopyOn_isLoopless_iff {E : Set α} : Loopless (loopyOn E) ↔ E = ∅ := by
  simp [loopless_iff_forall_not_isLoop, eq_empty_iff_forall_notMem]

/-- The loopless matroid obtained from `M` by deleting all its loops. -/
def removeLoops (M : Matroid α) : Matroid α := M ↾ {e | M.IsNonloop e}

lemma removeLoops_eq_restrict (M : Matroid α) : M.removeLoops = M ↾ {e | M.IsNonloop e} := rfl

lemma removeLoops_ground_eq (M : Matroid α) : M.removeLoops.E = {e | M.IsNonloop e} := rfl

instance removeLoops_loopless (M : Matroid α) : Loopless M.removeLoops := by
  simp [loopless_iff_forall_isNonloop, removeLoops]

@[simp]
lemma removeLoops_eq_self (M : Matroid α) [Loopless M] : M.removeLoops = M := by
  rw [removeLoops, ← Loopless.ground_eq, restrict_ground_eq_self]

lemma removeLoops_eq_self_iff : M.removeLoops = M ↔ M.Loopless := by
  refine ⟨fun h ↦ ?_, fun h ↦ M.removeLoops_eq_self⟩
  rw [← h]
  infer_instance

lemma removeLoops_isRestriction (M : Matroid α) : M.removeLoops ≤r M :=
  restrict_isRestriction _ _ (fun _ h ↦ IsNonloop.mem_ground h)

lemma eq_restrict_removeLoops (M : Matroid α) : M.removeLoops ↾ M.E = M := by
  rw [removeLoops, ext_iff_indep]
  simp only [restrict_ground_eq, restrict_indep_iff, true_and]
  exact fun I hIE ↦ ⟨ fun hI ↦ hI.1.1, fun hI ↦ ⟨⟨hI,fun e heI ↦ hI.isNonloop_of_mem heI⟩, hIE⟩⟩

@[simp]
lemma removeLoops_indep_eq : M.removeLoops.Indep = M.Indep := by
  ext I
  rw [removeLoops_eq_restrict, restrict_indep_iff, and_iff_left_iff_imp]
  exact fun h e ↦ h.isNonloop_of_mem

@[simp]
lemma removeLoops_isBasis'_eq : M.removeLoops.IsBasis' = M.IsBasis' := by
  ext
  simp [IsBasis']

@[simp] lemma removeLoops_isBase_eq : M.removeLoops.IsBase = M.IsBase := by
  ext B
  rw [isBase_iff_maximal_indep, removeLoops_indep_eq, isBase_iff_maximal_indep]

@[simp]
lemma removeLoops_isNonloop_eq : M.removeLoops.IsNonloop = M.IsNonloop := by
  ext e
  rw [removeLoops_eq_restrict, restrict_isNonloop_iff, mem_setOf, and_self]

lemma IsNonloop.removeLoops_isNonloop (he : M.IsNonloop e) : M.removeLoops.IsNonloop e := by
  simpa

lemma removeLoops_idem (M : Matroid α) : M.removeLoops.removeLoops = M.removeLoops := by
  simp

lemma removeLoops_restrict_eq_restrict (hX : X ⊆ {e | M.IsNonloop e}) :
    M.removeLoops ↾ X = M ↾ X := by
  rwa [removeLoops_eq_restrict, restrict_restrict_eq]

@[simp]
lemma restrict_univ_removeLoops_eq : (M ↾ univ).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_restrict, restrict_restrict_eq _ (subset_univ _), removeLoops_eq_restrict]
  simp

lemma IsRestriction.isRestriction_removeLoops (hNM : N ≤r M) [N.Loopless] : N ≤r M.removeLoops := by
  obtain ⟨R, hR, rfl⟩ := hNM.exists_eq_restrict
  exact IsRestriction.of_subset M fun e heR ↦ ((M ↾ R).isNonloop_of_loopless heR).of_restrict

lemma removeLoops_mono_isRestriction (hNM : N ≤r M) : N.removeLoops ≤r M.removeLoops :=
  ((removeLoops_isRestriction _).trans hNM).isRestriction_removeLoops

end Loopless

end Matroid
