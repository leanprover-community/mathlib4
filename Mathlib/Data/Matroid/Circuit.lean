/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Closure

/-!
# Matroid Circuits

A `Circuit` of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

# Main Declarations

* `Matroid.Circuit C` means that `C` is minimally dependent in `M`.
-/

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x y : α}

open Set

namespace Matroid

/-- A `Circuit` of `M` is a minimal dependent set in `M` -/
def Circuit (M : Matroid α) := Minimal M.Dep

lemma circuit_def : M.Circuit C ↔ Minimal M.Dep C := Iff.rfl

lemma Circuit.dep (hC : M.Circuit C) : M.Dep C :=
  hC.prop

lemma Circuit.not_indep (hC : M.Circuit C) : ¬ M.Indep C :=
  hC.dep.not_indep

lemma Circuit.minimal (hC : M.Circuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Circuit.subset_ground (hC : M.Circuit C) : C ⊆ M.E :=
  hC.dep.subset_ground

lemma Circuit.nonempty (hC : M.Circuit C) : C.Nonempty :=
  hC.dep.nonempty

lemma empty_not_circuit (M : Matroid α) : ¬M.Circuit ∅ :=
  fun h ↦ by simpa using h.nonempty

lemma circuit_iff : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃D⦄, M.Dep D → D ⊆ C → D = C := by
  simp_rw [circuit_def, minimal_subset_iff, eq_comm (a := C)]

lemma Circuit.ssubset_indep (hC : M.Circuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((circuit_iff.1 hC).2 h hXC.subset)

lemma Circuit.diff_singleton_indep (hC : M.Circuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (diff_singleton_sSubset.2 he)

lemma circuit_iff_forall_ssubset : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  simp_rw [circuit_iff, dep_iff, and_congr_right_iff, ssubset_iff_subset_ne, and_imp]
  exact fun _ hC ↦ ⟨fun h I hIC hne ↦ by_contra fun hi ↦ hne (h hi (hIC.trans hC) hIC),
    fun h I hi _ hIC ↦ by_contra fun hne ↦ hi (h hIC hne)⟩

lemma circuit_antichain : IsAntichain (· ⊆ ·) (setOf M.Circuit) :=
  fun _ hC _ hC' hne hss ↦ hne <| (Circuit.minimal hC').eq_of_subset hC.dep hss

lemma Circuit.eq_of_not_indep_subset (hC : M.Circuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma Circuit.eq_of_dep_subset (hC : M.Circuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

lemma Circuit.not_ssubset (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

lemma Circuit.eq_of_subset_circuit (hC : M.Circuit C) (hC' : M.Circuit C') (h : C ⊆ C') : C = C' :=
  hC'.eq_of_dep_subset hC.dep h

lemma circuit_iff_dep_forall_diff_singleton_indep :
    M.Circuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  rw [circuit_iff_forall_ssubset, and_congr_right_iff]
  refine fun _ ↦ ⟨fun h e heC ↦ h (Iff.mpr diff_singleton_sSubset heC), fun h I hIC ↦ ?_⟩
  obtain ⟨e, he⟩ := exists_of_ssubset hIC
  exact (h e he.1).subset (subset_diff_singleton hIC.subset he.2)

/-! ### Independence and bases -/

lemma Indep.insert_circuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.closure I)
    (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.Circuit (insert e I) := by
  rw [circuit_iff_dep_forall_diff_singleton_indep, hI.insert_dep_iff, and_iff_right ⟨he, heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_diff_singleton_comm (by rintro rfl; contradiction),
    (hI.diff _).insert_indep_iff_of_not_mem (by simp [heI])]
  exact ⟨mem_ground_of_mem_closure he, h f hfI⟩

lemma Indep.insert_circuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e ∈ M.closure I) (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.Circuit (insert e I) := by
  refine hI.insert_circuit_of_forall (fun heI ↦ ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

lemma Circuit.diff_singleton_basis (hC : M.Circuit C) (he : e ∈ C) : M.Basis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_diff_singleton, (hC.diff_singleton_indep he).basis_insert_iff,
    insert_diff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

lemma Circuit.basis_iff_eq_diff_singleton (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.diff_singleton_indep he.1)
      (subset_diff_singleton h.subset he.2) diff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.diff_singleton_basis he

lemma Circuit.basis_iff_insert_eq (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.basis_iff_eq_diff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_diff_singleton, insert_eq_of_mem he]
  rw [hC, insert_diff_self_of_not_mem he.2]

/-! ### Closure -/

lemma Circuit.closure_diff_singleton_eq (hC : M.Circuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e ∈ C)).elim
    (fun he ↦ by rw [(hC.diff_singleton_basis he).closure_eq_closure])
    (fun he ↦ by rw [diff_singleton_eq_self he])

lemma Circuit.subset_closure_diff_singleton (hC : M.Circuit C) (e : α) :
    C ⊆ M.closure (C \ {e}) := by
  by_cases he : e ∈ C
  · rw [(hC.diff_singleton_basis he).closure_eq_closure]; exact M.subset_closure _
  rw [diff_singleton_eq_self he]; exact M.subset_closure _

lemma Circuit.subset_closure_diff_subsingleton (hC : M.Circuit C) {Z : Set α}
    (hZ : Z.Subsingleton) : C ⊆ M.closure (C \ Z) := by
  obtain (rfl | ⟨x, rfl⟩) := hZ.eq_empty_or_singleton
  · simpa using M.subset_closure _
  exact hC.subset_closure_diff_singleton _

lemma Circuit.closure_diff_subsingleton_eq (hC : M.Circuit C) {Z : Set α} (hZ : Z.Subsingleton) :
    M.closure (C \ Z) = M.closure C := by
  obtain (rfl | ⟨x, rfl⟩) := hZ.eq_empty_or_singleton
  · simp
  rw [hC.closure_diff_singleton_eq]

lemma Circuit.mem_closure_diff_singleton_of_mem (hC : M.Circuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  (hC.subset_closure_diff_singleton e) heC

/-! ### Restriction -/

lemma Circuit.circuit_restrict_of_subset (hC : M.Circuit C) (hCR : C ⊆ R) :
    (M ↾ R).Circuit C := by
  simp_rw [circuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_circuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Circuit C ↔ M.Circuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.circuit_restrict_of_subset h.2⟩
  simp_rw [circuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

end Matroid
