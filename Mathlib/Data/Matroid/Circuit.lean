/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.Closure

/-!
# Matroid IsCircuits

A 'Circuit' of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

# Main Declarations

* `Matroid.IsCircuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_isCircuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Matroid.IsCircuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_isCircuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_isCircuit` : a matroid is determined by its collection of circuits.
* `Matroid.IsCircuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.IsCircuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_isCircuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.
* `Matroid.IsCocircuit M C` means that `C` is minimally dependent in `M✶`,
  or equivalently that `M.E \ C` is a hyperplane of `M`.
* `Matroid.fundCocircuit M B e` is the unique cocircuit that intersects the base `B` precisely
  in the element `e`.
* `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` : `e` is in the fundamental circuit
  for `B` and `f` iff `f` is in the fundamental cocircuit for `B` and `e`.

# Implementation Details

Since `Matroid.fundCircuit M e I` is only sensible if `I` is independent and `e ∈ M.closure I \ I`,
to avoid hypotheses being explicitly included in the definition,
junk values need to be chosen if either hypothesis fails.
The definition is chosen so that the junk values satisfy
`M.fundCircuit e I = {e}` for `e ∈ I` or `e ∉ M.E` and
`M.fundCircuit e I = insert e I` if `e ∈ M.E \ M.closure I`.
These make the useful statement `e ∈ M.fundCircuit e I ⊆ insert e I` true unconditionally.
-/

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x y : α}

open Set

namespace Matroid

/-- `M.IsCircuit C` means that `C` is a minimal dependent set in `M`. -/
def IsCircuit (M : Matroid α) := Minimal M.Dep

@[deprecated (since := "2025-02-14")] alias Circuit := IsCircuit

lemma isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C := Iff.rfl

lemma IsCircuit.dep (hC : M.IsCircuit C) : M.Dep C :=
  hC.prop

lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  hC.dep.not_indep

lemma IsCircuit.minimal (hC : M.IsCircuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : C ⊆ M.E :=
  hC.dep.subset_ground

lemma IsCircuit.nonempty (hC : M.IsCircuit C) : C.Nonempty :=
  hC.dep.nonempty

lemma empty_not_isCircuit (M : Matroid α) : ¬M.IsCircuit ∅ :=
  fun h ↦ by simpa using h.nonempty

lemma isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃D⦄, M.Dep D → D ⊆ C → D = C := by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]

lemma IsCircuit.ssubset_indep (hC : M.IsCircuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)

lemma IsCircuit.minimal_not_indep (hC : M.IsCircuit C) : Minimal (¬ M.Indep ·) C := by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a ↦ ssubset_indep hC a

lemma isCircuit_iff_minimal_not_indep (hCE : C ⊆ M.E) : M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C :=
  ⟨IsCircuit.minimal_not_indep, fun h ↦ ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC ↦ (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

lemma IsCircuit.diff_singleton_indep (hC : M.IsCircuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (diff_singleton_ssubset.2 he)

lemma isCircuit_iff_forall_ssubset : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  rw [IsCircuit, minimal_iff_forall_ssubset, and_congr_right_iff]
  exact fun h ↦ ⟨fun h' I hIC ↦ ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC ↦ (h hIC).not_dep⟩

lemma isCircuit_antichain : IsAntichain (· ⊆ ·) (setOf M.IsCircuit) :=
  fun _ hC _ hC' hne hss ↦ hne <| (IsCircuit.minimal hC').eq_of_subset hC.dep hss

lemma IsCircuit.eq_of_not_indep_subset (hC : M.IsCircuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma IsCircuit.eq_of_dep_subset (hC : M.IsCircuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

lemma IsCircuit.not_ssubset (hC : M.IsCircuit C) (hC' : M.IsCircuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

lemma IsCircuit.eq_of_subset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C ⊆ C') :
    C = C' :=
  hC'.eq_of_dep_subset hC.dep h

lemma IsCircuit.eq_of_superset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C' ⊆ C) :
    C = C' :=
  (hC'.eq_of_subset_isCircuit hC h).symm

lemma isCircuit_iff_dep_forall_diff_singleton_indep :
    M.IsCircuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  wlog hCE : C ⊆ M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h ↦ hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_diff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX ↦ hY <| hX.subset hYX)]

/-! ### Independence and bases -/

lemma Indep.insert_isCircuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.closure I)
    (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  rw [isCircuit_iff_dep_forall_diff_singleton_indep, hI.insert_dep_iff, and_iff_right ⟨he, heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_diff_singleton_comm (by rintro rfl; contradiction),
    (hI.diff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_ground_of_mem_closure he, h f hfI⟩

lemma Indep.insert_isCircuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e ∈ M.closure I) (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  refine hI.insert_isCircuit_of_forall (fun heI ↦ ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

lemma IsCircuit.diff_singleton_isBasis (hC : M.IsCircuit C) (he : e ∈ C) :
    M.IsBasis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_diff_singleton, (hC.diff_singleton_indep he).isBasis_insert_iff,
    insert_diff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

lemma IsCircuit.isBasis_iff_eq_diff_singleton (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.diff_singleton_indep he.1)
      (subset_diff_singleton h.subset he.2) diff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.diff_singleton_isBasis he

lemma IsCircuit.isBasis_iff_insert_eq (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.isBasis_iff_eq_diff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_diff_singleton, insert_eq_of_mem he]
  rw [hC, insert_diff_self_of_notMem he.2]

/-! ### Restriction -/

lemma IsCircuit.isCircuit_restrict_of_subset (hC : M.IsCircuit C) (hCR : C ⊆ R) :
    (M ↾ R).IsCircuit C := by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_isCircuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

/-! ### Fundamental IsCircuits -/

/-- For an independent set `I` and some `e ∈ M.closure I \ I`,
`M.fundCircuit e I` is the unique circuit contained in `insert e I`.
For the fact that this is a circuit, see `Matroid.Indep.fundCircuit_isCircuit`,
and the fact that it is unique, see `Matroid.IsCircuit.eq_fundCircuit_of_subset`.
Has the junk value `{e}` if `e ∈ I` or `e ∉ M.E`, and `insert e I` if `e ∈ M.E \ M.closure I`. -/
def fundCircuit (M : Matroid α) (e : α) (I : Set α) : Set α :=
  insert e (I ∩ ⋂₀ {J | J ⊆ I ∧ M.closure {e} ⊆ M.closure J})

lemma fundCircuit_eq_sInter (he : e ∈ M.closure I) :
    M.fundCircuit e I = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}) := by
  rw [fundCircuit]
  simp_rw [closure_subset_closure_iff_subset_closure
    (show {e} ⊆ M.E by simpa using mem_ground_of_mem_closure he), singleton_subset_iff]
  rw [inter_eq_self_of_subset_right (sInter_subset_of_mem (by simpa))]

lemma fundCircuit_subset_insert (M : Matroid α) (e : α) (I : Set α) :
    M.fundCircuit e I ⊆ insert e I :=
  insert_subset_insert inter_subset_left

lemma fundCircuit_subset_ground (he : e ∈ M.E) (hI : I ⊆ M.E := by aesop_mat) :
    M.fundCircuit e I ⊆ M.E :=
  (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)

lemma mem_fundCircuit (M : Matroid α) (e : α) (I : Set α) : e ∈ fundCircuit M e I :=
  mem_insert ..

lemma fundCircuit_diff_eq_inter (M : Matroid α) (heI : e ∉ I) :
    (M.fundCircuit e I) \ {e} = (M.fundCircuit e I) ∩ I :=
  (subset_inter diff_subset (by simp [fundCircuit_subset_insert])).antisymm
    (subset_diff_singleton inter_subset_left (by simp [heI]))

/-- The fundamental isCircuit of `e` and `X` has the junk value `{e}` if `e ∈ X` -/
lemma fundCircuit_eq_of_mem (heX : e ∈ X) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h ↦ h _ (singleton_subset_iff.2 heX) Subset.rfl

lemma fundCircuit_eq_of_notMem_ground (heX : e ∉ M.E) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h ↦ by simpa using h ∅ (empty_subset X) rfl.subset

@[deprecated (since := "2025-05-23")]
alias fundCircuit_eq_of_not_mem_ground := fundCircuit_eq_of_notMem_ground

lemma Indep.fundCircuit_isCircuit (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    M.IsCircuit (M.fundCircuit e I) := by
  have aux : ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J} ⊆ I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show ∃ x ⊆ I, e ∈ M.closure x ∧ e ∉ x from ⟨I, by simp [hecl, heI]⟩]
  · rw [hI.closure_sInter_eq_biInter_closure_of_forall_subset ⟨I, by simpa⟩ (by simp +contextual)]
    simp
  simp only [mem_sInter, mem_setOf_eq, and_imp]
  exact fun f hf hecl ↦ (hf _ (diff_subset.trans aux) hecl).2 rfl

lemma Indep.mem_fundCircuit_iff (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    x ∈ M.fundCircuit e I ↔ M.Indep (insert e I \ {x}) := by
  obtain rfl | hne := eq_or_ne x e
  · simp [hI.diff, mem_fundCircuit]
  suffices (∀ t ⊆ I, e ∈ M.closure t → x ∈ t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter hecl, hne, ← insert_diff_singleton_comm hne.symm,
      (hI.diff _).insert_indep_iff, mem_ground_of_mem_closure hecl, heI]
  refine ⟨fun h hecl ↦ (h _ diff_subset hecl).2 rfl, fun h J hJ heJ ↦ by_contra fun hxJ ↦ h ?_⟩
  exact M.closure_subset_closure (subset_diff_singleton hJ hxJ) heJ

lemma IsBase.fundCircuit_isCircuit {B : Set α} (hB : M.IsBase B) (hxE : x ∈ M.E) (hxB : x ∉ B) :
    M.IsCircuit (M.fundCircuit x B) :=
  hB.indep.fundCircuit_isCircuit (by rwa [hB.closure_eq]) hxB

/-- For `I` independent, `M.fundCircuit e I` is the only circuit contained in `insert e I`. -/
lemma IsCircuit.eq_fundCircuit_of_subset (hC : M.IsCircuit C) (hI : M.Indep I)
    (hCs : C ⊆ insert e I) : C = M.fundCircuit e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I ⊆ C by
    refine hC.eq_of_superset_isCircuit (hI.fundCircuit_isCircuit ?_ fun heI ↦ ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.superset hCs (insert_subset (hC.subset_ground heC) hI.subset_ground))
    exact hC.not_indep (hI.subset (hCs.trans (by simp [heI])))
  have heCcl := (hC.diff_singleton_isBasis heC).subset_closure heC
  have heI : e ∈ M.closure I := M.closure_subset_closure hCeI heCcl
  rw [fundCircuit_eq_sInter heI]
  refine insert_subset heC <| (sInter_subset_of_mem (t := C \ {e}) ?_).trans diff_subset
  exact ⟨hCeI, heCcl⟩

lemma fundCircuit_restrict {R : Set α} (hIR : I ⊆ R) (heR : e ∈ R) (hR : R ⊆ M.E) :
    (M ↾ R).fundCircuit e I = M.fundCircuit e I := by
  simp_rw [fundCircuit, M.restrict_closure_eq (R := R) (X := {e}) (by simpa)]
  refine subset_antisymm (insert_subset_insert (inter_subset_inter_right _ ?_))
    (insert_subset_insert (inter_subset_inter_right _ ?_))
  · refine subset_sInter fun J ⟨hJI, heJ⟩ ↦ sInter_subset_of_mem ⟨hJI, ?_⟩
    simp only [restrict_closure_eq', union_subset_iff, subset_union_right, and_true]
    refine (inter_subset_inter_left _ ?_).trans subset_union_left
    rwa [inter_eq_self_of_subset_left (hJI.trans hIR)]
  refine subset_sInter fun J ⟨hJI, heJ⟩ ↦ sInter_subset_of_mem
    ⟨hJI, M.closure_subset_closure_of_subset_closure ?_⟩
  rw [restrict_closure_eq _ (hJI.trans hIR) hR] at heJ
  simp only [subset_inter_iff, inter_subset_right, and_true] at heJ
  exact subset_trans (by simpa [M.mem_closure_of_mem' (mem_singleton e) (hR heR)]) heJ

@[simp] lemma fundCircuit_restrict_univ (M : Matroid α) :
    (M ↾ univ).fundCircuit e I = M.fundCircuit e I := by
  have aux (A B) : M.closure A ⊆ B ∪ univ \ M.E ↔ M.closure A ⊆ B := by
    refine ⟨fun h ↦ ?_, fun h ↦ h.trans subset_union_left⟩
    refine (subset_inter h (M.closure_subset_ground A)).trans ?_
    simp [union_inter_distrib_right]
  simp [fundCircuit, aux]

/-! ### Dependence -/

lemma Dep.exists_isCircuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.IsCircuit C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_isCircuit (hI.subset_closure heX) heI⟩

lemma dep_iff_superset_isCircuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.IsCircuit C :=
  ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.dep_iff_superset_isCircuit` that has the supportedness hypothesis
as part of the equivalence, rather than a hypothesis. -/
lemma dep_iff_superset_isCircuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.IsCircuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.indep_iff_forall_subset_not_isCircuit` that has the supportedness
hypothesis as part of the equivalence, rather than a hypothesis. -/
lemma indep_iff_forall_subset_not_isCircuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.IsCircuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop

lemma indep_iff_forall_subset_not_isCircuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.IsCircuit C := by
  rw [indep_iff_forall_subset_not_isCircuit', and_iff_left hI]

/-! ### Closure -/

lemma IsCircuit.closure_diff_singleton_eq (hC : M.IsCircuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e ∈ C)).elim
    (fun he ↦ by rw [(hC.diff_singleton_isBasis he).closure_eq_closure])
    (fun he ↦ by rw [diff_singleton_eq_self he])

lemma IsCircuit.subset_closure_diff_singleton (hC : M.IsCircuit C) (e : α) :
    C ⊆ M.closure (C \ {e}) := by
  rw [hC.closure_diff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

lemma IsCircuit.mem_closure_diff_singleton_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  hC.subset_closure_diff_singleton e heC

lemma exists_isCircuit_of_mem_closure (he : e ∈ M.closure X) (heX : e ∉ X) :
    ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  let ⟨I, hI⟩ := M.exists_isBasis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_isCircuit (by rwa [hI.closure_eq_closure]) (notMem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

lemma mem_closure_iff_exists_isCircuit (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  ⟨fun h ↦ exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ ↦ mem_of_mem_of_subset
    (hC.mem_closure_diff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

/-! ### Extensionality -/

lemma ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃C⦄, C ⊆ M₁.E → (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ = M₂ := by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C ⊆ M₁.E)).elim (h (C := C)) (fun hC ↦ iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss ↦ hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI ↦ ?_
  simp_rw [indep_iff_forall_subset_not_isCircuit hI, h',
    indep_iff_forall_subset_not_isCircuit (hI.trans_eq hE)]

/-- A stronger version of `Matroid.ext_isCircuit`:
two matroids on the same ground set are equal if no circuit of one is independent in the other. -/
lemma ext_isCircuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : ∀ C, M₁.IsCircuit C → ¬ M₂.Indep C) (h₂ : ∀ C, M₂.IsCircuit C → ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_isCircuit hE fun C hCE ↦ ⟨fun hC ↦ ?_, fun hC ↦ ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCircuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ C' hC') hC'C]

lemma ext_iff_isCircuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C, M₁.IsCircuit C ↔ M₂.IsCircuit C :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_isCircuit h.1 fun C hC ↦ h.2 (C := C)⟩

section Elimination

/-! ### Circuit Elimination -/

variable {ι : Type*} {J C₀ C₁ C₂ : Set α}

/-- A version of `Matroid.IsCircuit.strong_multi_elimination` that is phrased using insertion. -/
lemma IsCircuit.strong_multi_elimination_insert (x : ι → α) (I : ι → Set α) (z : α)
    (hxI : ∀ i, x i ∉ I i) (hC : ∀ i, M.IsCircuit (insert (x i) (I i)))
    (hJx : M.IsCircuit (J ∪ range x)) (hzJ : z ∈ J) (hzI : ∀ i, z ∉ I i) :
    ∃ C' ⊆ J ∪ ⋃ i, I i, M.IsCircuit C' ∧ z ∈ C' := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z ∈ M.closure ((⋃ i, I i) ∪ (J \ {z})) by
    rw [mem_closure_iff_exists_isCircuit (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', ?_, hC', hzC'⟩
    rwa [union_comm, ← insert_union, insert_diff_singleton, insert_eq_of_mem hzJ] at hC'ss
  have hC' (i) : M.closure (I i) = M.closure (insert (x i) (I i)) := by
    simpa [diff_singleton_eq_self (hxI _)] using (hC i).closure_diff_singleton_eq (x i)
  -- This is true because each `I i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hC',
    iUnion_insert_eq_range_union_iUnion, union_right_comm]
  refine mem_of_mem_of_subset (hJx.mem_closure_diff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_diff_distrib, union_comm]
  exact union_subset_union_left _ diff_subset

/-- A generalization of the strong circuit elimination axiom `Matroid.IsCircuit.strong_elimination`
to an infinite collection of circuits.

It states that, given a circuit `C₀`, a arbitrary collection `C : ι → Set α` of circuits,
an element `x i` of `C₀ ∩ C i` for each `i`, and an element `z ∈ C₀` outside all the `C i`,
the union of `C₀` and the `C i` contains a circuit containing `z` but none of the `x i`.

This is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed. -/
lemma IsCircuit.strong_multi_elimination (hC₀ : M.IsCircuit C₀) (x : ι → α) (C : ι → Set α) (z : α)
    (hC : ∀ i, M.IsCircuit (C i)) (h_mem_C₀ : ∀ i, x i ∈ C₀) (h_mem : ∀ i, x i ∈ C i)
    (h_unique : ∀ ⦃i i'⦄, x i ∈ C i' → i = i') (hzC₀ : z ∈ C₀) (hzC : ∀ i, z ∉ C i) :
    ∃ C' ⊆ (C₀ ∪ ⋃ i, C i) \ range x, M.IsCircuit C' ∧ z ∈ C' := by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i ↦ (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i ↦ ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (diff_subset_diff_left subset_union_left)
      (iUnion_subset fun i ↦ subset_diff.2
        ⟨diff_subset.trans (subset_union_of_subset_right (subset_iUnion ..) _), ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro _ he _ ⟨j, hj, rfl⟩ rfl
    obtain rfl : j = i := h_unique he.1
    simp at he
  · simpa [insert_eq_of_mem (h_mem i)] using hC i
  · rwa [diff_union_self, union_eq_self_of_subset_right]
    rintro _ ⟨i, hi, rfl⟩
    exact h_mem_C₀ i
  · rintro ⟨i, hi, rfl⟩
    exact hzC _ (h_mem i)
  simp only [mem_diff, mem_singleton_iff, not_and, not_not]
  exact fun i hzi ↦ (hzC i hzi).elim

/-- A version of `Circuit.strong_multi_elimination` where the collection of circuits is
a `Set (Set α)` and the distinguished elements are a `Set α`, rather than both being indexed. -/
lemma IsCircuit.strong_multi_elimination_set (hC₀ : M.IsCircuit C₀) (X : Set α) (S : Set (Set α))
    (z : α) (hCS : ∀ C ∈ S, M.IsCircuit C) (hXC₀ : X ⊆ C₀) (hX : ∀ x ∈ X, ∃ C ∈ S, C ∩ X = {x})
    (hzC₀ : z ∈ C₀) (hz : ∀ C ∈ S, z ∉ C) : ∃ C' ⊆ (C₀ ∪ ⋃₀ S) \ X, M.IsCircuit C' ∧ z ∈ C' := by
  choose! C hC using hX
  simp only [and_imp, forall_and, and_assoc] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X ↦ x) (fun x ↦ C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (diff_subset_diff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
    simpa using fun e heX ↦ (subset_sUnion_of_mem (hC.1 e heX))
  · simpa using fun e heX ↦ hCS _ <| hC.1 e heX
  · simpa using fun e heX ↦ hXC₀ heX
  · simp only [Subtype.forall, ← singleton_subset_iff (s := C _)]
    exact fun e heX ↦ by simp [← hC.2 e heX]
  · simp only [Subtype.forall, Subtype.mk.injEq]
    refine fun e heX f hfX hef ↦ ?_
    simpa [hC.2 f hfX] using subset_inter (singleton_subset_iff.2 hef) (singleton_subset_iff.2 heX)
  simpa using fun e heX heC ↦ hz _ (hC.1 e heX) heC

/-- The strong isCircuit elimination axiom. For any pair of distinct circuits `C₁, C₂` and all
`e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma IsCircuit.strong_elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (heC₁ : e ∈ C₁)
    (heC₂ : e ∈ C₂) (hfC₁ : f ∈ C₁) (hfC₂ : f ∉ C₂) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C ∧ f ∈ C := by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit ↦ e) (fun _ ↦ C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (diff_subset_diff (by simp) (by simp)), hC, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁, C₂` and any `e`,
some circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when defining a finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`. -/
lemma IsCircuit.elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C := by
  have hnss : ¬ (C₁ ⊆ C₂) := fun hss ↦ h <| hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subset_diff_singleton subset_union_right he₂, hC₂⟩
  exact ⟨C₁, subset_diff_singleton subset_union_left he₁, hC₁⟩

end Elimination

/-! ### Finitary Matroids -/
section Finitary

lemma IsCircuit.finite [Finitary M] (hC : M.IsCircuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push_neg at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

lemma finitary_iff_forall_isCircuit_finite : M.Finitary ↔ ∀ C, M.IsCircuit C → C.Finite := by
  refine ⟨fun _ _ ↦ IsCircuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

/-- In a finitary matroid, every element spanned by a set `X` is in fact
spanned by a finite independent subset of `X`. -/
lemma exists_mem_finite_closure_of_mem_closure [M.Finitary] (he : e ∈ M.closure X) :
    ∃ I ⊆ X, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  by_cases heY : e ∈ X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.diff, hC.diff_singleton_indep heC,
    hC.mem_closure_diff_singleton_of_mem heC⟩

/-- In a finitary matroid, each finite set `X` spanned by a set `Y` is in fact
spanned by a finite independent subset of `Y`. -/
lemma exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite)
    (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by
  suffices aux : ∃ T ⊆ Y, T.Finite ∧ X ⊆ M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨∅, by simp⟩ (fun {e Z} heX _ heZ ⟨T, hTY, hTfin, hT⟩ ↦ ?_)
  obtain ⟨S, hSY, hSfin, -, heS⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  exact ⟨S ∪ T, union_subset hSY hTY, hSfin.union hTfin, insert_subset
    (M.closure_mono subset_union_left heS) (hT.trans (M.closure_mono subset_union_right))⟩

end Finitary

/-! ### IsCocircuits -/
section IsCocircuit

variable {K B : Set α}

/-- A cocircuit is a circuit of the dual matroid,
or equivalently the complement of a hyperplane. -/
abbrev IsCocircuit (M : Matroid α) (K : Set α) : Prop := M✶.IsCircuit K

lemma isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircuit K := Iff.rfl

lemma IsCocircuit.isCircuit (hK : M.IsCocircuit K) : M✶.IsCircuit K :=
  hK

lemma IsCircuit.isCocircuit (hC : M.IsCircuit C) : M✶.IsCocircuit C := by
  rwa [isCocircuit_def, dual_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsCocircuit.subset_ground (hC : M.IsCocircuit C) : C ⊆ M.E :=
  hC.isCircuit.subset_ground

@[simp] lemma dual_isCocircuit_iff : M✶.IsCocircuit C ↔ M.IsCircuit C := by
  rw [isCocircuit_def, dual_dual]

lemma coindep_iff_forall_subset_not_isCocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.IsCocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_isCircuit'

/-- A cocircuit is a minimal set that intersects every base. -/
lemma isCocircuit_iff_minimal :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ∀ B, M.IsBase B → (X ∩ B).Nonempty) K := by
  have aux : M✶.Dep = fun X ↦ (∀ B, M.IsBase B → (X ∩ B).Nonempty) ∧ X ⊆ M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def, isCircuit_def, aux, iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1) fun X hX ↦
    ⟨X ∩ M.E, inter_subset_left, fun B hB ↦ ?_, inter_subset_right⟩
  rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

/-- A cocircuit is a minimal set whose complement is nonspanning. -/
lemma isCocircuit_iff_minimal_compl_nonspanning :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X)) K := by
  convert isCocircuit_iff_minimal with K
  simp_rw [spanning_iff_exists_isBase_subset (S := M.E \ K), not_exists, subset_diff, not_and,
    not_disjoint_iff_nonempty_inter, ← and_imp, and_iff_left_of_imp IsBase.subset_ground,
    inter_comm K]

/-- For an element `e` of a base `B`, the complement of the closure of `B \ {e}` is a cocircuit. -/
lemma IsBase.compl_closure_diff_singleton_isCocircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsCocircuit (M.E \ M.closure (B \ {e})) := by
  rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_subset_iff,
    diff_diff_cancel_left (M.closure_subset_ground _),
    closure_spanning_iff (diff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp ↦ hB'.notMem_of_prop_diff_singleton hsp he, fun X hX hXss ↦ hXss.antisymm' ?_⟩
  rw [diff_subset_comm]
  refine fun f hf ↦ by_contra fun fcl ↦ hX ?_
  rw [subset_diff] at hXss
  suffices hsp : M.IsBase (insert f (B \ {e})) by
    refine hsp.spanning.superset <| insert_subset hf <|
      (M.subset_closure _ (diff_subset.trans hB.subset_ground)).trans ?_
    rw [subset_diff, and_iff_left hXss.2.symm]
    apply closure_subset_ground
  exact hB.exchange_base_of_notMem_closure he fcl

/-- A version of `Matroid.isCocircuit_iff_minimal_compl_nonspanning` with a support assumption
in the minimality. -/
lemma isCocircuit_iff_minimal_compl_nonspanning' :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X) ∧ X ⊆ M.E) K := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1)
    (fun X hX ↦ ⟨X ∩ M.E, inter_subset_left, by rwa [diff_inter_self_eq_diff], inter_subset_right⟩)

/-- A cocircuit and a circuit cannot meet in exactly one element. -/
lemma IsCircuit.inter_isCocircuit_ne_singleton (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    C ∩ K ≠ {e} := by
  intro he
  have heC : e ∈ C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (diff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  nth_rw 1 [← hKe.closure_eq, diff_diff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← closure_union_congr_right
      (hC.closure_diff_singleton_eq e), union_eq_self_of_subset_right]
    rw [← he, diff_self_inter]
    exact diff_subset_diff_left hC.subset_ground
  rw [← he]
  exact inter_subset_left.trans hC.subset_ground

lemma IsCircuit.isCocircuit_inter_nontrivial (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter (hC : M.IsCircuit C)
    (hK : M.IsCocircuit K) : Disjoint C K ∨ (C ∩ K).Nontrivial := by
  rw [or_iff_not_imp_left, disjoint_iff_inter_eq_empty, ← ne_eq, ← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

lemma dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ ∃ C, M.IsCircuit C := by
  rw [rankPos_iff, dual_isBase_iff, diff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_isBase, indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma IsCircuit.dual_rankPos (hC : M.IsCircuit C) : M✶.RankPos :=
  dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

lemma exists_isCircuit [RankPos M✶] : ∃ C, M.IsCircuit C :=
  dual_rankPos_iff_exists_isCircuit.1 (by assumption)

lemma rankPos_iff_exists_isCocircuit : M.RankPos ↔ ∃ K, M.IsCocircuit K := by
  rw [← dual_dual M, dual_rankPos_iff_exists_isCircuit, dual_dual M]

/-- The fundamental cocircuit for `B` and `e`:
that is, the unique cocircuit `K` of `M` for which `K ∩ B = {e}`.
Should be used when `B` is a base and `e ∈ B`.
Has the junk value `{e}` if `e ∉ B` or `e ∉ M.E`. -/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) := M✶.fundCircuit e (M✶.E \ B)

lemma fundCocircuit_isCocircuit (he : e ∈ B) (hB : M.IsBase B) :
    M.IsCocircuit <| M.fundCocircuit e B := by
  apply hB.compl_isBase_dual.indep.fundCircuit_isCircuit _ (by simp [he])
  rw [hB.compl_isBase_dual.closure_eq, dual_ground]
  exact hB.subset_ground he

lemma mem_fundCocircuit (M : Matroid α) (e : α) (B : Set α) : e ∈ M.fundCocircuit e B :=
  mem_insert _ _

lemma fundCocircuit_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocircuit e B ⊆ insert e (M.E \ B) :=
  fundCircuit_subset_insert ..

lemma fundCocircuit_inter_eq (M : Matroid α) {B : Set α} (he : e ∈ B) :
    (M.fundCocircuit e B) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocircuit _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocircuit_subset_insert_compl _ _)).trans ?_
  simp +contextual

/-- The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ M.E` -/
lemma fundCocircuit_eq_of_notMem_ground (X : Set α) (he : e ∉ M.E) :
    M.fundCocircuit e X = {e} := by
  rwa [fundCocircuit, fundCircuit_eq_of_notMem_ground]

@[deprecated (since := "2025-05-23")]
alias fundCocircuit_eq_of_not_mem_ground := fundCocircuit_eq_of_notMem_ground

/-- The fundamental cocircuit of `X` and `e` has the junk value `{e}` if `e ∉ X` -/
lemma fundCocircuit_eq_of_notMem (M : Matroid α) (heX : e ∉ X) : M.fundCocircuit e X = {e} := by
  by_cases he : e ∈ M.E
  · rw [fundCocircuit, fundCircuit_eq_of_mem]
    exact ⟨he, heX⟩
  rw [fundCocircuit_eq_of_notMem_ground _ he]

@[deprecated (since := "2025-05-23")]
alias fundCocircuit_eq_of_not_mem := fundCocircuit_eq_of_notMem

/-- For every element `e` of an independent set `I`,
there is a cocircuit whose intersection with `I` is `{e}`. -/
lemma Indep.exists_isCocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.IsCocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨M.fundCocircuit e B, fundCocircuit_isCocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocircuit _ _ _), singleton_subset_iff, and_iff_left heI,
    ← M.fundCocircuit_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

/-- Fundamental circuits and cocircuits of a base `B` play dual roles;
`e` belongs to the fundamental cocircuit for `B` and `f` if and only if
`f` belongs to the fundamental circuit for `e` and `B`.
This statement isn't so reasonable unless `f ∈ B` and `e ∉ B`,
but holds due to junk values even without these assumptions. -/
lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.IsBase B) :
    e ∈ M.fundCocircuit f B ↔ f ∈ M.fundCircuit e B := by
  -- By symmetry and duality, it suffices to show the implication in one direction.
  suffices aux : ∀ {N : Matroid α} {B' : Set α} (hB' : N.IsBase B') {e f},
      e ∈ N.fundCocircuit f B' → f ∈ N.fundCircuit e B' from
    ⟨fun h ↦ aux hB h , fun h ↦ aux hB.compl_isBase_dual <| by
      simpa [fundCocircuit, inter_eq_self_of_subset_right hB.subset_ground]⟩
  clear! B M e f
  intro M B hB e f he
  -- discharge the various degenerate cases.
  obtain rfl | hne := eq_or_ne e f
  · simp [mem_fundCircuit]
  have hB' : M✶.IsBase (M✶.E \ B) := hB.compl_isBase_dual
  obtain hfE | hfE := em' <| f ∈ M.E
  · rw [fundCocircuit, fundCircuit_eq_of_notMem_ground (by simpa)] at he
    contradiction
  obtain hfB | hfB := em' <| f ∈ B
  · rw [fundCocircuit, fundCircuit_eq_of_mem (by simp [hfE, hfB])] at he
    contradiction
  obtain ⟨heE, heB⟩ : e ∈ M.E \ B :=
    by simpa [hne] using (M.fundCocircuit_subset_insert_compl f B) he
  -- Use basis exchange to argue the equivalence.
  rw [fundCocircuit, hB'.indep.mem_fundCircuit_iff (by rwa [hB'.closure_eq]) (by simp [hfB])] at he
  rw [hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) heB]
  have hB' : M.IsBase (M.E \ (insert f (M✶.E \ B) \ {e})) :=
    (hB'.exchange_isBase_of_indep' ⟨heE, heB⟩ (by simp [hfE, hfB]) he).compl_isBase_of_dual
  refine hB'.indep.subset ?_
  simp only [dual_ground, diff_singleton_subset_iff]
  rw [diff_diff_right, inter_eq_self_of_subset_right (by simpa), union_singleton, insert_comm,
    ← union_singleton (s := M.E \ B), ← diff_diff, diff_diff_cancel_left hB.subset_ground]
  simp [hfB]

end IsCocircuit

end Matroid
