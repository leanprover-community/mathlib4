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

* `Matroid.Circuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_circuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Circuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_circuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_circuit` : a matroid is determined by its collection of circuits.

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

lemma Circuit.minimal_not_indep (hC : M.Circuit C) : Minimal (¬ M.Indep ·) C := by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a ↦ ssubset_indep hC a

lemma circuit_iff_minimal_not_indep (hCE : C ⊆ M.E) : M.Circuit C ↔ Minimal (¬ M.Indep ·) C :=
  ⟨Circuit.minimal_not_indep, fun h ↦ ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC ↦ (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

lemma Circuit.diff_singleton_indep (hC : M.Circuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (diff_singleton_sSubset.2 he)

lemma circuit_iff_forall_ssubset : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  rw [Circuit, minimal_iff_forall_ssubset, and_congr_right_iff]
  exact fun h ↦ ⟨fun h' I hIC ↦ ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC ↦ (h hIC).not_dep⟩

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

lemma Circuit.eq_of_superset_circuit (hC : M.Circuit C) (hC' : M.Circuit C') (h : C' ⊆ C) :
    C = C' :=
  (hC'.eq_of_subset_circuit hC h).symm

lemma circuit_iff_dep_forall_diff_singleton_indep :
    M.Circuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  wlog hCE : C ⊆ M.E
  · exact iff_of_false (hCE ∘ Circuit.subset_ground) (fun h ↦ hCE h.1.subset_ground)
  simp [circuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_diff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX ↦ hY <| hX.subset hYX)]

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
  rw [hC.closure_diff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

lemma Circuit.mem_closure_diff_singleton_of_mem (hC : M.Circuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  (hC.subset_closure_diff_singleton e) heC

/-! ### Restriction -/

lemma Circuit.circuit_restrict_of_subset (hC : M.Circuit C) (hCR : C ⊆ R) : (M ↾ R).Circuit C := by
  simp_rw [circuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_circuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Circuit C ↔ M.Circuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.circuit_restrict_of_subset h.2⟩
  simp_rw [circuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

/-! ### Fundamental Circuits -/

/-- For an independent set `I` and some `e ∈ M.closure I \ I`,
`M.fundCircuit e I` is the unique circuit contained in `insert e I`.
For the fact that this is a circuit, see `Matroid.Indep.fundCircuit_circuit`,
and the fact that it is unique, see `Matroid.Circuit.eq_fundCircuit_of_subset`.
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

/-- The fundamental circuit of `e` and `X` has the junk value `{e}` if `e ∈ X` -/
lemma fundCircuit_eq_of_mem (heX : e ∈ X) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun b hbX h ↦ h _ (singleton_subset_iff.2 heX) Subset.rfl

lemma fundCircuit_eq_of_not_mem_ground (heX : e ∉ M.E) : M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ t ⊆ X, M.closure {e} ⊆ M.closure t → a ∈ t) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  simp_rw [← M.closure_inter_ground {e}, singleton_inter_eq_empty.2 heX]
  exact fun a haX h ↦ by simpa using h ∅ (empty_subset X) rfl.subset

lemma Indep.fundCircuit_circuit (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    M.Circuit (M.fundCircuit e I) := by
  have aux : ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J} ⊆ I := sInter_subset_of_mem (by simpa)
  rw [fundCircuit_eq_sInter hecl]
  refine (hI.subset aux).insert_circuit_of_forall ?_ ?_ ?_
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

lemma Base.fundCircuit_circuit {B : Set α} (hB : M.Base B) (hxE : x ∈ M.E) (hxB : x ∉ B) :
    M.Circuit (M.fundCircuit x B) :=
  hB.indep.fundCircuit_circuit (by rwa [hB.closure_eq]) hxB

/-- For `I` independent, `M.fundCircuit e I` is the only circuit contained in `insert e I`. -/
lemma Circuit.eq_fundCircuit_of_subset (hC : M.Circuit C) (hI : M.Indep I) (hCss : C ⊆ insert e I) :
    C = M.fundCircuit e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCss
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I ⊆ C by
    refine hC.eq_of_superset_circuit (hI.fundCircuit_circuit ?_ fun heI ↦ ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.superset hCss (insert_subset (hC.subset_ground heC) hI.subset_ground))
    exact hC.not_indep (hI.subset (hCss.trans (by simp [heI])))
  rw [fundCircuit_eq_sInter <|
    M.closure_subset_closure hCeI <| hC.mem_closure_diff_singleton_of_mem heC]
  refine insert_subset heC <| (sInter_subset_of_mem (t := C \ {e}) ?_).trans diff_subset
  simp [hCss, hC.mem_closure_diff_singleton_of_mem heC]

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

lemma Dep.exists_circuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.Circuit C := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  exact ⟨M.fundCircuit e I, (M.fundCircuit_subset_insert e I).trans (insert_subset heX hI.subset),
    hI.indep.fundCircuit_circuit (hI.subset_closure heX) heI⟩

lemma dep_iff_superset_circuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.Circuit C :=
  ⟨Dep.exists_circuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.dep_iff_superset_circuit` that has the supportedness hypothesis
as part of the equivalence, rather than a hypothesis. -/
lemma dep_iff_superset_circuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.Circuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_circuit_subset, h.subset_ground⟩, fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.indep_iff_forall_subset_not_circuit` that has the supportedness hypothesis
as part of the equivalence, rather than a hypothesis. -/
lemma indep_iff_forall_subset_not_circuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.Circuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_circuit']
  aesop

lemma indep_iff_forall_subset_not_circuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.Circuit C := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]

/-! ### Extensionality -/

lemma ext_circuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃C⦄, C ⊆ M₁.E → (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  have h' {C} : M₁.Circuit C ↔ M₂.Circuit C :=
    (em (C ⊆ M₁.E)).elim (h (C := C)) (fun hC ↦ iff_of_false (mt Circuit.subset_ground hC)
      (mt Circuit.subset_ground fun hss ↦ hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI ↦ ?_
  simp_rw [indep_iff_forall_subset_not_circuit hI, h',
    indep_iff_forall_subset_not_circuit (hI.trans_eq hE)]

/-- A stronger version of `Matroid.ext_circuit`:
two matroids on the same ground set are equal if no circuit of one is independent in the other. -/
lemma ext_circuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : ∀ C, M₁.Circuit C → ¬ M₂.Indep C) (h₂ : ∀ C, M₂.Circuit C → ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_circuit hE fun C hCE ↦ ⟨fun hC ↦ ?_, fun hC ↦ ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_circuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_circuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ C' hC') hC'C]

lemma ext_iff_circuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C, M₁.Circuit C ↔ M₂.Circuit C :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_circuit h.1 fun C hC ↦ h.2 (C := C)⟩

end Matroid
