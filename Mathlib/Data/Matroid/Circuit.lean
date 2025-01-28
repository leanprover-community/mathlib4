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
* `Matroid.Circuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.Circuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_circuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.

# Implementation Details

Since `Matroid.fundCircuit M e I` is only sensible if `I` is independent and `e ∈ M.closure I \ I`,
to avoid hypotheses being explicitly included in the definition,
junk values need to be chosen if either hypothesis fails.
The definition is chosen so that the junk values satisfy
`M.fundCircuit e I = {e}` for `e ∈ I` and
`M.fundCircuit e I = insert e I` if `e ∉ M.closure I`.
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
Has the junk value `{e}` if `e ∈ I` and `insert e I` if `e ∉ M.closure I`. -/
def fundCircuit (M : Matroid α) (e : α) (I : Set α) : Set α :=
  insert e (I ∩ (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}))

lemma fundCircuit_eq_sInter (he : e ∈ M.closure I) :
    M.fundCircuit e I = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}) := by
  rw [fundCircuit, inter_eq_self_of_subset_right]
  exact sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma fundCircuit_subset_insert (M : Matroid α) (e : α) (I : Set α) :
    M.fundCircuit e I ⊆ insert e I :=
  insert_subset_insert inter_subset_left

lemma fundCircuit_subset_ground (he : e ∈ M.E) (hI : I ⊆ M.E := by aesop_mat) :
    M.fundCircuit e I ⊆ M.E :=
  (M.fundCircuit_subset_insert e I).trans (insert_subset he hI)

lemma mem_fundCircuit (M : Matroid α) (e : α) (I : Set α) : e ∈ fundCircuit M e I :=
  mem_insert ..

/-- The fundamental circuit of `e` and `X` has the junk value `{e}` if `e ∈ X` -/
lemma fundCircuit_eq_of_mem (heX : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    M.fundCircuit e X = {e} := by
  suffices h : ∀ a ∈ X, (∀ I ⊆ X, e ∈ M.closure I → a ∈ I) → a = e by
    simpa [subset_antisymm_iff, fundCircuit]
  exact fun f hfX h ↦ h {e} (by simpa) (mem_closure_of_mem' _ rfl)

/-- A version of `Matroid.fundCircuit_eq_of_mem` that applies when `X ⊆ M.E` instead of `e ∈ X`.-/
lemma fundCircuit_eq_of_mem' (heX : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.fundCircuit e X = {e} := by
  rwa [fundCircuit_eq_of_mem]

lemma Indep.fundCircuit_circuit (hI : M.Indep I) (hecl : e ∈ M.closure I) (heI : e ∉ I) :
    M.Circuit (M.fundCircuit e I) := by
  apply (hI.inter_right _).insert_circuit_of_forall (by simp [heI])
  · rw [(hI.subset _).closure_inter_eq_inter_closure, mem_inter_iff, and_iff_right hecl,
      hI.closure_sInter_eq_biInter_closure_of_forall_subset _ (by simp +contextual)]
    · simp
    · exact ⟨I, rfl.subset, hecl⟩
    exact union_subset rfl.subset (sInter_subset_of_mem ⟨rfl.subset, hecl⟩)
  simp only [mem_inter_iff, mem_sInter, mem_setOf_eq, and_imp]
  exact fun f hfI hf hecl ↦ (hf _ (diff_subset.trans inter_subset_left) hecl).2 rfl

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
lemma Circuit.eq_fundCircuit_of_subset (hC : M.Circuit C) (hI : M.Indep I) (hCs : C ⊆ insert e I) :
    C = M.fundCircuit e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I ⊆ C by
    refine hC.eq_of_superset_circuit (hI.fundCircuit_circuit ?_ fun heI ↦ ?_) hss
    · rw [hI.mem_closure_iff]
      exact .inl (hC.dep.superset hCs (insert_subset (hC.subset_ground heC) hI.subset_ground))
    exact hC.not_indep (hI.subset (hCs.trans (by simp [heI])))
  refine insert_subset heC (inter_subset_right.trans ?_)
  refine (sInter_subset_of_mem (t := C \ {e}) ?_).trans diff_subset
  simp [hCs, (hC.diff_singleton_basis heC).closure_eq_closure, M.mem_closure_of_mem heC]

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

lemma exists_circuit_of_mem_closure (he : e ∈ M.closure X) (heX : e ∉ X) :
    ∃ C ⊆ insert e X, M.Circuit C ∧ e ∈ C :=
  let ⟨I, hI⟩ := M.exists_basis' X
  ⟨_, (fundCircuit_subset_insert ..).trans (insert_subset_insert hI.subset),
    hI.indep.fundCircuit_circuit (by rwa [hI.closure_eq_closure]) (not_mem_subset
    hI.subset heX), M.mem_fundCircuit e I⟩

lemma mem_closure_iff_exists_circuit_of_not_mem (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C ⊆ insert e X, M.Circuit C ∧ e ∈ C :=
  ⟨fun h ↦ exists_circuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ ↦ mem_of_mem_of_subset
    (hC.mem_closure_diff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

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

section Elimination

/-! ### Circuit Elimination -/

variable {ι : Type*} (x : ι → α) {z : α} {C₁ C₂ : Set α}

/-- A version of `Matroid.Circuit.strong_multi_elimination` that is phrased using insertion. -/
lemma strong_multi_elimination_insert (I : ι → Set α) (hxI : ∀ i, x i ∉ I i) {J : Set α}
    (hC : ∀ i, M.Circuit (insert (x i) (I i))) (hJx : M.Circuit (J ∪ range x)) (hzJ : z ∈ J)
    (hzI : ∀ i, z ∉ I i) : ∃ C' ⊆ J ∪ ⋃ i, I i, M.Circuit C' ∧ z ∈ C' := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z ∈ M.closure ((⋃ i, I i) ∪ (J \ {z})) by
    rw [mem_closure_iff_exists_circuit_of_not_mem (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', ?_, hC', hzC'⟩
    rwa [union_comm, ← insert_union, insert_diff_singleton, insert_eq_of_mem hzJ] at hC'ss
  replace hC := show ∀ (i : ι), M.closure (I i) = M.closure ({x i} ∪ (I i))
    by simpa [diff_singleton_eq_self (hxI _)] using fun i ↦ (hC i).closure_diff_singleton_eq (x i)
  -- This is true because each `I i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hC, iUnion_union_distrib,
    iUnion_singleton_eq_range, union_right_comm]
  refine mem_of_mem_of_subset (hJx.mem_closure_diff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_diff_distrib, union_comm]
  exact union_subset_union_left _ diff_subset

/-- A generalization of the strong circuit elimination axiom `Matroid.Circuit.strong_elimination`
to an infinite collection of circuits.
This version is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed. -/
lemma Circuit.strong_multi_elimination {C₀ : Set α} (C : ι → Set α) (hC₀ : M.Circuit C₀)
    (hC : ∀ i, M.Circuit (C i))(h_mem_C₀ : ∀ i, x i ∈ C₀) (h_mem : ∀ i, x i ∈ C i)
    (h_unique : ∀ ⦃i i'⦄, x i ∈ C i' → i = i') (hzC₀ : z ∈ C₀) (hzC : ∀ i, z ∉ C i) :
    ∃ C' ⊆ (C₀ ∪ ⋃ i, C i) \ range x, M.Circuit C' ∧ z ∈ C' := by
  have hwin := M.strong_multi_elimination_insert x (fun i ↦ (C i \ {x i}))
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

/-- The strong circuit elimination axiom. For any two circuits `C₁, C₂` and all `e ∈ C₁ ∩ C₂` and
`f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma Circuit.strong_elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (heC₁ : e ∈ C₁)
    (heC₂ : e ∈ C₂) (hfC₁ : f ∈ C₁) (hfC₂ : f ∉ C₂) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.Circuit C ∧ f ∈ C := by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit ↦ e) (fun _ ↦ C₂)
    (by simpa) (z := f) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (diff_subset_diff (by simp) (by simp)), hC, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when definining finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`. --/
lemma Circuit.elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.Circuit C := by
  obtain ⟨f, hf₁, hf₂⟩ : (C₁ \ C₂).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    exact fun hss ↦ h (hC₁.eq_of_subset_circuit hC₂ hss)
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subset_diff_singleton subset_union_right he₂, hC₂⟩
  exact ⟨C₁, subset_diff_singleton subset_union_left he₁, hC₁⟩

end Elimination

/-! ### Finitary Matroids -/

lemma Circuit.finite [Finitary M] (hC : M.Circuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push_neg at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

lemma finitary_iff_forall_circuit_finite : M.Finitary ↔ ∀ C, M.Circuit C → C.Finite := by
  refine ⟨fun _ _ ↦ Circuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_circuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

lemma exists_mem_finite_closure_of_mem_closure {Y : Set α} [M.Finitary] (he : e ∈ M.closure Y) :
    ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  by_cases heY : e ∈ Y
  · obtain ⟨J, hJ⟩ := M.exists_basis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_circuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.diff, hC.diff_singleton_indep heC,
    hC.mem_closure_diff_singleton_of_mem heC⟩

/-- In a finitary matroid, each finite set spanned by `X` is spanned by a finite independent
subset of `X`. -/
lemma exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite)
    (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by
  refine Set.Finite.induction_on_subset X hX ⟨∅, by simp⟩
    (@fun e Z heX hZX heZ ⟨J, hJY, hJfin, hJ, hJcl⟩ ↦ ?_)
  obtain ⟨K, hKY, hKfin, hK, heK⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  obtain ⟨I, hI⟩ := M.exists_basis (J ∪ K)
  refine ⟨I, hI.subset.trans (union_subset hJY hKY), (hJfin.union hKfin).subset hI.subset, hI.indep,
    (subset_trans (insert_subset ?_ ?_) hI.closure_eq_closure.symm.subset)⟩
  · exact mem_of_mem_of_subset heK (M.closure_subset_closure subset_union_right)
  exact hJcl.trans (M.closure_subset_closure subset_union_left)

end Matroid
