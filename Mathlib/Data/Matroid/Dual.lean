/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import Mathlib.Data.Matroid.IndepAxioms

/-!
# Matroid Duality

For a matroid `M` on ground set `E`, the collection of complements of the bases of `M` is the
collection of bases of another matroid on `E` called the 'dual' of `M`.
The map from `M` to its dual is an involution, interacts nicely with minors,
and preserves many important matroid properties such as representability and connectivity.

This file defines the dual matroid `M✶` of `M`, and gives associated API. The definition
is in terms of its independent sets, using `IndepMatroid.matroid`.

We also define 'Co-independence' (independence in the dual) of a set as a predicate `M.Coindep X`.
This is an abbreviation for `M✶.Indep X`, but has its own name for the sake of dot notation.

## Main Definitions

* `M.Dual`, written `M✶`, is the matroid on `M.E` which a set `B ⊆ M.E` is a base if and only if
  `M.E \ B` is a base for `M`.

* `M.Coindep X` means `M✶.Indep X`, or equivalently that `X` is contained in `M.E \ B` for some
  base `B` of `M`.
-/

assert_not_exists Field

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {I B X : Set α}

section dual

/-- Given `M : Matroid α`, the `IndepMatroid α` whose independent sets are
  the subsets of `M.E` that are disjoint from some base of `M` -/
@[simps] def dualIndepMatroid (M : Matroid α) : IndepMatroid α where
  E := M.E
  Indep I := I ⊆ M.E ∧ ∃ B, M.IsBase B ∧ Disjoint I B
  indep_empty := ⟨empty_subset M.E, M.exists_isBase.imp (fun _ hB ↦ ⟨hB, empty_disjoint _⟩)⟩
  indep_subset := by
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩
  indep_aug := by
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    have hXE := hX_max.1.1
    have hB' := (isBase_compl_iff_maximal_disjoint_isBase hXE).mpr hX_max
    set B' := M.E \ X with hX
    have hI := (not_iff_not.mpr (isBase_compl_iff_maximal_disjoint_isBase)).mpr hI_not_max
    obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_isBase_subset_union_isBase hB
    rw [← compl_subset_compl, ← hIB.sdiff_eq_right, ← union_diff_distrib, diff_eq, compl_inter,
      compl_compl, union_subset_iff, compl_subset_compl] at hB''₂
    have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne
      (by { rintro rfl; apply hI; convert hB''; simp [hB''.subset_ground] })
    obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu
    use e
    simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
    refine ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨?_, heI⟩)), ⟨B'', hB'', ?_⟩⟩
    · rw [hX]; exact ⟨heE, heX⟩
    rw [← union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB'']
    exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left
  indep_maximal := by
    rintro X - I' ⟨hI'E, B, hB, hI'B⟩ hI'X
    obtain ⟨I, hI⟩ := M.exists_isBasis (M.E \ X)
    obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_isBase_subset_union_isBase hB
    obtain rfl : I = B' \ X := hI.eq_of_subset_indep (hB'.indep.diff _)
      (subset_diff.2 ⟨hIB', (subset_diff.1 hI.subset).2⟩)
      (diff_subset_diff_left hB'.subset_ground)
    simp_rw [maximal_subset_iff']
    refine ⟨(X \ B') ∩ M.E, ?_, ⟨⟨inter_subset_right, ?_⟩, ?_⟩, ?_⟩
    · rw [subset_inter_iff, and_iff_left hI'E, subset_diff, and_iff_right hI'X]
      exact Disjoint.mono_right hB'IB <| disjoint_union_right.2
        ⟨disjoint_sdiff_right.mono_left hI'X  , hI'B⟩
    · exact ⟨B', hB', (disjoint_sdiff_left (t := X)).mono_left inter_subset_left⟩
    · exact inter_subset_left.trans diff_subset
    simp only [subset_inter_iff, subset_diff, and_imp, forall_exists_index]
    refine fun J hJE B'' hB'' hdj hJX hXJ ↦ ⟨⟨hJX, ?_⟩, hJE⟩
    have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B' := by
      rw [union_subset_iff, and_iff_left diff_subset, ← union_diff_cancel hJX,
        inter_union_distrib_left, hdj.symm.inter_eq, empty_union, diff_eq, ← inter_assoc,
        ← diff_eq, diff_subset_comm, diff_eq, inter_assoc, ← diff_eq, inter_comm]
      exact subset_trans (inter_subset_inter_right _ hB''.subset_ground) hXJ
    obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_isBase_subset_union_isBase hB''
    rw [union_comm, ← union_assoc, union_eq_self_of_subset_right inter_subset_left] at hB₁I
    obtain rfl : B₁ = B' := by
      refine hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ ?_)
      refine (hB₁I he).elim (fun heB'' ↦ ?_) (fun h ↦ h.1)
      refine (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' ?_)
      refine hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ ?_
      exact hB₁.indep.subset (insert_subset he (subset_union_right.trans hI'B₁))
    by_contra hdj'
    obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hdj'
    obtain (heB'' | ⟨-,heX⟩ ) := hB₁I heB'
    · exact hdj.ne_of_mem heJ heB'' rfl
    exact heX (hJX heJ)
  subset_ground := by tauto

/-- The dual of a matroid; the bases are the complements (w.r.t `M.E`) of the bases of `M`. -/
def dual (M : Matroid α) : Matroid α := M.dualIndepMatroid.matroid

/-- The `✶` symbol, which denotes matroid duality.
  (This is distinct from the usual `*` symbol for multiplication, due to precedence issues.) -/
postfix:max "✶" => Matroid.dual

theorem dual_indep_iff_exists' : (M✶.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.IsBase B ∧ Disjoint I B) :=
  Iff.rfl

@[simp] theorem dual_ground : M✶.E = M.E := rfl

theorem dual_indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) :
    M✶.Indep I ↔ (∃ B, M.IsBase B ∧ Disjoint I B) := by
  rw [dual_indep_iff_exists', and_iff_right hI]

theorem dual_dep_iff_forall : (M✶.Dep I) ↔ (∀ B, M.IsBase B → (I ∩ B).Nonempty) ∧ I ⊆ M.E := by
  simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and,
    not_exists, not_and, not_disjoint_iff_nonempty_inter, Classical.imp_iff_right_iff,
    iff_true_intro Or.inl]

instance dual_finite [M.Finite] : M✶.Finite :=
  ⟨M.ground_finite⟩

instance dual_nonempty [M.Nonempty] : M✶.Nonempty :=
  ⟨M.ground_nonempty⟩

@[simp] theorem dual_isBase_iff (hB : B ⊆ M.E := by aesop_mat) :
    M✶.IsBase B ↔ M.IsBase (M.E \ B) := by
  rw [isBase_compl_iff_maximal_disjoint_isBase, isBase_iff_maximal_indep, maximal_subset_iff,
    maximal_subset_iff]
  simp [dual_indep_iff_exists', hB]

theorem dual_isBase_iff' : M✶.IsBase B ↔ M.IsBase (M.E \ B) ∧ B ⊆ M.E :=
  (em (B ⊆ M.E)).elim (fun h ↦ by rw [dual_isBase_iff, and_iff_left h])
    (fun h ↦ iff_of_false (h ∘ (fun h' ↦ h'.subset_ground)) (h ∘ And.right))

theorem setOf_dual_isBase_eq : {B | M✶.IsBase B} = (fun X ↦ M.E \ X) '' {B | M.IsBase B} := by
  ext B
  simp only [mem_setOf_eq, mem_image, dual_isBase_iff']
  refine ⟨fun h ↦ ⟨_, h.1, diff_diff_cancel_left h.2⟩,
    fun ⟨B', hB', h⟩ ↦ ⟨?_,h.symm.trans_subset diff_subset⟩⟩
  rwa [← h, diff_diff_cancel_left hB'.subset_ground]

@[simp] theorem dual_dual (M : Matroid α) : M✶✶ = M :=
  ext_isBase rfl (fun B (h : B ⊆ M.E) ↦
    by rw [dual_isBase_iff, dual_isBase_iff, dual_ground, diff_diff_cancel_left h])

theorem dual_involutive : Function.Involutive (dual : Matroid α → Matroid α) := dual_dual

theorem dual_injective : Function.Injective (dual : Matroid α → Matroid α) :=
  dual_involutive.injective

@[simp] theorem dual_inj {M₁ M₂ : Matroid α} : M₁✶ = M₂✶ ↔ M₁ = M₂ :=
  dual_injective.eq_iff

theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₂ = M₁✶ := by
  rw [← dual_inj, dual_dual, eq_comm]

theorem eq_dual_iff_dual_eq {M₁ M₂ : Matroid α} : M₁ = M₂✶ ↔ M₁✶ = M₂ :=
  dual_involutive.eq_iff.symm

theorem IsBase.compl_isBase_of_dual (h : M✶.IsBase B) : M.IsBase (M.E \ B) :=
  (dual_isBase_iff'.1 h).1

theorem IsBase.compl_isBase_dual (h : M.IsBase B) : M✶.IsBase (M.E \ B) := by
  rwa [dual_isBase_iff, diff_diff_cancel_left h.subset_ground]

theorem IsBase.compl_inter_isBasis_of_inter_isBasis (hB : M.IsBase B) (hBX : M.IsBasis (B ∩ X) X) :
    M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine Indep.isBasis_of_forall_insert ?_ inter_subset_right (fun e he ↦ ?_)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left inter_subset_left disjoint_sdiff_left⟩
  simp only [diff_inter_self_eq_diff, mem_diff, not_and, not_not, imp_iff_right he.1.1] at he
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1,
    and_iff_left (inter_subset_left.trans diff_subset)]
  refine fun B' hB' ↦ by_contra (fun hem ↦ ?_)
  rw [nonempty_iff_ne_empty, not_ne_iff, ← union_singleton, diff_inter_diff,
    union_inter_distrib_right, union_empty_iff, singleton_inter_eq_empty, diff_eq,
    inter_right_comm, inter_eq_self_of_subset_right hB'.subset_ground, ← diff_eq,
    diff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩
  have hi : M.Indep (insert f (B ∩ X)) := by
    refine hBf.indep.subset (insert_subset_insert ?_)
    simp_rw [subset_diff, and_iff_right inter_subset_left, disjoint_singleton_right,
      mem_inter_iff, iff_false_intro he.1.2, and_false, not_false_iff]
  exact hfb.2 (hBX.mem_of_insert_indep (Or.elim (hem.1 hfb.1) (False.elim ∘ hfb.2) id) hi).1

theorem IsBase.inter_isBasis_iff_compl_inter_isBasis_dual (hB : M.IsBase B)
    (hX : X ⊆ M.E := by aesop_mat) :
    M.IsBasis (B ∩ X) X ↔ M✶.IsBasis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine ⟨hB.compl_inter_isBasis_of_inter_isBasis, fun h ↦ ?_⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_isBase_dual.compl_inter_isBasis_of_inter_isBasis h

theorem base_iff_dual_isBase_compl (hB : B ⊆ M.E := by aesop_mat) :
    M.IsBase B ↔ M✶.IsBase (M.E \ B) := by
  rw [dual_isBase_iff, diff_diff_cancel_left hB]

theorem ground_not_isBase (M : Matroid α) [h : RankPos M✶] : ¬M.IsBase M.E := by
  rwa [rankPos_iff, dual_isBase_iff, diff_empty] at h

theorem IsBase.ssubset_ground [h : RankPos M✶] (hB : M.IsBase B) : B ⊂ M.E :=
  hB.subset_ground.ssubset_of_ne (by rintro rfl; exact M.ground_not_isBase hB)

theorem Indep.ssubset_ground [h : RankPos M✶] (hI : M.Indep I) : I ⊂ M.E := by
  obtain ⟨B, hB⟩ := hI.exists_isBase_superset; exact hB.2.trans_ssubset hB.1.ssubset_ground

/-- A coindependent set of `M` is an independent set of the dual of `M✶`. we give it a separate
  definition to enable dot notation. Which spelling is better depends on context. -/
abbrev Coindep (M : Matroid α) (I : Set α) : Prop := M✶.Indep I

theorem coindep_def : M.Coindep X ↔ M✶.Indep X := Iff.rfl

theorem Coindep.indep (hX : M.Coindep X) : M✶.Indep X :=
  hX

@[simp] theorem dual_coindep_iff : M✶.Coindep X ↔ M.Indep X := by
  rw [Coindep, dual_dual]

theorem Indep.coindep (hI : M.Indep I) : M✶.Coindep I :=
  dual_coindep_iff.2 hI

theorem coindep_iff_exists' : M.Coindep X ↔ (∃ B, M.IsBase B ∧ B ⊆ M.E \ X) ∧ X ⊆ M.E := by
  simp_rw [Coindep, dual_indep_iff_exists', and_comm (a := _ ⊆ _), and_congr_left_iff, subset_diff]
  exact fun _ ↦ ⟨fun ⟨B, hB, hXB⟩ ↦ ⟨B, hB, hB.subset_ground, hXB.symm⟩,
    fun ⟨B, hB, _, hBX⟩ ↦ ⟨B, hB, hBX.symm⟩⟩

theorem coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ ∃ B, M.IsBase B ∧ B ⊆ M.E \ X := by
  rw [coindep_iff_exists', and_iff_left hX]

theorem coindep_iff_subset_compl_isBase : M.Coindep X ↔ ∃ B, M.IsBase B ∧ X ⊆ M.E \ B := by
  simp_rw [coindep_iff_exists', subset_diff]
  exact ⟨fun ⟨⟨B, hB, _, hBX⟩, hX⟩ ↦ ⟨B, hB, hX, hBX.symm⟩,
    fun ⟨B, hB, hXE, hXB⟩ ↦ ⟨⟨B, hB, hB.subset_ground, hXB.symm⟩, hXE⟩⟩

@[aesop unsafe 10% (rule_sets := [Matroid])]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.indep.subset_ground

theorem Coindep.exists_isBase_subset_compl (h : M.Coindep X) : ∃ B, M.IsBase B ∧ B ⊆ M.E \ X :=
  (coindep_iff_exists h.subset_ground).1 h

theorem Coindep.exists_subset_compl_isBase (h : M.Coindep X) : ∃ B, M.IsBase B ∧ X ⊆ M.E \ B :=
  coindep_iff_subset_compl_isBase.1 h

end dual

end Matroid
