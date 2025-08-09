/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Further lemmas related to Archimedean classes for ordered module.

## Main definitions
* `ArchimedeanClass.ball` and `ArchimedeanClass.closedBall`:
  `ArchimedeanClass.ballAddSubgroup` and `ArchimedeanClass.closedBallAddSubgroup` as submodules.
* `ArchimedeanClass.IsGrade`: The module version of `ArchimedeanClass.IsGradeAddSubgroup`.
-/

namespace ArchimedeanClass

variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

variable (K) in
/-- For a ordered module over an `Archimedean` ring,
`ArchimedeanClass.addSubgroup` is a submodule. -/
noncomputable
def submodule (s : UpperSet (ArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
  smul_mem' k {a} := by
    obtain rfl | hs := eq_or_ne s ⊤
    · aesop
    change a ∈ addSubgroup s → k • a ∈ addSubgroup s
    simp_rw [mem_addSubgroup_iff hs]
    intro ha
    obtain _ | _ := subsingleton_or_nontrivial K
    · rw [Subsingleton.eq_zero k]
      simpa using (IsUpperSet.top_mem s.upper).mpr <| UpperSet.coe_nonempty.mpr hs
    obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
    refine s.upper (mk_le_mk.mpr ⟨n, ?_⟩) ha
    have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this, abs_smul]
    exact smul_le_smul_of_nonneg_right hn (by simp)

variable (K) in
/-- `ArchimedeanClass.ballAddSubgroup` as a submodule. -/
noncomputable
abbrev ball (A : ArchimedeanClass M) := submodule K (UpperSet.Ioi A)

variable (K) in
/-- `ArchimedeanClass.closedBallAddSubgroup` as a submodule. -/
noncomputable
abbrev closedBall (A : ArchimedeanClass M) := submodule K (UpperSet.Ici A)

variable (K) in
theorem toAddSubgroup_ball (A : ArchimedeanClass M) :
    (ball K A).toAddSubgroup = ballAddSubgroup A := rfl

variable (K) in
theorem toAddSubgroup_closedBall (A : ArchimedeanClass M) :
    (closedBall K A).toAddSubgroup = closedBallAddSubgroup A := rfl

variable (K) in
theorem mem_ball_iff {a : M} {A : ArchimedeanClass M} (hA : A ≠ ⊤) : a ∈ ball K A ↔ A < mk a :=
  mem_ballAddSubgroup_iff hA

variable (K) in
@[simp]
theorem mem_closedBall_iff {a : M} {A : ArchimedeanClass M} : a ∈ closedBall K A ↔ A ≤ mk a :=
  mem_closedBallAddSubgroup_iff

variable (M K) in
@[simp]
theorem ball_top : ball (M := M) K ⊤ = ⊥ :=
  (Submodule.toAddSubgroup_inj _ _).mp <| ballAddSubgroup_top M

variable (M K) in
@[simp]
theorem closedBall_top : closedBall (M := M) K ⊤ = ⊥ :=
  (Submodule.toAddSubgroup_inj _ _).mp <| closedBallAddSubgroup_top M

variable (M K) in
theorem ball_antitone : Antitone (ball (M := M) K) := by
  intro A B h
  exact (Submodule.toAddSubgroup_le _ _).mp <| ballAddSubgroup_antitone M h

/-- The module version of `ArchimedeanClass.IsGradeAddSubgroup`. -/
def IsGrade (A : ArchimedeanClass M) (G : Submodule K M) :=
  Disjoint (ball K A) G ∧ ball K A ⊔ G = closedBall K A

namespace IsGrade
variable {A : ArchimedeanClass M} {G : Submodule K M}

theorem disjoint (hgrade : IsGrade A G) : Disjoint (ball K A) G := hgrade.1

theorem sup_eq (hgrade : IsGrade A G) : ball K A ⊔ G = closedBall K A := hgrade.2

theorem isGradeAddSubgroup (hgrade : IsGrade A G) : IsGradeAddSubgroup A G.toAddSubgroup := by
  constructor
  · simpa [disjoint_iff, ← SetLike.coe_set_eq] using hgrade.disjoint
  · rw [← toAddSubgroup_ball K A, ← toAddSubgroup_closedBall K A]
    rw [← Submodule.sup_toAddSubgroup, hgrade.sup_eq]

theorem nontrivial (hgrade : IsGrade A G) (h : A ≠ ⊤) : Nontrivial G :=
  hgrade.isGradeAddSubgroup.nontrivial h

theorem archimedeanClass_eq (hgrade : IsGrade A G) {a : M} (ha : a ∈ G) (h0 : a ≠ 0) : mk a = A :=
  hgrade.isGradeAddSubgroup.archimedeanClass_eq ha h0

theorem archimedean (hgrade : IsGrade A G) : Archimedean G :=
  hgrade.isGradeAddSubgroup.archimedean

end IsGrade

theorem iSupIndep_of_isGrade {F : ArchimedeanClass M → Submodule K M}
    (hgrade : ∀ A : ArchimedeanClass M, IsGrade A (F A)) : iSupIndep F := by
  rw [iSupIndep_def]
  intro A
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congrArg mk hf
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases hnonempty : f.support.Nonempty
  · have hmem (x : ArchimedeanClass M) : (f x).val ∈ F x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ mk (f i).val) f.support := by
      intro x hx y hy hxy
      change mk (f x).val < mk (f y).val
      rw [(hgrade x).archimedeanClass_eq (hmem x) (by simpa using hx)]
      rw [(hgrade y).archimedeanClass_eq (hmem y) (by simpa using hy)]
      exact hxy
    rw [mk_sum hnonempty hmono]
    rw [(hgrade _).archimedeanClass_eq (hmem _)
      (by simpa using Finset.min'_mem f.support hnonempty)]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    rw [DFinsupp.notMem_support_iff, (hgrade _).archimedeanClass_eq ha h0]
    simpa using (f A).prop
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    symm
    simpa using h0

end ArchimedeanClass
