/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Module.Basic
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Further lemmas related to Archimedean classes for ordered module.

## Main definitions
* `ArchimedeanSubgroup.submodule`: `ArchimedeanSubgroup` as a submodule.
* `IsArchimedeanGrade`: a submodule `G` is called an Archimedean grade at
  `A : ArchimedeanClass M` iff $ Submodule[A, \top] = G \oplus Submodule(A, \top] $.
-/

variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable (K : Type*) [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

/-- For a ordered module over an `Archimedean` ring, `ArchimedeanSubgroup` is a submodule. -/
noncomputable
def ArchimedeanSubgroup.submodule (s : UpperSet (ArchimedeanClass M)) : Submodule K M where
  __ := ArchimedeanSubgroup s
  smul_mem' k {a} := by
    obtain rfl | hs := eq_or_ne s ⊤
    · suffices a = 0 → k • a = 0 by simpa using this
      intro ha
      simp [ha]
    · change a ∈ ArchimedeanSubgroup s → k • a ∈ ArchimedeanSubgroup s
      simp_rw [mem_iff_of_ne_top hs]
      intro ha
      by_cases htrivial : Nontrivial K
      · obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
        refine s.upper (ArchimedeanClass.mk_le_mk.mpr ⟨n, ?_⟩) ha
        have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
        rw [this, abs_smul]
        exact smul_le_smul_of_nonneg_right hn (by simp)
      · have : Subsingleton K := not_nontrivial_iff_subsingleton.mp htrivial
        rw [Subsingleton.eq_zero k]
        simpa using (IsUpperSet.top_mem s.upper).mpr <| UpperSet.coe_nonempty.mpr hs

theorem ArchimedeanSubgroup.mem_submodule_iff_of_ne_top {a : M} {s : UpperSet (ArchimedeanClass M)}
    (hs : s ≠ ⊤) : a ∈ ArchimedeanSubgroup.submodule K s ↔ ArchimedeanClass.mk a ∈ s :=
  mem_iff_of_ne_top hs

theorem ArchimedeanSubgroup.mem_submodule_Ioi_iff_of_ne_top {a : M} {A : ArchimedeanClass M}
    (hA : A ≠ ⊤) :
    a ∈ ArchimedeanSubgroup.submodule K (UpperSet.Ioi A) ↔ A < ArchimedeanClass.mk a :=
  mem_Ioi_iff_of_ne_top hA

@[simp]
theorem ArchimedeanSubgroup.mem_submodule_Ici_iff_of_ne_top {a : M} {A : ArchimedeanClass M}
    : a ∈ ArchimedeanSubgroup.submodule K (UpperSet.Ici A) ↔ A ≤ ArchimedeanClass.mk a :=
  mem_Ici_iff

variable (M) in
@[simp]
theorem ArchimedeanSubgroup.submodule_eq_bot :
    ArchimedeanSubgroup.submodule K (M := M) ⊤ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  change ∀ x ∈ ArchimedeanSubgroup ⊤, x = 0
  simp

variable (M) in
@[simp]
theorem ArchimedeanSubgroup.submodule_eq_bot_of_Ici_top :
    ArchimedeanSubgroup.submodule K (M := M) (UpperSet.Ici ⊤) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  change ∀ x ∈ ArchimedeanSubgroup (UpperSet.Ici ⊤), x = 0
  simp

variable (M) in
theorem ArchimedeanSubgroup.submodule_strictAntiOn :
    StrictAntiOn (ArchimedeanSubgroup.submodule (M := M) K) (Set.Iio ⊤) :=
  ArchimedeanSubgroup.strictAntiOn M

variable (M) in
theorem ArchimedeanSubgroup.submodule_antitone :
    Antitone (ArchimedeanSubgroup.submodule (M := M) K) :=
  ArchimedeanSubgroup.antitone M

/-- a submodule `G` is called an Archimedean grade at `A : ArchimedeanClass M`
iff $ Submodule[A, \top] = G \oplus Submodule(A, \top] $.

Such submodule is `Archimedean` itself (see `IsArchimedeanGrade.archimedean`),
and a family of such submodules is linearly independent (see `IsArchimedeanGrade.iSupIndep`).
-/
def IsArchimedeanGrade (A : ArchimedeanClass M) (G : Submodule K M) :=
  Disjoint (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) G ∧
    (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) ⊔ G =
    (ArchimedeanSubgroup.submodule K (UpperSet.Ici A))

namespace IsArchimedeanGrade
variable {A : ArchimedeanClass M} {G : Submodule K M}

theorem disjoint (hgrade : IsArchimedeanGrade K A G) :
    Disjoint (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) G := hgrade.1

theorem sup_eq (hgrade : IsArchimedeanGrade K A G) :
    (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) ⊔ G =
    (ArchimedeanSubgroup.submodule K (UpperSet.Ici A)) := hgrade.2

omit A in
theorem eq_bot_of_top (hgrade : IsArchimedeanGrade K (⊤ : ArchimedeanClass M) G) : G = ⊥ := by
  obtain hsup := hgrade.sup_eq
  simpa using hsup

theorem nontrivial_of_ne_top (hgrade : IsArchimedeanGrade K A G) (h : A ≠ ⊤) :
    Nontrivial G := by
  obtain hcodisj := hgrade.sup_eq
  contrapose! hcodisj with htrivial
  have hbot : G = ⊥ := by simpa using Submodule.nontrivial_iff_ne_bot.not.mp htrivial
  have hA : UpperSet.Ioi A ∈ Set.Iio ⊤ := by
    suffices UpperSet.Ioi A < ⊤ by simpa using this
    refine Ne.lt_top (UpperSet.ext_iff.ne.mpr ?_)
    simpa using h
  rw [hbot, sup_bot_eq]
  rw [((ArchimedeanSubgroup.submodule_strictAntiOn M K).eq_iff_eq hA (by simp)).ne]
  rw [UpperSet.ext_iff.ne]
  by_contra!
  have h' : A ∈ Set.Ici A := Set.left_mem_Ici
  simp [show Set.Ici A = Set.Ioi A by exact this] at h'

theorem le_Ici (hgrade : IsArchimedeanGrade K A G) :
    G ≤ (ArchimedeanSubgroup.submodule K (UpperSet.Ici A)) := by
  simp [← hgrade.sup_eq]

theorem archimedeanClass_eq_of_mem (hgrade : IsArchimedeanGrade K A G) {a : M}
    (ha : a ∈ G) (h0 : a ≠ 0) : ArchimedeanClass.mk a = A := by
  apply le_antisymm
  · have hA : (UpperSet.Ioi A) ≠ ⊤ := by
      contrapose! h0
      have : A = ⊤ := IsMax.eq_top (Set.Ioi_eq_empty_iff.mp (UpperSet.ext_iff.mp h0))
      rw [this] at hgrade
      rw [hgrade.eq_bot_of_top] at ha
      exact (Submodule.mem_bot _).mp ha
    contrapose! h0 with hlt
    have ha' : a ∈ ArchimedeanSubgroup.submodule K (UpperSet.Ioi A) :=
      (ArchimedeanSubgroup.mem_iff_of_ne_top hA).mpr hlt
    exact (Submodule.disjoint_def.mp hgrade.disjoint) a ha' ha
  · apply (ArchimedeanSubgroup.mem_iff_of_ne_top (show (UpperSet.Ici A) ≠ ⊤ by simp)).mp
    exact Set.mem_of_subset_of_mem hgrade.le_Ici ha

theorem archimedean (hgrade : IsArchimedeanGrade K A G) : Archimedean G := by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [hgrade.archimedeanClass_eq_of_mem K a.prop (by simpa using ha)]
  rw [hgrade.archimedeanClass_eq_of_mem K b.prop (by simpa using hb)]

end IsArchimedeanGrade

theorem IsArchimedeanGrade.iSupIndep {F : ArchimedeanClass M → Submodule K M}
    (hgrade : ∀ A : ArchimedeanClass M, IsArchimedeanGrade K A (F A)) : iSupIndep F := by
  rw [iSupIndep_def]
  intro A
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congrArg ArchimedeanClass.mk hf
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases hnonempty : f.support.Nonempty
  · have hmem (x : ArchimedeanClass M) : (f x).val ∈ F x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [(hgrade x).archimedeanClass_eq_of_mem K (hmem x) (by simpa using hx)]
      rw [(hgrade y).archimedeanClass_eq_of_mem K (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono]
    rw [(hgrade _).archimedeanClass_eq_of_mem K (hmem _)
      (by simpa using Finset.min'_mem f.support hnonempty)]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    rw [DFinsupp.notMem_support_iff, (hgrade _).archimedeanClass_eq_of_mem K ha h0]
    simpa using (f A).prop
  · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
    symm
    simpa using h0
