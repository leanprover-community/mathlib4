/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Module.Basic

/-!
# Archimedean classes for ordered module

## Main definitions
* `ArchimedeanClass.ball` are `ArchimedeanClass.ballAddSubgroup` as a submodules.
* `ArchimedeanClass.closedBall` are `ArchimedeanClass.closedBallAddSubgroup` as a submodules.
-/

@[expose] public section

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

namespace ArchimedeanClass

@[simp]
theorem mk_smul (a : M) {k : K} (h : k ≠ 0) : mk (k • a) = mk a := by
  have : Nontrivial K := nontrivial_iff.mpr ⟨k, 0, h⟩
  obtain ⟨m, hm⟩ := Archimedean.arch 1 (show 0 < |k| by simpa using h)
  obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp)
  simp_rw [mk_eq_mk, abs_smul]
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← smul_assoc]
    exact le_smul_of_one_le_left (by simp) hm
  · have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
    rw [this]
    exact smul_le_smul_of_nonneg_right hn (by simp)

theorem mk_le_mk_smul (a : M) (k : K) : mk a ≤ mk (k • a) := by
  obtain rfl | h := eq_or_ne k 0 <;> simp [*]

variable (K)

/-- Given an upper set `s` of archimedean classes in a linearly ordered module `M` with Archimedean
scalars, all elements belonging to these classes form a submodule, except when `s = ⊤` for which the
set would be empty. For `s = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.addSubgroup`'s. -/
noncomputable
def submodule (s : UpperSet (ArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
  smul_mem' k {a} := by
    obtain rfl | hs := eq_or_ne s ⊤
    · aesop
    simpa [mem_addSubgroup_iff hs] using s.upper (mk_le_mk_smul a k)

/-- An open ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.ballAddSubgroup`'s. -/
noncomputable
abbrev ball (c : ArchimedeanClass M) := submodule K (UpperSet.Ioi c)

/-- A closed ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ici c`.

This has the same carrier as `ArchimedeanClass.closedBallAddSubgroup`'s. -/
noncomputable
abbrev closedBall (c : ArchimedeanClass M) := submodule K (UpperSet.Ici c)

@[simp]
theorem toAddSubgroup_ball (c : ArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

@[simp]
theorem toAddSubgroup_closedBall (c : ArchimedeanClass M) :
    (closedBall K c).toAddSubgroup = closedBallAddSubgroup c := rfl

@[simp]
theorem mem_ball_iff {a : M} {c : ArchimedeanClass M} (hc : c ≠ ⊤) : a ∈ ball K c ↔ c < mk a :=
  mem_ballAddSubgroup_iff hc

@[simp]
theorem mem_closedBall_iff {a : M} {c : ArchimedeanClass M} : a ∈ closedBall K c ↔ c ≤ mk a :=
  mem_closedBallAddSubgroup_iff

variable (M) in
@[simp]
theorem ball_top : ball (M := M) K ⊤ = ⊥ :=
  (Submodule.toAddSubgroup_inj _ _).mp <| ballAddSubgroup_top M

variable (M) in
@[simp]
theorem closedBall_top : closedBall (M := M) K ⊤ = ⊥ :=
  (Submodule.toAddSubgroup_inj _ _).mp <| closedBallAddSubgroup_top M

theorem ball_antitone : Antitone (ball (M := M) K) := by
  intro _ _ h
  exact (Submodule.toAddSubgroup_le _ _).mp <| ballAddSubgroup_antitone h

theorem ball_le_closedBall {c : ArchimedeanClass M} : ball K c ≤ closedBall K c := by
  obtain rfl | hc := eq_or_ne c ⊤
  · simp
  intro a ha
  simpa using ((mem_ball_iff K hc).mp ha).le

end ArchimedeanClass

namespace FiniteArchimedeanClass

variable (K)

/-- Given an upper set `s` of finite archimedean classes in a linearly ordered module `M` with
Archimedean scalars, all elements belonging to these classes together with 0 form a submodule.

This has the same carrier as `FiniteArchimedeanClass.addSubgroup`. -/
noncomputable
def submodule (s : UpperSet (FiniteArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
  smul_mem' k {a} ha ne := s.upper (ArchimedeanClass.mk_le_mk_smul ..) <|
    ha fun eq ↦ ne <| by simp [ArchimedeanClass.mk_eq_top_iff.mp eq]

theorem submodule_strictAnti : StrictAnti (submodule K (M := M)) := addSubgroup_strictAnti

/-- An open ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.ballAddSubgroup`'s. -/
noncomputable
abbrev ball (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ioi c)

/-- A closed ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ici c`.

This has the same carrier as `ArchimedeanClass.closedBallAddSubgroup`'s. -/
noncomputable
abbrev closedBall (c : FiniteArchimedeanClass M) := submodule K (UpperSet.Ici c)

@[simp]
theorem toAddSubgroup_ball (c : FiniteArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

@[simp]
theorem toAddSubgroup_closedBall (c : FiniteArchimedeanClass M) :
    (closedBall K c).toAddSubgroup = closedBallAddSubgroup c := rfl

@[simp]
theorem mem_ball_iff {a : M} {c : FiniteArchimedeanClass M} :
    a ∈ ball K c ↔ ∀ h : a ≠ 0, c < mk a h :=
  mem_ballAddSubgroup_iff

@[simp]
theorem mem_closedBall_iff {a : M} {c : FiniteArchimedeanClass M} :
    a ∈ closedBall K c ↔ ∀ h : a ≠ 0, c ≤ mk a h :=
  mem_closedBallAddSubgroup_iff

theorem ball_strictAnti : StrictAnti (ball (M := M) K) := ballAddSubgroup_strictAnti

theorem ball_lt_closedBall {c : FiniteArchimedeanClass M} : ball K c < closedBall K c :=
  submodule_strictAnti _ Set.Ioi_ssubset_Ici_self

attribute [deprecated submodule (since := "2025-12-14")] ArchimedeanClass.submodule
attribute [deprecated ball (since := "2025-12-14")] ArchimedeanClass.ball
attribute [deprecated closedBall (since := "2025-12-14")] ArchimedeanClass.closedBall
attribute [deprecated toAddSubgroup_ball (since := "2025-12-14")]
  ArchimedeanClass.toAddSubgroup_ball
attribute [deprecated toAddSubgroup_closedBall (since := "2025-12-14")]
  ArchimedeanClass.toAddSubgroup_closedBall
attribute [deprecated mem_ball_iff (since := "2025-12-14")] ArchimedeanClass.mem_ball_iff
attribute [deprecated mem_closedBall_iff (since := "2025-12-14")]
  ArchimedeanClass.mem_closedBall_iff
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")] ArchimedeanClass.ball_top
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")]
  ArchimedeanClass.closedBall_top
attribute [deprecated ball_strictAnti (since := "2025-12-14")] ArchimedeanClass.ball_antitone
attribute [deprecated ball_lt_closedBall (since := "2025-12-14")]
  ArchimedeanClass.ball_le_closedBall

end FiniteArchimedeanClass
