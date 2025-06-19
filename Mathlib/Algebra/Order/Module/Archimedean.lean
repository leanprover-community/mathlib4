/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.Module.Basic

/-!
# Further lemmas related to Archimedean classes for ordered module.

## Main definitions
* `ArchimedeanClass.ball` are `ArchimedeanClass.ballAddSubgroup` as a submodules.
* `ArchimedeanClass.closedBall` are `ArchimedeanClass.closedBallAddSubgroup` as a submodules.
-/

namespace ArchimedeanClass

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable (K : Type*) [Ring K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

variable {K} in
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

variable {K} in
theorem mk_le_mk_smul (a : M) (k : K) : mk a ≤ mk (k • a) := by
  obtain rfl | h := eq_or_ne k 0
  · simp
  · rw [mk_smul a h]

/-- Given a `s : UpperSet` of `ArchimedeanClass M` for a linearly ordered module `M` with
Archimedean scaler, all elements belong to these classes form a submodule, with the exception for
`s = ⊤` where the set would be empty. For `s = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.addSubgroup`'s. -/
noncomputable
def submodule (s : UpperSet (ArchimedeanClass M)) : Submodule K M where
  __ := addSubgroup s
  smul_mem' k {a} := by
    obtain rfl | hs := eq_or_ne s ⊤
    · aesop
    change a ∈ addSubgroup s → k • a ∈ addSubgroup s
    simp_rw [mem_addSubgroup_iff hs]
    refine fun h ↦ s.upper ?_ h
    apply mk_le_mk_smul

/-- An open ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ioi c`.
For `c = ⊤`, we assign the junk value `⊥`.

This has the same carrier as `ArchimedeanClass.ballAddSubgroup`'s. -/
noncomputable
abbrev ball (c : ArchimedeanClass M) := submodule K (UpperSet.Ioi c)

/-- A closed ball defined by `ArchimedeanClass.submodule` of `UpperSet.Ici c`.

This has the same carrier as `ArchimedeanClass.closedBallAddSubgroup`'s. -/
noncomputable
abbrev closedBall (c : ArchimedeanClass M) := submodule K (UpperSet.Ici c)

theorem toAddSubgroup_ball (c : ArchimedeanClass M) :
    (ball K c).toAddSubgroup = ballAddSubgroup c := rfl

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

end ArchimedeanClass
