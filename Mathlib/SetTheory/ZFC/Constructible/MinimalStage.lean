/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Equivalence

/-!
# Minimal constructible stages

Every constructible set has a least stage at which it occurs.  That stage is
never zero or a limit, hence is a successor.  Its predecessor is the canonical
stage over which the set receives a `DefZF` (equivalently, Gödel-operation)
representation.
-/

@[expose] public section

open Set

universe u

namespace Constructible

/-- The least constructible stage containing `x`. -/
noncomputable def firstStage (x : ZFSet.{u}) (_hx : x ∈ L) : Ordinal.{u} :=
  sInf {alpha : Ordinal.{u} | x ∈ LStageZF alpha}

/-- The set of stages containing a constructible set is nonempty. -/
theorem firstStage_indexSet_nonempty (x : ZFSet.{u}) (hx : x ∈ L) :
    ({alpha : Ordinal.{u} | x ∈ LStageZF alpha} : Set Ordinal).Nonempty := by
  rcases hx with ⟨alpha, hxa⟩
  exact ⟨alpha, hxa⟩

/-- A constructible set belongs to its least occurrence stage. -/
theorem mem_LStageZF_firstStage (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ LStageZF (firstStage x hx) := by
  exact csInf_mem (firstStage_indexSet_nonempty x hx)

/-- The least occurrence stage lies below every other occurrence stage. -/
theorem firstStage_le {x : ZFSet.{u}} (hx : x ∈ L)
    {alpha : Ordinal.{u}} (hxa : x ∈ LStageZF alpha) :
    firstStage x hx ≤ alpha := by
  exact csInf_le' hxa

/-- No strictly earlier stage contains `x`. -/
theorem not_mem_LStageZF_of_lt_firstStage {x : ZFSet.{u}} (hx : x ∈ L)
    {alpha : Ordinal.{u}} (halpha : alpha < firstStage x hx) :
    x ∉ LStageZF alpha := by
  intro hxa
  have hnot : alpha ∉
      ({beta : Ordinal.{u} | x ∈ LStageZF beta} : Set Ordinal.{u}) :=
    notMem_of_lt_csInf' halpha
  exact hnot hxa

/-- The first occurrence stage of a constructible set is nonzero. -/
theorem firstStage_ne_zero (x : ZFSet.{u}) (hx : x ∈ L) :
    firstStage x hx ≠ 0 := by
  intro hzero
  have hmem := mem_LStageZF_firstStage x hx
  rw [hzero, LStageZF_zero] at hmem
  exact ZFSet.notMem_empty x hmem

/-- The first occurrence stage cannot be a nonzero limit. -/
theorem not_isSuccLimit_firstStage (x : ZFSet.{u}) (hx : x ∈ L) :
    Not (Order.IsSuccLimit (firstStage x hx)) := by
  intro hlimit
  rcases (mem_LStageZF_limit_iff hlimit).mp
      (mem_LStageZF_firstStage x hx) with
    ⟨alpha, halpha, hxa⟩
  exact not_mem_LStageZF_of_lt_firstStage hx halpha hxa

/-- The least occurrence stage is a successor ordinal. -/
theorem exists_firstStage_eq_succ (x : ZFSet.{u}) (hx : x ∈ L) :
    exists alpha : Ordinal.{u}, firstStage x hx = Order.succ alpha := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit (firstStage x hx) with
    hzero | hsucc | hlimit
  · exact False.elim (firstStage_ne_zero x hx hzero)
  · rcases hsucc with ⟨alpha, halpha⟩
    exact ⟨alpha, halpha.symm⟩
  · exact False.elim (not_isSuccLimit_firstStage x hx hlimit)

/-- The predecessor of the first stage containing `x`. -/
noncomputable def birthStage (x : ZFSet.{u}) (hx : x ∈ L) : Ordinal.{u} :=
  Classical.choose (exists_firstStage_eq_succ x hx)

@[simp]
theorem firstStage_eq_succ_birthStage (x : ZFSet.{u}) (hx : x ∈ L) :
    firstStage x hx = Order.succ (birthStage x hx) :=
  Classical.choose_spec (exists_firstStage_eq_succ x hx)

/-- Every constructible set is definable over its canonical birth stage. -/
theorem mem_DefZF_birthStage (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∈ DefZF (LStageZF (birthStage x hx)) := by
  rw [← LStageZF_succ, ← firstStage_eq_succ_birthStage]
  exact mem_LStageZF_firstStage x hx

/-- A constructible set does not already belong to its birth stage. -/
theorem not_mem_LStageZF_birthStage (x : ZFSet.{u}) (hx : x ∈ L) :
    x ∉ LStageZF (birthStage x hx) := by
  apply not_mem_LStageZF_of_lt_firstStage hx
  rw [firstStage_eq_succ_birthStage]
  exact Order.lt_succ _

/-- Every member of `L_alpha` was born strictly before `alpha`. -/
theorem birthStage_lt_of_mem_LStageZF {x : ZFSet.{u}} {alpha : Ordinal.{u}}
    (hx : x ∈ LStageZF alpha) :
    birthStage x (LStageZF_subset_constructibleUniverse alpha hx) < alpha := by
  have hfirst := firstStage_le
    (LStageZF_subset_constructibleUniverse alpha hx) hx
  rw [firstStage_eq_succ_birthStage] at hfirst
  exact Order.succ_le_iff.mp hfirst

/-- The stage `L_alpha` first occurs as an element at stage `alpha + 1`. -/
theorem firstStage_LStageZF (alpha : Ordinal.{u}) :
    firstStage (LStageZF alpha) (LStageZF_mem_L alpha) = Order.succ alpha := by
  apply le_antisymm
  · apply firstStage_le (LStageZF_mem_L alpha)
    exact LStageZF_mem_succ alpha
  · apply Order.succ_le_of_lt
    by_contra hnot
    have hle : firstStage (LStageZF alpha) (LStageZF_mem_L alpha) ≤ alpha :=
      le_of_not_gt hnot
    have hself : LStageZF alpha ∈ LStageZF alpha :=
      LStageZF_mono hle
        (mem_LStageZF_firstStage (LStageZF alpha) (LStageZF_mem_L alpha))
    exact ZFSet.mem_irrefl _ hself

@[simp]
theorem birthStage_LStageZF (alpha : Ordinal.{u}) :
    birthStage (LStageZF alpha) (LStageZF_mem_L alpha) = alpha := by
  apply Order.succ_injective
  calc
    Order.succ (birthStage (LStageZF alpha) (LStageZF_mem_L alpha)) =
        firstStage (LStageZF alpha) (LStageZF_mem_L alpha) :=
      (firstStage_eq_succ_birthStage
        (LStageZF alpha) (LStageZF_mem_L alpha)).symm
    _ = Order.succ alpha := firstStage_LStageZF alpha

/-- The birth stage is independent of the proof of constructibility. -/
theorem birthStage_proof_irrel (x : ZFSet.{u}) (hx hy : x ∈ L) :
    birthStage x hx = birthStage x hy := by
  apply Order.succ_injective
  calc
    Order.succ (birthStage x hx) = firstStage x hx :=
      (firstStage_eq_succ_birthStage x hx).symm
    _ = firstStage x hy := by rfl
    _ = Order.succ (birthStage x hy) :=
      firstStage_eq_succ_birthStage x hy

end Constructible
