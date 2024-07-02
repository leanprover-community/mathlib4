/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Logic.UnivLE
import Mathlib.SetTheory.Ordinal.Basic

/-!
# UnivLE and cardinals
-/

noncomputable section

universe u v

open Cardinal

theorem univLE_iff_cardinal_le : UnivLE.{u, v} ↔ univ.{u, v+1} ≤ univ.{v, u+1} := by
  rw [← not_iff_not, UnivLE]; simp_rw [small_iff_lift_mk_lt_univ]; push_neg
  -- strange: simp_rw [univ_umax.{v,u}] doesn't work
  refine ⟨fun ⟨α, le⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [univ_umax.{v,u}, ← lift_le.{u+1}, lift_univ, lift_lift] at le
    exact le.trans_lt (lift_lt_univ'.{u,v+1} #α)
  · obtain ⟨⟨α⟩, h⟩ := lt_univ'.mp h; use α
    rw [univ_umax.{v,u}, ← lift_le.{u+1}, lift_univ, lift_lift]
    exact h.le

/-- Together with transitivity, this shows UnivLE "IsTotalPreorder". -/
theorem univLE_total : UnivLE.{u, v} ∨ UnivLE.{v, u} := by
  simp_rw [univLE_iff_cardinal_le]; apply le_total
