import Mathlib.Data.Rat.Order
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Rewrites
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Sqrt
import Mathlib.Util.Qq

namespace Mathlib.Tactic.ByApprox

open Lean hiding Rat
open Qq Meta

-- TODO there is no way that this is the cleanest proof of this result
lemma rat_lt_of_int_lt (na nb : ℤ) (da db : ℕ) (ha : 0 < da) (hb : 0 < db) (h : na * db < nb * da) :
    (na : ℚ) / da < nb / db := by
  replace h := Int.cast_mono (α := ℚ) h
  simp at h
  replace h : (na : ℚ) * ↑db < ↑nb * ↑da := lt_of_lt_of_le (by simp) h
  replace ha : 0 < (da : ℚ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr ha)
  replace hb : 0 < (db : ℚ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hb)
  rw [Rat.div_def, Rat.div_def]
  have h3 := (mul_lt_mul_right hb).mpr $ (mul_lt_mul_right ha).mpr h
  simp at h3
  rw [mul_assoc _ (db : ℚ), mul_assoc, mul_comm (db : ℚ), mul_assoc] at h3
  rw [mul_inv_cancel, mul_one] at h3
  rw [mul_assoc _ (da : ℚ), mul_inv_cancel, mul_one] at h3
  exact h3
  . intro az
    rw [az] at ha
    simp at ha
  . intro bz
    rw [bz] at hb
    simp at hb

lemma le_of_int_le {α : Type} [LinearOrderedField α] (na nb : ℤ) (da db : ℕ) (ha : 0 < da)
    (hb : 0 < db) (h : na * db ≤ nb * da) : (na : α) / da ≤ nb / db := by
  replace h := Int.cast_mono (α := α) h
  simp at h
  replace h : (na : α) * ↑db ≤ ↑nb * ↑da := le_trans (by simp) h
  replace ha : 0 < (da : α)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr ha)
  replace hb : 0 < (db : α)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hb)
  have h3 := (mul_le_mul_right hb).mpr $ (mul_le_mul_right ha).mpr h
  simp at h3
  rw [mul_assoc _ (db : α), mul_assoc, mul_comm (db : α), mul_assoc] at h3
  rw [mul_inv_cancel, mul_one] at h3
  rw [mul_assoc _ (da : α), mul_inv_cancel, mul_one] at h3
  rwa [division_def, division_def]
  . intro az
    rw [az] at ha
    simp at ha
  . intro bz
    rw [bz] at hb
    simp at hb
