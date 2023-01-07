/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann

! This file was ported from Lean 3 source module data.rat.floor
! leanprover-community/mathlib commit 134625f523e737f650a6ea7f0c82a6177e45e622
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Tactic.FieldSimp

/-!
# Floor Function for Rational Numbers

## Summary

We define the `floor` function and the `floor_ring` instance on `ℚ`. Some technical lemmas relating
`floor` to integer division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/


open Int

namespace Rat

variable {α : Type _} [LinearOrderedField α] [FloorRing α]

#print Rat.floor /-
/-- `floor q` is the largest integer `z` such that `z ≤ q` -/
protected def floor : ℚ → ℤ
  | ⟨n, d, h, c⟩ => n / d
#align rat.floor Rat.floor
-/

protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ Rat.floor r ↔ (z : ℚ) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp [Rat.floor]
    rw [num_denom']
    have h' := Int.ofNat_lt.2 h
    conv =>
      rhs
      rw [coe_int_eq_mk, Rat.le_def zero_lt_one h', mul_one]
    exact Int.le_ediv_iff_mul_le h'
#align rat.le_floor Rat.le_floor

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun a z => Rat.le_floor.symm

protected theorem floor_def {q : ℚ} : ⌊q⌋ = q.num / q.denom :=
  by
  cases q
  rfl
#align rat.floor_def Rat.floor_def

theorem floor_int_div_nat_eq_div {n : ℤ} {d : ℕ} : ⌊(↑n : ℚ) / (↑d : ℚ)⌋ = n / (↑d : ℤ) :=
  by
  rw [Rat.floor_def]
  obtain rfl | hd := @eq_zero_or_pos _ _ d
  · simp
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.denom :=
    by
    rw [q_eq]
    exact_mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (by exact_mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine' (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left _ <| Int.coe_nat_nonneg q.denom).symm
  rwa [← d_eq_c_mul_denom, Int.coe_nat_pos]
#align rat.floor_int_div_nat_eq_div Rat.floor_int_div_nat_eq_div

@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (by exact_mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))
#align rat.floor_cast Rat.floor_cast

@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]
#align rat.ceil_cast Rat.ceil_cast

@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x :=
  by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]
#align rat.round_cast Rat.round_cast

@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract x := by
  simp only [fract, cast_sub, cast_coe_int, floor_cast]
#align rat.cast_fract Rat.cast_fract

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [eq_sub_of_add_eq <| Int.mod_add_div n d, Rat.floor_int_div_nat_eq_div]
#align int.mod_nat_eq_sub_mul_floor_rat_div Int.mod_nat_eq_sub_mul_floor_rat_div

theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.Coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.Coprime d :=
  by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this
#align nat.coprime_sub_mul_floor_rat_div_of_coprime Nat.coprime_sub_mul_floor_rat_div_of_coprime

namespace Rat

theorem num_lt_succ_floor_mul_denom (q : ℚ) : q.num < (⌊q⌋ + 1) * q.denom :=
  by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.denom by exact_mod_cast this
  suffices (q.num : ℚ) < (q - fract q + 1) * q.denom
    by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.denom
    by
    have : (q - fract q + 1) * q.denom = q.num + (1 - fract q) * q.denom
    calc
      (q - fract q + 1) * q.denom = (q + (1 - fract q)) * q.denom := by ring
      _ = q * q.denom + (1 - fract q) * q.denom := by rw [add_mul]
      _ = q.num + (1 - fract q) * q.denom := by simp

    rwa [this]
  suffices 0 < (1 - fract q) * q.denom
    by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact_mod_cast q.pos)
#align rat.num_lt_succ_floor_mul_denom Rat.num_lt_succ_floor_mul_denom

theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num :=
  by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := rat.num_pos_iff_pos.elim_right q_pos
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.nat_abs : ℤ) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  set q_inv := (q.denom : ℚ) / q.num with q_inv_def
  have q_inv_eq : q⁻¹ = q_inv := Rat.inv_def''
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  suffices ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num by
    field_simp [this, ne_of_gt q_num_pos]
  suffices (q.denom : ℤ) - q.num * ⌊q_inv⌋ < q.num
    by
    -- use that `q.num` and `q.denom` are coprime to show that the numerator stays unreduced
    have : ((q.denom - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.denom - q.num * ⌊q_inv⌋ :=
      by
      suffices ((q.denom : ℤ) - q.num * ⌊q_inv⌋).natAbs.Coprime q.num.nat_abs by
        exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have : (q.num.nat_abs : ℚ) = (q.num : ℚ) := by exact_mod_cast q_num_abs_eq_q_num
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.cop.symm
      simpa only [this, q_num_abs_eq_q_num] using tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.denom < q⁻¹.denom :=
    by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.denom := Rat.num_lt_succ_floor_mul_denom q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.denom + q⁻¹.denom := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.denom` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.denom ∧ q_inv.denom = q.num.nat_abs :=
    by
    have coprime_q_denom_q_num : q.denom.coprime q.num.nat_abs := q.cop.symm
    have : Int.natAbs q.denom = q.denom := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.denom : ℚ) / q.num).denom : ℤ) = q.num.nat_abs by exact_mod_cast this
      rw [q_num_abs_eq_q_num]
      exact_mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq
#align rat.fract_inv_num_lt_num_of_pos Rat.fract_inv_num_lt_num_of_pos

end Rat
