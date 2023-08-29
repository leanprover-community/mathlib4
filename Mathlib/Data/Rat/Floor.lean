/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Data.Rat.Cast
import Mathlib.Tactic.FieldSimp

#align_import data.rat.floor from "leanprover-community/mathlib"@"e1bccd6e40ae78370f01659715d3c948716e3b7e"

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/


open Int

namespace Rat

variable {α : Type*} [LinearOrderedField α] [FloorRing α]

protected theorem floor_def' (a : ℚ) : a.floor = a.num / a.den := by
  rw [Rat.floor]
  -- ⊢ (if a.den = 1 then a.num else a.num / ↑a.den) = a.num / ↑a.den
  split
  -- ⊢ a.num = a.num / ↑a.den
  · next h => simp [h]
    -- 🎉 no goals
  · next => rfl
    -- 🎉 no goals

protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ Rat.floor r ↔ (z : ℚ) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp [Rat.floor_def']
    -- ⊢ z ≤ n / ↑d ↔ ↑z ≤ mk' n d
    rw [num_den']
    -- ⊢ z ≤ n / ↑d ↔ ↑z ≤ n /. ↑d
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    -- ⊢ z ≤ n / ↑d ↔ ↑z ≤ n /. ↑d
    conv =>
      rhs
      rw [coe_int_eq_divInt, Rat.le_def zero_lt_one h', mul_one]
    exact Int.le_ediv_iff_mul_le h'
    -- 🎉 no goals
#align rat.le_floor Rat.le_floor

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor.symm

protected theorem floor_def {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def' q
#align rat.floor_def Rat.floor_def

theorem floor_int_div_nat_eq_div {n : ℤ} {d : ℕ} : ⌊(↑n : ℚ) / (↑d : ℚ)⌋ = n / (↑d : ℤ) := by
  rw [Rat.floor_def]
  -- ⊢ (↑n / ↑d).num / ↑(↑n / ↑d).den = n / ↑d
  obtain rfl | hd := @eq_zero_or_pos _ _ d
  -- ⊢ (↑n / ↑0).num / ↑(↑n / ↑0).den = n / ↑0
  · simp
    -- 🎉 no goals
  set q := (n : ℚ) / d with q_eq
  -- ⊢ q.num / ↑q.den = n / ↑d
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.den := by
    rw [q_eq]
    exact_mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (by exact_mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  -- ⊢ q.num / ↑q.den = c * q.num / (c * ↑q.den)
  refine' (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left _ <| Int.coe_nat_nonneg q.den).symm
  -- ⊢ 0 < c * ↑q.den
  rwa [← d_eq_c_mul_denom, Int.coe_nat_pos]
  -- 🎉 no goals
#align rat.floor_int_div_nat_eq_div Rat.floor_int_div_nat_eq_div

@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (by exact_mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))
                     -- 🎉 no goals
#align rat.floor_cast Rat.floor_cast

@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]
  -- 🎉 no goals
#align rat.ceil_cast Rat.ceil_cast

@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x := by
  -- Porting note: `simp` worked rather than `simp [H]` in mathlib3
  have H : ((2 : ℚ) : α) = (2 : α) := Rat.cast_coe_nat 2
  -- ⊢ round ↑x = round x
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp [H]
  -- ⊢ round ↑x = round x
  rw [round_eq, round_eq, ← this, floor_cast]
  -- 🎉 no goals
#align rat.round_cast Rat.round_cast

@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_coe_int, floor_cast]
  -- 🎉 no goals
#align rat.cast_fract Rat.cast_fract

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [eq_sub_of_add_eq <| Int.emod_add_ediv n d, Rat.floor_int_div_nat_eq_div]
  -- 🎉 no goals
#align int.mod_nat_eq_sub_mul_floor_rat_div Int.mod_nat_eq_sub_mul_floor_rat_div

theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.coprime d := by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  -- ⊢ coprime (natAbs (↑n - ↑d * ⌊↑n / ↑d⌋)) d
  rw [← this]
  -- ⊢ coprime (natAbs (↑n % ↑d)) d
  have : d.coprime n := n_coprime_d.symm
  -- ⊢ coprime (natAbs (↑n % ↑d)) d
  rwa [Nat.coprime, Nat.gcd_rec] at this
  -- 🎉 no goals
#align nat.coprime_sub_mul_floor_rat_div_of_coprime Nat.coprime_sub_mul_floor_rat_div_of_coprime

namespace Rat

theorem num_lt_succ_floor_mul_den (q : ℚ) : q.num < (⌊q⌋ + 1) * q.den := by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.den by exact_mod_cast this
  -- ⊢ ↑q.num < (↑⌊q⌋ + 1) * ↑q.den
  suffices (q.num : ℚ) < (q - fract q + 1) * q.den by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * q.den = q.num + (1 - fract q) * q.den
    calc
      (q - fract q + 1) * q.den = (q + (1 - fract q)) * q.den := by ring
      _ = q * q.den + (1 - fract q) * q.den := by rw [add_mul]
      _ = q.num + (1 - fract q) * q.den := by simp

    rwa [this]
  suffices 0 < (1 - fract q) * q.den by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact_mod_cast q.pos)
  -- 🎉 no goals
#align rat.num_lt_succ_floor_mul_denom Rat.num_lt_succ_floor_mul_den

theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num := by
  -- we know that the numerator must be positive
  have q_num_pos : 0 < q.num := Rat.num_pos_iff_pos.mpr q_pos
  -- ⊢ (fract q⁻¹).num < q.num
  -- we will work with the absolute value of the numerator, which is equal to the numerator
  have q_num_abs_eq_q_num : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg q_num_pos.le
  -- ⊢ (fract q⁻¹).num < q.num
  set q_inv := (q.den : ℚ) / q.num with q_inv_def
  -- ⊢ (fract q⁻¹).num < q.num
  have q_inv_eq : q⁻¹ = q_inv := Rat.inv_def''
  -- ⊢ (fract q⁻¹).num < q.num
  suffices (q_inv - ⌊q_inv⌋).num < q.num by rwa [q_inv_eq]
  -- ⊢ (q_inv - ↑⌊q_inv⌋).num < q.num
  suffices ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num < q.num by
    field_simp [this, ne_of_gt q_num_pos]
  suffices (q.den : ℤ) - q.num * ⌊q_inv⌋ < q.num by
    -- use that `q.num` and `q.den` are coprime to show that the numerator stays unreduced
    have : ((q.den - q.num * ⌊q_inv⌋ : ℚ) / q.num).num = q.den - q.num * ⌊q_inv⌋ := by
      suffices ((q.den : ℤ) - q.num * ⌊q_inv⌋).natAbs.coprime q.num.natAbs by
        exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos this
      have tmp := Nat.coprime_sub_mul_floor_rat_div_of_coprime q.reduced.symm
      simpa only [Nat.cast_natAbs, abs_of_nonneg q_num_pos.le] using tmp
    rwa [this]
  -- to show the claim, start with the following inequality
  have q_inv_num_denom_ineq : q⁻¹.num - ⌊q⁻¹⌋ * q⁻¹.den < q⁻¹.den := by
    have : q⁻¹.num < (⌊q⁻¹⌋ + 1) * q⁻¹.den := Rat.num_lt_succ_floor_mul_den q⁻¹
    have : q⁻¹.num < ⌊q⁻¹⌋ * q⁻¹.den + q⁻¹.den := by rwa [right_distrib, one_mul] at this
    rwa [← sub_lt_iff_lt_add'] at this
  -- use that `q.num` and `q.den` are coprime to show that q_inv is the unreduced reciprocal
  -- of `q`
  have : q_inv.num = q.den ∧ q_inv.den = q.num.natAbs := by
    have coprime_q_denom_q_num : q.den.coprime q.num.natAbs := q.reduced.symm
    have : Int.natAbs q.den = q.den := by simp
    rw [← this] at coprime_q_denom_q_num
    rw [q_inv_def]
    constructor
    · exact_mod_cast Rat.num_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
    · suffices (((q.den : ℚ) / q.num).den : ℤ) = q.num.natAbs by exact_mod_cast this
      rw [q_num_abs_eq_q_num]
      exact_mod_cast Rat.den_div_eq_of_coprime q_num_pos coprime_q_denom_q_num
  rwa [q_inv_eq, this.left, this.right, q_num_abs_eq_q_num, mul_comm] at q_inv_num_denom_ineq
  -- 🎉 no goals
#align rat.fract_inv_num_lt_num_of_pos Rat.fract_inv_num_lt_num_of_pos

end Rat
