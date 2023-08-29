/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Div
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

#align_import data.rat.lemmas from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Further lemmas for the Rational Numbers

-/


namespace Rat

open Rat

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a := by
  cases' e : a /. b with n d h c
  -- ⊢ (mk' n d).num ∣ a
  rw [Rat.num_den', divInt_eq_iff b0 (ne_of_gt (Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h)))] at e
  -- ⊢ (mk' n d).num ∣ a
  refine' Int.natAbs_dvd.1 <| Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| c.dvd_of_dvd_mul_right _
  -- ⊢ Int.natAbs n ∣ Int.natAbs a * d
  have := congr_arg Int.natAbs e
  -- ⊢ Int.natAbs n ∣ Int.natAbs a * d
  simp only [Int.natAbs_mul, Int.natAbs_ofNat] at this; simp [this]
  -- ⊢ Int.natAbs n ∣ Int.natAbs a * d
                                                        -- 🎉 no goals
#align rat.num_dvd Rat.num_dvd

theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  -- ⊢ ↑(a /. b).den ∣ b
                         -- 🎉 no goals
  cases' e : a /. b with n d h c
  -- ⊢ ↑(mk' n d).den ∣ b
  rw [num_den', divInt_eq_iff b0 (ne_of_gt (Int.coe_nat_pos.2 (Nat.pos_of_ne_zero h)))] at e
  -- ⊢ ↑(mk' n d).den ∣ b
  refine' Int.dvd_natAbs.1 <| Int.coe_nat_dvd.2 <| c.symm.dvd_of_dvd_mul_left _
  -- ⊢ d ∣ Int.natAbs n * Int.natAbs b
  rw [← Int.natAbs_mul, ← Int.coe_nat_dvd, Int.dvd_natAbs, ← e]; simp
  -- ⊢ ↑d ∣ a * ↑d
                                                                 -- 🎉 no goals
#align rat.denom_dvd Rat.den_dvd

theorem num_den_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
    ∃ c : ℤ, n = c * q.num ∧ d = c * q.den := by
  obtain rfl | hn := eq_or_ne n 0
  -- ⊢ ∃ c, 0 = c * q.num ∧ d = c * ↑q.den
  · simp [qdf]
    -- 🎉 no goals
  have : q.num * d = n * ↑q.den := by
    refine' (divInt_eq_iff _ hd).mp _
    · exact Int.coe_nat_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine' ⟨n / q.num, _, _⟩
  -- ⊢ n = n / q.num * q.num
  · rw [Int.ediv_mul_cancel hqdn]
    -- 🎉 no goals
  · refine' Int.eq_mul_div_of_mul_eq_mul_of_dvd_left _ hqdn this
    -- ⊢ q.num ≠ 0
    rw [qdf]
    -- ⊢ (n /. d).num ≠ 0
    exact Rat.num_ne_zero_of_ne_zero ((divInt_ne_zero hd).mpr hn)
    -- 🎉 no goals
#align rat.num_denom_mk Rat.num_den_mk

#noalign rat.mk_pnat_num
#noalign rat.mk_pnat_denom

theorem num_mk (n d : ℤ) : (n /. d).num = d.sign * n / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
  rw [←Int.div_eq_ediv_of_dvd] <;>
  -- ⊢ (n /. Int.ofNat Nat.zero).num = Int.div (Int.sign (Int.ofNat Nat.zero) * n)  …
  -- ⊢ (n /. Int.ofNat (Nat.succ n✝)).num = Int.div (Int.sign (Int.ofNat (Nat.succ  …
  -- ⊢ (n /. Int.negSucc a✝).num = Int.div (Int.sign (Int.negSucc a✝) * n) ↑(Int.gc …
  simp [divInt, mkRat, Rat.normalize, Nat.succPNat, Int.sign, Int.gcd, -Nat.cast_succ,
    Int.zero_ediv, Int.ofNat_dvd_left, Nat.gcd_dvd_left]
#align rat.num_mk Rat.num_mk

theorem den_mk (n d : ℤ) : (n /. d).den = if d = 0 then 1 else d.natAbs / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
    simp [divInt, mkRat, Rat.normalize, Nat.succPNat, Int.sign, Int.gcd, -Nat.cast_succ]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align rat.denom_mk Rat.den_mk

#noalign rat.mk_pnat_denom_dvd

theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den := by
  rw [add_def, normalize_eq]
  -- ⊢ (mk' ((q₁.num * ↑q₂.den + q₂.num * ↑q₁.den) / ↑(Nat.gcd (Int.natAbs (q₁.num  …
  apply Nat.div_dvd_of_dvd
  -- ⊢ Nat.gcd (Int.natAbs (q₁.num * ↑q₂.den + q₂.num * ↑q₁.den)) (q₁.den * q₂.den) …
  apply Nat.gcd_dvd_right
  -- 🎉 no goals
#align rat.add_denom_dvd Rat.add_den_dvd

theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def, normalize_eq]
  -- ⊢ (mk' (q₁.num * q₂.num / ↑(Nat.gcd (Int.natAbs (q₁.num * q₂.num)) (q₁.den * q …
  apply Nat.div_dvd_of_dvd
  -- ⊢ Nat.gcd (Int.natAbs (q₁.num * q₂.num)) (q₁.den * q₂.den) ∣ q₁.den * q₂.den
  apply Nat.gcd_dvd_right
  -- 🎉 no goals
#align rat.mul_denom_dvd Rat.mul_den_dvd

theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]
  -- 🎉 no goals
#align rat.mul_num Rat.mul_num

theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]
  -- 🎉 no goals
#align rat.mul_denom Rat.mul_den

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.coprime.gcd_eq_one, Int.ofNat_one, Int.ediv_one]
  -- ⊢ Nat.coprime (Int.natAbs q.num * Int.natAbs q.num) (q.den * q.den)
  exact (q.reduced.mul_right q.reduced).mul (q.reduced.mul_right q.reduced)
  -- 🎉 no goals
#align rat.mul_self_num Rat.mul_self_num

theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.coprime.gcd_eq_one, Nat.div_one]
  -- ⊢ Nat.coprime (Int.natAbs q.num * Int.natAbs q.num) (q.den * q.den)
  exact (q.reduced.mul_right q.reduced).mul (q.reduced.mul_right q.reduced)
  -- 🎉 no goals
#align rat.mul_self_denom Rat.mul_self_den

theorem add_num_den (q r : ℚ) :
    q + r = (q.num * r.den + q.den * r.num : ℤ) /. (↑q.den * ↑r.den : ℤ) := by
  have hqd : (q.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 q.den_pos
  -- ⊢ q + r = (q.num * ↑r.den + ↑q.den * r.num) /. (↑q.den * ↑r.den)
  have hrd : (r.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 r.den_pos
  -- ⊢ q + r = (q.num * ↑r.den + ↑q.den * r.num) /. (↑q.den * ↑r.den)
  conv_lhs => rw [← @num_den q, ← @num_den r, Rat.add_def'' hqd hrd]
  -- ⊢ (q.num * ↑r.den + r.num * ↑q.den) /. (↑q.den * ↑r.den) = (q.num * ↑r.den + ↑ …
  rw [mul_comm r.num q.den]
  -- 🎉 no goals
#align rat.add_num_denom Rat.add_num_den

section Casts

theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den :=
  haveI : (n : ℚ) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
                                             -- 🎉 no goals
  Rat.num_den_mk d_ne_zero this
#align rat.exists_eq_mul_div_num_and_eq_mul_div_denom Rat.exists_eq_mul_div_num_and_eq_mul_div_den

theorem mul_num_den' (q r : ℚ) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  let s := q.num * r.num /. (q.den * r.den : ℤ)
  -- ⊢ (q * r).num * ↑q.den * ↑r.den = q.num * r.num * ↑(q * r).den
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  -- ⊢ (q * r).num * ↑q.den * ↑r.den = q.num * r.num * ↑(q * r).den
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  -- ⊢ ↑q.den * ↑r.den * (q * r).num = c * (↑(q.num * r.num) / ↑(↑q.den * ↑r.den)). …
  nth_rw 1 [c_mul_den]
  -- ⊢ c * ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num = c * (↑(q.nu …
  repeat' rw [Int.mul_assoc]
  -- ⊢ c * (↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num) = c * ((↑(q …
  apply mul_eq_mul_left_iff.2
  -- ⊢ ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num = (↑(q.num * r.nu …
  rw [or_iff_not_imp_right]
  -- ⊢ ¬c = 0 → ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num = (↑(q.n …
  intro
  -- ⊢ ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num = (↑(q.num * r.nu …
  have h : _ = s :=
    @mul_def' q.num q.den r.num r.den (Int.coe_nat_ne_zero_iff_pos.mpr q.pos)
      (Int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_den, num_den] at h
  -- ⊢ ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * (q * r).num = (↑(q.num * r.nu …
  rw [h]
  -- ⊢ ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den * s.num = (↑(q.num * r.num) / ↑ …
  rw [mul_comm]
  -- ⊢ s.num * ↑(↑(q.num * r.num) / ↑(↑q.den * ↑r.den)).den = (↑(q.num * r.num) / ↑ …
  apply Rat.eq_iff_mul_eq_mul.mp
  -- ⊢ s = ↑(q.num * r.num) / ↑(↑q.den * ↑r.den)
  rw [← divInt_eq_div]
  -- 🎉 no goals
#align rat.mul_num_denom' Rat.mul_num_den'

theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : ℤ)
  -- ⊢ (q + r).num * ↑q.den * ↑r.den = (q.num * ↑r.den + r.num * ↑q.den) * ↑(q + r) …
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  -- ⊢ (q + r).num * ↑q.den * ↑r.den = (q.num * ↑r.den + r.num * ↑q.den) * ↑(q + r) …
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  -- ⊢ ↑q.den * ↑r.den * (q + r).num = c * (↑(q.num * ↑r.den + r.num * ↑q.den) / ↑( …
  nth_rw 1 [c_mul_den]
  -- ⊢ c * ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q + r) …
  repeat' rw [Int.mul_assoc]
  -- ⊢ c * (↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q + r …
  apply mul_eq_mul_left_iff.2
  -- ⊢ ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q + r).num …
  rw [or_iff_not_imp_right]
  -- ⊢ ¬c = 0 → ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q …
  intro
  -- ⊢ ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q + r).num …
  have h : _ = s :=
    @add_def'' q.num q.den r.num r.den (Int.coe_nat_ne_zero_iff_pos.mpr q.pos)
      (Int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_den, num_den] at h
  -- ⊢ ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * (q + r).num …
  rw [h]
  -- ⊢ ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den * s.num = (↑( …
  rw [mul_comm]
  -- ⊢ s.num * ↑(↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)).den = (↑( …
  apply Rat.eq_iff_mul_eq_mul.mp
  -- ⊢ s = ↑(q.num * ↑r.den + r.num * ↑q.den) / ↑(↑q.den * ↑r.den)
  rw [← divInt_eq_div]
  -- 🎉 no goals
#align rat.add_num_denom' Rat.add_num_den'

theorem substr_num_den' (q r : ℚ) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← den_neg_eq_den r,
    add_num_den' q (-r)]
#align rat.substr_num_denom' Rat.substr_num_den'

end Casts

theorem inv_def'' {q : ℚ} : q⁻¹ = (q.den : ℚ) / q.num := by
  conv_lhs => rw [← @num_den q]
  -- ⊢ (q.num /. ↑q.den)⁻¹ = ↑q.den / ↑q.num
  rw [inv_def', divInt_eq_div]; rfl
  -- ⊢ ↑↑q.den / ↑q.num = ↑q.den / ↑q.num
                                -- 🎉 no goals
#align rat.inv_def' Rat.inv_def''

protected theorem inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ := by
  rw [← @num_den q]
  -- ⊢ (-(q.num /. ↑q.den))⁻¹ = -(q.num /. ↑q.den)⁻¹
  simp only [Rat.neg_def, Rat.inv_def', eq_self_iff_true, Rat.divInt_neg_den]
  -- 🎉 no goals
#align rat.inv_neg Rat.inv_neg

@[simp]
theorem mul_den_eq_num {q : ℚ} : q * q.den = q.num := by
  suffices (q.num /. ↑q.den) * (↑q.den /. 1) = q.num /. 1 by
    conv => pattern (occs := 1)q; (rw [← @num_den q])
    simp only [coe_int_eq_divInt, coe_nat_eq_divInt, num_den] at this ⊢; assumption
  have : (q.den : ℤ) ≠ 0 := ne_of_gt (by exact_mod_cast q.pos)
  -- ⊢ q.num /. ↑q.den * (↑q.den /. 1) = q.num /. 1
  rw [Rat.mul_def' this one_ne_zero, mul_comm (q.den : ℤ) 1, divInt_mul_right this]
  -- 🎉 no goals
#align rat.mul_denom_eq_num Rat.mul_den_eq_num

theorem den_div_cast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m := by
  replace hn : (n : ℚ) ≠ 0
  -- ⊢ ↑n ≠ 0
  · rwa [Ne.def, ← Int.cast_zero, coe_int_inj]
    -- 🎉 no goals
  constructor
  -- ⊢ (↑m / ↑n).den = 1 → n ∣ m
  · intro h
    -- ⊢ n ∣ m
    -- Porting note: was `lift (m : ℚ) / n to ℤ using h with k hk`
    use ((m : ℚ) / n).num
    -- ⊢ m = n * (↑m / ↑n).num
    have hk := Rat.coe_int_num_of_den_eq_one h
    -- ⊢ m = n * (↑m / ↑n).num
    simp_rw [eq_div_iff_mul_eq hn, ← Int.cast_mul] at hk
    -- ⊢ m = n * (↑m / ↑n).num
    rwa [mul_comm, eq_comm, coe_int_inj] at hk
    -- 🎉 no goals
  · rintro ⟨d, rfl⟩
    -- ⊢ (↑(n * d) / ↑n).den = 1
    rw [Int.cast_mul, mul_comm, mul_div_cancel _ hn, Rat.coe_int_den]
    -- 🎉 no goals
#align rat.denom_div_cast_eq_one_iff Rat.den_div_cast_eq_one_iff

theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = a := by
  -- Porting note: was `lift b to ℕ using le_of_lt hb0`
  rw [←Int.natAbs_of_nonneg hb0.le, ← Rat.divInt_eq_div,
    ←mk_eq_divInt _ _ (Int.natAbs_ne_zero.mpr hb0.ne') h]
#align rat.num_div_eq_of_coprime Rat.num_div_eq_of_coprime

theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b := by
  -- Porting note: was `lift b to ℕ using le_of_lt hb0`
  rw [←Int.natAbs_of_nonneg hb0.le, ← Rat.divInt_eq_div,
    ←mk_eq_divInt _ _ (Int.natAbs_ne_zero.mpr hb0.ne') h]
#align rat.denom_div_eq_of_coprime Rat.den_div_eq_of_coprime

theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.coprime a.natAbs b.natAbs)
    (h2 : Nat.coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  apply And.intro
  -- ⊢ a = c
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
    -- 🎉 no goals
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]
    -- 🎉 no goals
#align rat.div_int_inj Rat.div_int_inj

@[norm_cast]
theorem coe_int_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n := by
  by_cases hn : n = 0
  -- ⊢ ↑(n / n) = ↑n / ↑n
  · subst hn
    -- ⊢ ↑(0 / 0) = ↑0 / ↑0
    simp only [Int.cast_zero, Int.zero_div, zero_div]
    -- 🎉 no goals
  · have : (n : ℚ) ≠ 0 := by rwa [← coe_int_inj] at hn
    -- ⊢ ↑(n / n) = ↑n / ↑n
    simp only [Int.ediv_self hn, Int.cast_one, Ne.def, not_false_iff, div_self this]
    -- 🎉 no goals
#align rat.coe_int_div_self Rat.coe_int_div_self

@[norm_cast]
theorem coe_nat_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  coe_int_div_self n
#align rat.coe_nat_div_self Rat.coe_nat_div_self

theorem coe_int_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  -- ⊢ ↑(b * c / b) = ↑(b * c) / ↑b
  rw [mul_comm b, Int.mul_ediv_assoc c (dvd_refl b), Int.cast_mul,
    coe_int_div_self, Int.cast_mul, mul_div_assoc]
#align rat.coe_int_div Rat.coe_int_div

theorem coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  -- ⊢ ↑(b * c / b) = ↑(b * c) / ↑b
  simp only [mul_comm b, Nat.mul_div_assoc c (dvd_refl b), Nat.cast_mul, mul_div_assoc,
    coe_nat_div_self]
#align rat.coe_nat_div Rat.coe_nat_div

theorem inv_coe_int_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 := by
  rw [← ofInt_eq_cast, ofInt, mk_eq_divInt, Rat.inv_def', divInt_eq_div, Nat.cast_one]
  -- ⊢ (↑1 / ↑a).num = 1
  apply num_div_eq_of_coprime ha0
  -- ⊢ Nat.coprime (Int.natAbs 1) (Int.natAbs a)
  rw [Int.natAbs_one]
  -- ⊢ Nat.coprime 1 (Int.natAbs a)
  exact Nat.coprime_one_left _
  -- 🎉 no goals
#align rat.inv_coe_int_num_of_pos Rat.inv_coe_int_num_of_pos

theorem inv_coe_nat_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_coe_int_num_of_pos (by exact_mod_cast ha0 : 0 < (a : ℤ))
                             -- 🎉 no goals
#align rat.inv_coe_nat_num_of_pos Rat.inv_coe_nat_num_of_pos

theorem inv_coe_int_den_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.den : ℤ) = a := by
  rw [← ofInt_eq_cast, ofInt, mk_eq_divInt, Rat.inv_def', divInt_eq_div, Nat.cast_one]
  -- ⊢ ↑(↑1 / ↑a).den = a
  apply den_div_eq_of_coprime ha0
  -- ⊢ Nat.coprime (Int.natAbs 1) (Int.natAbs a)
  rw [Int.natAbs_one]
  -- ⊢ Nat.coprime 1 (Int.natAbs a)
  exact Nat.coprime_one_left _
  -- 🎉 no goals
#align rat.inv_coe_int_denom_of_pos Rat.inv_coe_int_den_of_pos

theorem inv_coe_nat_den_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.den = a := by
  rw [← Int.ofNat_inj, ← Int.cast_ofNat a, inv_coe_int_den_of_pos]
  -- ⊢ 0 < ↑a
  rwa [Nat.cast_pos]
  -- 🎉 no goals
#align rat.inv_coe_nat_denom_of_pos Rat.inv_coe_nat_den_of_pos

@[simp]
theorem inv_coe_int_num (a : ℤ) : (a : ℚ)⁻¹.num = Int.sign a := by
  induction a using Int.induction_on <;>
    simp [← Int.negSucc_coe', Int.negSucc_coe, -neg_add_rev, Rat.inv_neg, Int.ofNat_add_one_out,
      -Nat.cast_succ, inv_coe_nat_num_of_pos, -Int.cast_negSucc, @eq_comm ℤ 1,
      Int.sign_eq_one_of_pos, ofInt_eq_cast]
#align rat.inv_coe_int_num Rat.inv_coe_int_num

@[simp]
theorem inv_coe_nat_num (a : ℕ) : (a : ℚ)⁻¹.num = Int.sign a :=
  inv_coe_int_num a
#align rat.inv_coe_nat_num Rat.inv_coe_nat_num

@[simp]
theorem inv_coe_int_den (a : ℤ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a.natAbs := by
  induction a using Int.induction_on <;>
    simp [← Int.negSucc_coe', Int.negSucc_coe, -neg_add_rev, Rat.inv_neg, Int.ofNat_add_one_out,
      -Nat.cast_succ, inv_coe_nat_den_of_pos, -Int.cast_negSucc, ofInt_eq_cast]
#align rat.inv_coe_int_denom Rat.inv_coe_int_den

@[simp]
theorem inv_coe_nat_den (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by
  simpa [-inv_coe_int_den, ofInt_eq_cast] using inv_coe_int_den a
  -- 🎉 no goals
#align rat.inv_coe_nat_denom Rat.inv_coe_nat_den

protected theorem «forall» {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, p (a / b) :=
  ⟨fun h _ _ => h _,
   fun h q => by
    have := h q.num q.den
    -- ⊢ p q
    rwa [Int.cast_ofNat, num_div_den q] at this⟩
    -- 🎉 no goals
#align rat.forall Rat.forall

protected theorem «exists» {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, p (a / b) :=
  ⟨fun ⟨r, hr⟩ => ⟨r.num, r.den, by convert hr; convert num_div_den r⟩, fun ⟨a, b, h⟩ => ⟨_, h⟩⟩
                                    -- ⊢ ↑r.num / ↑↑r.den = r
                                                -- 🎉 no goals
#align rat.exists Rat.exists

/-!
### Denominator as `ℕ+`
-/


section PNatDen

/-- Denominator as `ℕ+`. -/
def pnatDen (x : ℚ) : ℕ+ :=
  ⟨x.den, x.pos⟩
#align rat.pnat_denom Rat.pnatDen

@[simp]
theorem coe_pnatDen (x : ℚ) : (x.pnatDen : ℕ) = x.den :=
  rfl
#align rat.coe_pnat_denom Rat.coe_pnatDen

#noalign rat.mk_pnat_pnat_denom_eq

theorem pnatDen_eq_iff_den_eq {x : ℚ} {n : ℕ+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff
#align rat.pnat_denom_eq_iff_denom_eq Rat.pnatDen_eq_iff_den_eq

@[simp]
theorem pnatDen_one : (1 : ℚ).pnatDen = 1 :=
  rfl
#align rat.pnat_denom_one Rat.pnatDen_one

@[simp]
theorem pnatDen_zero : (0 : ℚ).pnatDen = 1 :=
  rfl
#align rat.pnat_denom_zero Rat.pnatDen_zero

end PNatDen

end Rat
