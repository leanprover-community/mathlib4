/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.PNat.Defs

#align_import data.rat.lemmas from "leanprover-community/mathlib"@"550b58538991c8977703fdeb7c9d51a5aa27df11"

/-!
# Further lemmas for the Rational Numbers

-/


namespace Rat

open Rat

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a := by
  cases' e : a /. b with n d h c
  rw [Rat.mk'_eq_divInt, divInt_eq_iff b0 (mod_cast h)] at e
  refine Int.natAbs_dvd.1 <| Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <|
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_ofNat] at this; simp [this]
#align rat.num_dvd Rat.num_dvd

theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  cases' e : a /. b with n d h c
  rw [mk'_eq_divInt, divInt_eq_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
  refine Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <| c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← e]; simp
#align rat.denom_dvd Rat.den_dvd

theorem num_den_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
    ∃ c : ℤ, n = c * q.num ∧ d = c * q.den := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_iff ?_ hd).mp ?_
    · exact Int.natCast_ne_zero.mpr (Rat.den_nz _)
    · rwa [num_divInt_den]
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine ⟨n / q.num, ?_, ?_⟩
  · rw [Int.ediv_mul_cancel hqdn]
  · refine Int.eq_mul_div_of_mul_eq_mul_of_dvd_left ?_ hqdn this
    rw [qdf]
    exact Rat.num_ne_zero.2 ((divInt_ne_zero hd).mpr hn)
#align rat.num_denom_mk Rat.num_den_mk

#noalign rat.mk_pnat_num
#noalign rat.mk_pnat_denom

theorem num_mk (n d : ℤ) : (n /. d).num = d.sign * n / n.gcd d := by
  have (m : ℕ) : Int.natAbs (m + 1) = m + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
  rcases d with ((_ | _) | _) <;>
  rw [← Int.div_eq_ediv_of_dvd] <;>
  simp [divInt, mkRat, Rat.normalize, Nat.succPNat, Int.sign, Int.gcd,
    Int.zero_ediv, Int.ofNat_dvd_left, Nat.gcd_dvd_left, this]
#align rat.num_mk Rat.num_mk

theorem den_mk (n d : ℤ) : (n /. d).den = if d = 0 then 1 else d.natAbs / n.gcd d := by
  have (m : ℕ) : Int.natAbs (m + 1) = m + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
  rcases d with ((_ | _) | _) <;>
    simp [divInt, mkRat, Rat.normalize, Nat.succPNat, Int.sign, Int.gcd,
      if_neg (Nat.cast_add_one_ne_zero _), this]
#align rat.denom_mk Rat.den_mk

#noalign rat.mk_pnat_denom_dvd

theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den := by
  rw [add_def, normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right
#align rat.add_denom_dvd Rat.add_den_dvd

theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def, normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right
#align rat.mul_denom_dvd Rat.mul_den_dvd

theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]
#align rat.mul_num Rat.mul_num

theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]
#align rat.mul_denom Rat.mul_den

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Int.ofNat_one, Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul (q.reduced.mul_right q.reduced)
#align rat.mul_self_num Rat.mul_self_num

theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul (q.reduced.mul_right q.reduced)
#align rat.mul_self_denom Rat.mul_self_den

theorem add_num_den (q r : ℚ) :
    q + r = (q.num * r.den + q.den * r.num : ℤ) /. (↑q.den * ↑r.den : ℤ) := by
  have hqd : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]
#align rat.add_num_denom Rat.add_num_den


theorem isSquare_iff {q : ℚ} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den := by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num, mul_self_den]
    simp only [isSquare_mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm, ← Int.cast_mul, ← Nat.cast_mul, ← hnr, ← hdr, num_div_den]

@[norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℚ) ↔ IsSquare n := by
  simp_rw [isSquare_iff, num_natCast, den_natCast, isSquare_one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]
theorem isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z := by
  simp_rw [isSquare_iff, intCast_num, intCast_den, isSquare_one, and_true]

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (no_index (OfNat.ofNat n) : ℚ) ↔ IsSquare (OfNat.ofNat n : ℕ) :=
  isSquare_natCast_iff

section Casts

theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den :=
  haveI : (n : ℚ) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this
#align rat.exists_eq_mul_div_num_and_eq_mul_div_denom Rat.exists_eq_mul_div_num_and_eq_mul_div_den

theorem mul_num_den' (q r : ℚ) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  let s := q.num * r.num /. (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_den]
  rw [Int.mul_assoc, Int.mul_assoc, mul_eq_mul_left_iff, or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_mul_divInt q.num r.num (mod_cast q.den_ne_zero) (mod_cast r.den_ne_zero)
  rw [num_divInt_den, num_divInt_den] at h
  rw [h, mul_comm, ← Rat.eq_iff_mul_eq_mul, ← divInt_eq_div]
#align rat.mul_num_denom' Rat.mul_num_den'

theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.den + r.num * q.den) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_den]
  repeat rw [Int.mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_add_divInt q.num r.num (mod_cast q.den_ne_zero) (mod_cast r.den_ne_zero)
  rw [num_divInt_den, num_divInt_den] at h
  rw [h]
  rw [mul_comm]
  apply Rat.eq_iff_mul_eq_mul.mp
  rw [← divInt_eq_div]
#align rat.add_num_denom' Rat.add_num_den'

theorem substr_num_den' (q r : ℚ) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← den_neg_eq_den r,
    add_num_den' q (-r)]
#align rat.substr_num_denom' Rat.substr_num_den'

end Casts

protected theorem inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ := by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt', eq_self_iff_true, Rat.divInt_neg]
#align rat.inv_neg Rat.inv_neg

theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = a := by
  -- Porting note: was `lift b to ℕ using le_of_lt hb0`
  rw [← Int.natAbs_of_nonneg hb0.le, ← Rat.divInt_eq_div,
    ← mk_eq_divInt _ _ (Int.natAbs_ne_zero.mpr hb0.ne') h]
#align rat.num_div_eq_of_coprime Rat.num_div_eq_of_coprime

theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b := by
  -- Porting note: was `lift b to ℕ using le_of_lt hb0`
  rw [← Int.natAbs_of_nonneg hb0.le, ← Rat.divInt_eq_div,
    ← mk_eq_divInt _ _ (Int.natAbs_ne_zero.mpr hb0.ne') h]
#align rat.denom_div_eq_of_coprime Rat.den_div_eq_of_coprime

theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]
#align rat.div_int_inj Rat.div_int_inj

@[norm_cast]
theorem intCast_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n := by
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, Int.zero_div, zero_div, Int.ediv_zero]
  · have : (n : ℚ) ≠ 0 := by rwa [← coe_int_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, Ne, not_false_iff, div_self this]
#align rat.coe_int_div_self Rat.intCast_div_self

@[norm_cast]
theorem natCast_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  intCast_div_self n
#align rat.coe_nat_div_self Rat.natCast_div_self

theorem intCast_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b, Int.mul_ediv_assoc c (dvd_refl b), Int.cast_mul,
    intCast_div_self, Int.cast_mul, mul_div_assoc]
#align rat.coe_int_div Rat.intCast_div

theorem natCast_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b :=
  intCast_div a b (Int.ofNat_dvd.mpr h)
#align rat.coe_nat_div Rat.natCast_div

theorem den_div_intCast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m := by
  replace hn : (n : ℚ) ≠ 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)
#align rat.denom_div_cast_eq_one_iff Rat.den_div_intCast_eq_one_iff

theorem den_div_natCast_eq_one_iff (m n : ℕ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m :=
  (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd

@[deprecated (since := "2024-05-11")] alias den_div_cast_eq_one_iff := den_div_intCast_eq_one_iff

theorem inv_intCast_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 := by
  rw [← ofInt_eq_cast, ofInt, mk_eq_divInt, Rat.inv_divInt', divInt_eq_div, Nat.cast_one]
  apply num_div_eq_of_coprime ha0
  rw [Int.natAbs_one]
  exact Nat.coprime_one_left _
#align rat.inv_coe_int_num_of_pos Rat.inv_intCast_num_of_pos

theorem inv_natCast_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : ℤ))
#align rat.inv_coe_nat_num_of_pos Rat.inv_natCast_num_of_pos

theorem inv_intCast_den_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.den : ℤ) = a := by
  rw [← ofInt_eq_cast, ofInt, mk_eq_divInt, Rat.inv_divInt', divInt_eq_div, Nat.cast_one]
  apply den_div_eq_of_coprime ha0
  rw [Int.natAbs_one]
  exact Nat.coprime_one_left _
#align rat.inv_coe_int_denom_of_pos Rat.inv_intCast_den_of_pos

theorem inv_natCast_den_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.den = a := by
  rw [← Int.ofNat_inj, ← Int.cast_natCast a, inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]
#align rat.inv_coe_nat_denom_of_pos Rat.inv_natCast_den_of_pos

@[simp]
theorem inv_intCast_num (a : ℤ) : (a : ℚ)⁻¹.num = Int.sign a := by
  rcases lt_trichotomy a 0 with lt | rfl | gt
  · obtain ⟨a, rfl⟩ : ∃ b, -b = a := ⟨-a, a.neg_neg⟩
    simp at lt
    simp [Rat.inv_neg, inv_intCast_num_of_pos lt, (Int.sign_eq_one_iff_pos _).mpr lt]
  · rfl
  · simp [inv_intCast_num_of_pos gt, (Int.sign_eq_one_iff_pos _).mpr gt]
#align rat.inv_coe_int_num Rat.inv_intCast_num

@[simp]
theorem inv_natCast_num (a : ℕ) : (a : ℚ)⁻¹.num = Int.sign a :=
  inv_intCast_num a
#align rat.inv_coe_nat_num Rat.inv_natCast_num

@[simp]
theorem inv_ofNat_num (a : ℕ) [a.AtLeastTwo] : (no_index (OfNat.ofNat a : ℚ))⁻¹.num = 1 :=
  inv_natCast_num_of_pos (NeZero.pos a)

@[simp]
theorem inv_intCast_den (a : ℤ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a.natAbs := by
  rw [← Int.ofNat_inj]
  rcases lt_trichotomy a 0 with lt | rfl | gt
  · obtain ⟨a, rfl⟩ : ∃ b, -b = a := ⟨-a, a.neg_neg⟩
    simp at lt
    rw [if_neg (by omega)]
    simp [Rat.inv_neg, inv_intCast_den_of_pos lt, abs_of_pos lt]
  · rfl
  · rw [if_neg (by omega)]
    simp [inv_intCast_den_of_pos gt, abs_of_pos gt]
#align rat.inv_coe_int_denom Rat.inv_intCast_den

@[simp]
theorem inv_natCast_den (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by
  simpa [-inv_intCast_den, ofInt_eq_cast] using inv_intCast_den a
#align rat.inv_coe_nat_denom Rat.inv_natCast_den

@[deprecated (since := "2024-04-05")] alias coe_int_div_self := intCast_div_self
@[deprecated (since := "2024-04-05")] alias coe_nat_div_self := natCast_div_self
@[deprecated (since := "2024-04-05")] alias coe_int_div := intCast_div
@[deprecated (since := "2024-04-05")] alias coe_nat_div := natCast_div
@[deprecated (since := "2024-04-05")] alias inv_coe_int_num_of_pos := inv_intCast_num_of_pos
@[deprecated (since := "2024-04-05")] alias inv_coe_nat_num_of_pos := inv_natCast_num_of_pos
@[deprecated (since := "2024-04-05")] alias inv_coe_int_den_of_pos := inv_intCast_den_of_pos
@[deprecated (since := "2024-04-05")] alias inv_coe_nat_den_of_pos := inv_natCast_den_of_pos
@[deprecated (since := "2024-04-05")] alias inv_coe_int_num := inv_intCast_num
@[deprecated (since := "2024-04-05")] alias inv_coe_nat_num := inv_natCast_num
@[deprecated (since := "2024-04-05")] alias inv_coe_int_den := inv_intCast_den
@[deprecated (since := "2024-04-05")] alias inv_coe_nat_den := inv_natCast_den

@[simp]
theorem inv_ofNat_den (a : ℕ) [a.AtLeastTwo] :
    (no_index (OfNat.ofNat a : ℚ))⁻¹.den = OfNat.ofNat a :=
  inv_natCast_den_of_pos (NeZero.pos a)

protected theorem «forall» {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, p (a / b) :=
  ⟨fun h _ _ => h _,
   fun h q => by
    have := h q.num q.den
    rwa [Int.cast_natCast, num_div_den q] at this⟩
#align rat.forall Rat.forall

protected theorem «exists» {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, p (a / b) :=
  ⟨fun ⟨r, hr⟩ => ⟨r.num, r.den, by convert hr; convert num_div_den r⟩, fun ⟨a, b, h⟩ => ⟨_, h⟩⟩
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
