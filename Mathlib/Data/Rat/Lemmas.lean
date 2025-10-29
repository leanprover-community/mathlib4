/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.PNat.Defs

/-!
# Further lemmas for the Rational Numbers

-/


namespace Rat

-- TODO: move this to Lean
attribute [norm_cast] num_intCast den_intCast

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a := by
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [Rat.mk'_eq_divInt, divInt_eq_divInt_iff b0 (mod_cast h)] at e
  refine Int.natAbs_dvd.1 <| Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <|
    c.dvd_of_dvd_mul_right ?_
  have := congr_arg Int.natAbs e
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at this; simp [this]

theorem den_dvd (a b : ℤ) : ((a /. b).den : ℤ) ∣ b := by
  by_cases b0 : b = 0; · simp [b0]
  rcases e : a /. b with ⟨n, d, h, c⟩
  rw [mk'_eq_divInt,
    divInt_eq_divInt_iff b0 (ne_of_gt (Int.natCast_pos.2 (Nat.pos_of_ne_zero h)))] at e
  refine Int.dvd_natAbs.1 <| Int.natCast_dvd_natCast.2 <| c.symm.dvd_of_dvd_mul_left ?_
  rw [← Int.natAbs_mul, ← Int.natCast_dvd_natCast, Int.dvd_natAbs, ← e]; simp

theorem num_den_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) :
    ∃ c : ℤ, n = c * q.num ∧ d = c * q.den := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [qdf]
  have : q.num * d = n * ↑q.den := by
    refine (divInt_eq_divInt_iff ?_ hd).mp ?_
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

theorem num_mk (n d : ℤ) : (n /. d).num = d.sign * n / n.gcd d := by
  have (m : ℕ) : Int.natAbs (m + 1) = m + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
  rcases d with ((_ | _) | _) <;>
  simp [divInt, mkRat, Rat.normalize_eq, Int.sign, Int.gcd,
    Int.zero_ediv, this]

theorem den_mk (n d : ℤ) : (n /. d).den = if d = 0 then 1 else d.natAbs / n.gcd d := by
  have (m : ℕ) : Int.natAbs (m + 1) = m + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, Int.natAbs_cast]
  rcases d with ((_ | _) | _) <;>
    simp [divInt, mkRat, Rat.normalize_eq, Int.gcd,
      if_neg (Nat.cast_add_one_ne_zero _), this]

theorem add_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den := by
  rw [add_def, normalize_eq, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  apply Int.dvd_add
    <;> apply dvd_mul_of_dvd_right <;> rw [Int.natCast_dvd_natCast]
    <;> [exact Nat.gcd_dvd_right _ _; exact Nat.gcd_dvd_left _ _]

theorem sub_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den.lcm q₂.den := by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)

theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den :=
  (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

theorem sub_den_dvd (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den * q₂.den :=
  (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def, normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right

theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]

theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]

@[simp]
theorem add_intCast_den (q : ℚ) (n : ℤ) : (q + n).den = q.den := by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]
theorem intCast_add_den (n : ℤ) (q : ℚ) : (n + q).den = q.den := by
  rw [add_comm, add_intCast_den]

@[simp]
theorem sub_intCast_den (q : ℚ) (n : ℤ) : (q - n).den = q.den := by
  rw [sub_eq_add_neg, ← Int.cast_neg, add_intCast_den]

@[simp]
theorem intCast_sub_den (n : ℤ) (q : ℚ) : (n - q).den = q.den := by
  rw [sub_eq_add_neg, intCast_add_den, neg_den]

@[simp]
theorem add_natCast_den (q : ℚ) (n : ℕ) : (q + n).den = q.den := mod_cast add_intCast_den q n

@[simp]
theorem natCast_add_den (n : ℕ) (q : ℚ) : (n + q).den = q.den := mod_cast intCast_add_den n q

@[simp]
theorem sub_natCast_den (q : ℚ) (n : ℕ) : (q - n).den = q.den := mod_cast sub_intCast_den q n

@[simp]
theorem natCast_sub_den (n : ℕ) (q : ℚ) : (n - q).den = q.den := mod_cast intCast_sub_den n q

@[simp] theorem add_ofNat_den (q : ℚ) (n : ℕ) : (q + ofNat(n)).den = q.den := add_natCast_den q n
@[simp] theorem ofNat_add_den (n : ℕ) (q : ℚ) : (ofNat(n) + q).den = q.den := natCast_add_den n q
@[simp] theorem sub_ofNat_den (q : ℚ) (n : ℕ) : (q - ofNat(n)).den = q.den := sub_natCast_den ..
@[simp] theorem ofNat_sub_den (n : ℕ) (q : ℚ) : (ofNat(n) - q).den = q.den := natCast_sub_den ..

/-- A version of `Rat.mul_den` without division. -/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : ℚ) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

/-- A version of `Rat.mul_num` without division. -/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : ℚ) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Int.ofNat_one, Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

theorem add_num_den (q r : ℚ) :
    q + r = (q.num * r.den + q.den * r.num : ℤ) /. (↑q.den * ↑r.den : ℤ) := by
  have hqd : (q.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 q.den_pos
  have hrd : (r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.2 r.den_pos
  conv_lhs => rw [← num_divInt_den q, ← num_divInt_den r, divInt_add_divInt _ _ hqd hrd]
  rw [mul_comm r.num q.den]

theorem num_add (q r : ℚ) : (q + r).num =
    (q.num * r.den + r.num * q.den) /
    (q.num * r.den + r.num * q.den).natAbs.gcd (q.den * r.den) := by
  simp [Rat.add_def, Rat.normalize]

theorem den_add (q r : ℚ) : (q + r).den =
    (q.den * r.den) / (q.num * r.den + r.num * q.den).natAbs.gcd (q.den * r.den) := by
  simp [Rat.add_def, Rat.normalize]

private lemma num_add_int_gcd_den_eq_one (q : ℚ) (z : ℤ) :
    (q.num + z * ↑q.den).natAbs.gcd q.den = 1 :=
  q.reduced ▸ Int.gcd_add_mul_right_left _ _ _

theorem den_add_int (q : ℚ) (z : ℤ) : (q + z).den = q.den := by
  simp [den_add, num_add_int_gcd_den_eq_one]

theorem num_add_int (q : ℚ) (z : ℤ) : (q + z).num = q.num + z * q.den := by
  simp [num_add, num_add_int_gcd_den_eq_one]

theorem den_eq_den_of_den_add_eq_one {q r : ℚ} (h : (q + r).den = 1) : q.den = r.den := by
  rw [← add_sub_cancel_right q r, sub_eq_add_neg, ← (den_eq_one_iff _).mp h, add_comm, den_add_int,
  den_neg_eq_den]

theorem isSquare_iff {q : ℚ} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den := by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num, mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    refine ⟨nr / dr, ?_⟩
    rw [div_mul_div_comm, ← Int.cast_mul, ← Nat.cast_mul, ← hnr, ← hdr, num_div_den]

@[norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℚ) ↔ IsSquare n := by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true, Int.isSquare_natCast_iff]

@[norm_cast, simp]
theorem isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z := by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp]
theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℚ) ↔ IsSquare (OfNat.ofNat n : ℕ) :=
  isSquare_natCast_iff

theorem mkRat_add_mkRat_of_den (n₁ n₂ : Int) {d : Nat} (h : d ≠ 0) :
    mkRat n₁ d + mkRat n₂ d = mkRat (n₁ + n₂) d := by
  rw [mkRat_add_mkRat _ _ h h, ← add_mul, mkRat_mul_right h]

section Casts

theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den :=
  haveI : (n : ℚ) / d = Rat.divInt n d := by rw [← Rat.divInt_eq_div]
  Rat.num_den_mk d_ne_zero this

theorem mul_num_den' (q r : ℚ) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  let s := q.num * r.num /. (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_den⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_den (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 1 [c_mul_den]
  rw [Int.mul_assoc, Int.mul_assoc, mul_eq_mul_left_iff, or_iff_not_imp_right]
  intro
  have h : _ = s := divInt_mul_divInt q.num r.num
  rw [num_divInt_den, num_divInt_den] at h
  rw [h, mul_comm, ← Rat.eq_iff_mul_eq_mul, ← divInt_eq_div]

theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  let s := divInt (q.num * r.den + r.num * q.den) (q.den * r.den : ℤ)
  have hs : (q.den * r.den : ℤ) ≠ 0 := Int.natCast_ne_zero_iff_pos.mpr (Nat.mul_pos q.pos r.pos)
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

theorem substr_num_den' (q r : ℚ) :
    (q - r).num * q.den * r.den = (q.num * r.den - r.num * q.den) * (q - r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← den_neg_eq_den r,
    add_num_den' q (-r)]

end Casts

protected theorem inv_neg (q : ℚ) : (-q)⁻¹ = -q⁻¹ := by
  rw [← num_divInt_den q]
  simp only [Rat.neg_divInt, Rat.inv_divInt, Rat.divInt_neg]

theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    (a / b : ℚ).num = a := by
  lift b to ℕ using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div, ← mk_eq_divInt _ _ hb0.ne' h]

theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).den : ℤ) = b := by
  lift b to ℕ using hb0.le
  simp only [Int.natAbs_natCast, Int.natCast_pos] at h hb0
  rw [← Rat.divInt_eq_div, ← mk_eq_divInt _ _ hb0.ne' h]

theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]
theorem intCast_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n := by
  by_cases hn : n = 0
  · subst hn
    simp only [Int.cast_zero, zero_div, Int.ediv_zero]
  · have : (n : ℚ) ≠ 0 := by rwa [← coe_int_inj] at hn
    simp only [Int.ediv_self hn, Int.cast_one, div_self this]

@[norm_cast]
theorem natCast_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  intCast_div_self n

theorem intCast_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  rw [mul_comm b, Int.mul_ediv_assoc c (dvd_refl b), Int.cast_mul,
    intCast_div_self, Int.cast_mul, mul_div_assoc]

theorem natCast_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b :=
  intCast_div a b (Int.ofNat_dvd.mpr h)

theorem den_div_intCast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m := by
  replace hn : (n : ℚ) ≠ 0 := num_ne_zero.mp hn
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff hn]
    exact mod_cast (Dvd.intro_left _)
  · exact (intCast_div _ _ · ▸ rfl)

theorem den_div_natCast_eq_one_iff (m n : ℕ) (hn : n ≠ 0) : ((m : ℚ) / n).den = 1 ↔ n ∣ m :=
  (den_div_intCast_eq_one_iff m n (Int.ofNat_ne_zero.mpr hn)).trans Int.ofNat_dvd

theorem inv_intCast_num_of_pos {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 := by
  simp [*]

theorem inv_natCast_num_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_intCast_num_of_pos (mod_cast ha0 : 0 < (a : ℤ))

theorem inv_intCast_den_of_pos {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.den : ℤ) = a := by
  rw [← ofInt_eq_cast, ofInt, mk_eq_divInt, Rat.inv_divInt, divInt_eq_div, Nat.cast_one]
  apply den_div_eq_of_coprime ha0
  rw [Int.natAbs_one]
  exact Nat.coprime_one_left _

theorem inv_natCast_den_of_pos {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.den = a := by
  rw [← Int.ofNat_inj, ← Int.cast_natCast a, inv_intCast_den_of_pos]
  rwa [Int.natCast_pos]

theorem inv_intCast_num (a : ℤ) : (a : ℚ)⁻¹.num = Int.sign a := by simp

theorem inv_natCast_num (a : ℕ) : (a : ℚ)⁻¹.num = Int.sign a := by simp

theorem inv_ofNat_num (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.num = 1 := by
  -- This proof is quite unpleasant: golf / find better simp lemmas?
  have : 2 ≤ a := Nat.AtLeastTwo.prop
  simp only [num_inv, num_ofNat, den_ofNat, Nat.cast_one, mul_one, Int.sign_eq_one_iff_pos,
    gt_iff_lt]
  change 0 < (a : ℤ)
  cutsat

theorem inv_intCast_den (a : ℤ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a.natAbs := by simp

theorem inv_natCast_den (a : ℕ) : (a : ℚ)⁻¹.den = if a = 0 then 1 else a := by simp

theorem inv_ofNat_den (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.den = OfNat.ofNat a := by
  simp [den_inv, Int.natAbs_eq_iff]

theorem den_inv_of_ne_zero {q : ℚ} (hq : q ≠ 0) : (q⁻¹).den = q.num.natAbs := by
  simp [*]

protected theorem «forall» {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, b ≠ 0 → p (a / b) where
  mp h _ _ _ := h _
  mpr h q := by simpa [num_div_den] using h q.num q.den (mod_cast q.den_ne_zero)

protected theorem «exists» {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, b ≠ 0 ∧ p (a / b) := by
  simpa using Rat.forall (p := (¬ p ·)).not

/-!
### Denominator as `ℕ+`
-/


section PNatDen

/-- Denominator as `ℕ+`. -/
def pnatDen (x : ℚ) : ℕ+ :=
  ⟨x.den, x.pos⟩

@[simp]
theorem coe_pnatDen (x : ℚ) : (x.pnatDen : ℕ) = x.den :=
  rfl

theorem pnatDen_eq_iff_den_eq {x : ℚ} {n : ℕ+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff

@[simp]
theorem pnatDen_one : (1 : ℚ).pnatDen = 1 :=
  rfl

@[simp]
theorem pnatDen_zero : (0 : ℚ).pnatDen = 1 :=
  rfl

end PNatDen

end Rat
