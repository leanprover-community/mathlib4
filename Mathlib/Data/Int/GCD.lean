/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Semiconj
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.Data.Set.Operations
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Int.Basic
import Batteries.Data.Nat.Gcd
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcdA x y` and `gcdB x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcdA x y + y * gcdB x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/

/-! ### Extended Euclidean algorithm -/


namespace Nat

/-- Helper function for the extended GCD algorithm (`Nat.xgcd`). -/
def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
  | 0, _, _, r', s', t' => (r', s', t')
  | succ k, s, t, r', s', t' =>
    let q := r' / succ k
    xgcdAux (r' % succ k) (s' - q * s) (t' - q * t) (succ k) s t
termination_by k => k
decreasing_by exact mod_lt _ <| (succ_pos _).gt

@[simp]
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := by simp [xgcdAux]

theorem xgcdAux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  simp [xgcdAux]

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ :=
  (xgcdAux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : ℕ) : ℤ :=
  (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : ℕ) : ℤ :=
  (xgcd x y).2

@[simp]
theorem gcdA_zero_left {s : ℕ} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcdB_zero_left {s : ℕ} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]

@[simp]
theorem gcdA_zero_right {s : ℕ} (h : s ≠ 0) : gcdA s 0 = 1 := by
  unfold gcdA xgcd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [xgcdAux]
  simp

@[simp]
theorem gcdB_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by
  unfold gcdB xgcd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  rw [xgcdAux]
  simp

@[simp]
theorem xgcdAux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]

theorem xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcdAux_fst x y 1 0 0 1]

theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcdA gcdB; constructor

section

variable (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
  | (r, s, t) => (r : ℤ) = x * s + y * t

theorem xgcdAux_P {r r'} :
    ∀ {s t s' t'}, P x y (r, s, t) → P x y (r', s', t') → P x y (xgcdAux r s t r' s' t') := by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcdAux_rec h]; refine IH ?_ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : ℤ) = k
    rw [p, p', Int.mul_sub, sub_add_eq_add_sub, Int.mul_sub, Int.add_mul, mul_comm k t,
      mul_comm k s, ← mul_assoc, ← mul_assoc, add_comm (x * s * k), ← add_sub_assoc, sub_sub]

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this

end

theorem exists_mul_emod_eq_gcd {k n : ℕ} (hk : gcd n k < k) : ∃ m, n * m % k = gcd n k := by
  have hk' := Int.ofNat_ne_zero.2 (ne_of_gt (lt_of_le_of_lt (zero_le (gcd n k)) hk))
  have key := congr_arg (fun (m : ℤ) => (m % k).toNat) (gcd_eq_gcd_ab n k)
  simp only at key
  rw [Int.add_mul_emod_self_left, ← Int.natCast_mod, Int.toNat_natCast, mod_eq_of_lt hk] at key
  refine ⟨(n.gcdA k % k).toNat, Eq.trans (Int.ofNat.inj ?_) key.symm⟩
  rw [Int.ofNat_eq_coe, Int.natCast_mod, Int.natCast_mul,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hk'), Int.ofNat_eq_coe,
    Int.toNat_of_nonneg (Int.emod_nonneg _ hk'), Int.mul_emod, Int.emod_emod, ← Int.mul_emod]

theorem exists_mul_emod_eq_one_of_coprime {k n : ℕ} (hkn : Coprime n k) (hk : 1 < k) :
    ∃ m, n * m % k = 1 :=
  Exists.recOn (exists_mul_emod_eq_gcd (lt_of_le_of_lt (le_of_eq hkn) hk)) fun m hm ↦
    ⟨m, hm.trans hkn⟩

end Nat

/-! ### Divisibility over ℤ -/


namespace Int

theorem gcd_def (i j : ℤ) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA : ℤ → ℤ → ℤ
  | ofNat m, n => m.gcdA n.natAbs
  | -[m+1], n => -m.succ.gcdA n.natAbs

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB : ℤ → ℤ → ℤ
  | m, ofNat n => m.natAbs.gcdB n
  | m, -[n+1] => -m.natAbs.gcdB n.succ

/-- **Bézout's lemma** -/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y
  | (m : ℕ), (n : ℕ) => Nat.gcd_eq_gcd_ab _ _
  | (m : ℕ), -[n+1] =>
    show (_ : ℤ) = _ + -(n + 1) * -_ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], (n : ℕ) =>
    show (_ : ℤ) = -(m + 1) * -_ + _ by rw [Int.neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], -[n+1] =>
    show (_ : ℤ) = -(m + 1) * -_ + -(n + 1) * -_ by
      rw [Int.neg_mul_neg, Int.neg_mul_neg]
      apply Nat.gcd_eq_gcd_ab

theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl

@[deprecated (since := "2025-04-04")] alias coe_nat_lcm := Int.lcm_natCast_natCast

alias gcd_div := gcd_ediv
alias gcd_div_gcd_div_gcd := gcd_ediv_gcd_ediv_gcd

@[deprecated (since := "2025-04-04")] alias gcd_dvd_gcd_mul_left := gcd_dvd_gcd_mul_left_left
@[deprecated (since := "2025-04-04")] alias gcd_dvd_gcd_mul_right := gcd_dvd_gcd_mul_right_left

/-- If `gcd a (m * n) = 1`, then `gcd a m = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_left {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd m = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_right_right a m n

/-- If `gcd a (m * n) = 1`, then `gcd a n = 1`. -/
theorem gcd_eq_one_of_gcd_mul_right_eq_one_right {a : ℤ} {m n : ℕ} (h : a.gcd (m * n) = 1) :
    a.gcd n = 1 :=
  Nat.dvd_one.mp <| h ▸ gcd_dvd_gcd_mul_left_right a n m

theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  contrapose! hc
  rw [hc.left, hc.right, gcd_zero_right, natAbs_zero]

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
    ∃ m' n' : ℤ, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left ..)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right ..)).symm⟩

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩

theorem gcd_dvd_iff {a b : ℤ} {n : ℕ} : gcd a b ∣ n ↔ ∃ x y : ℤ, ↑n = a * x + b * y := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h, Int.natCast_mul, gcd_eq_gcd_ab, Int.add_mul, mul_assoc, mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.natCast_dvd_natCast, h]
    exact Int.dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left ..) _)
      (dvd_mul_of_dvd_left (gcd_dvd_right ..) y)

theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (ofNat_zero_le (gcd a b)) (dvd_coe_gcd hda hdb)
    (hd _ (gcd_dvd_left ..) (gcd_dvd_right ..))

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `IsCoprime.dvd_of_dvd_mul_left` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a c = 1) :
    a ∣ b := by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.natCast_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← Int.mul_add, ← this]
  rw [← this]
  exact Int.dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b) _) (dvd_mul_of_dvd_left habc _)

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a b = 1` then `a ∣ c`.
Compare with `IsCoprime.dvd_of_dvd_mul_right` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a b = 1) :
    a ∣ c := by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab

/-- For nonzero integers `a` and `b`, `gcd a b` is the smallest positive natural number that can be
written in the form `a * x + b * y` for some pair of integers `x` and `y` -/
theorem gcd_least_linear {a b : ℤ} (ha : a ≠ 0) :
    IsLeast { n : ℕ | 0 < n ∧ ∃ x y : ℤ, ↑n = a * x + b * y } (a.gcd b) := by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true, dvd_refl, Set.mem_setOf_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_setOf_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn

end Int

@[to_additive gcd_nsmul_eq_zero]
theorem pow_gcd_eq_one {M : Type*} [Monoid M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
    x ^ m.gcd n = 1 := by
  rcases m with (rfl | m); · simp [hn]
  obtain ⟨y, rfl⟩ := IsUnit.of_pow_eq_one hm m.succ_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← Units.val_one (α := M), ← zpow_natCast, ← Units.ext_iff] at *
  rw [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, zpow_mul, hn, hm, one_zpow, one_zpow, one_mul]

variable {α : Type*}

section GroupWithZero
variable [GroupWithZero α] {a b : α} {m n : ℕ}

protected lemma Commute.pow_eq_pow_iff_of_coprime (hab : Commute a b) (hmn : m.Coprime n) :
    a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m := by
  refine ⟨fun h ↦ ?_, by rintro ⟨c, rfl, rfl⟩; rw [← pow_mul, ← pow_mul']⟩
  by_cases m = 0; · aesop
  by_cases n = 0; · aesop
  by_cases hb : b = 0; · exact ⟨0, by aesop⟩
  by_cases ha : a = 0; · exact ⟨0, by have := h.symm; aesop⟩
  refine ⟨a ^ Nat.gcdB m n * b ^ Nat.gcdA m n, ?_, ?_⟩ <;>
  · refine (pow_one _).symm.trans ?_
    conv_lhs => rw [← zpow_natCast, ← hmn, Nat.gcd_eq_gcd_ab]
    simp only [zpow_add₀ ha, zpow_add₀ hb, ← zpow_natCast, (hab.zpow_zpow₀ _ _).mul_zpow,
      ← zpow_mul, mul_comm (Nat.gcdB m n), mul_comm (Nat.gcdA m n)]
    simp only [zpow_mul, zpow_natCast, h]
    exact ((Commute.pow_pow (by aesop) _ _).zpow_zpow₀ _ _).symm

end GroupWithZero

section CommGroupWithZero
variable [CommGroupWithZero α] {a b : α} {m n : ℕ}

lemma pow_eq_pow_iff_of_coprime (hmn : m.Coprime n) : a ^ m = b ^ n ↔ ∃ c, a = c ^ n ∧ b = c ^ m :=
  (Commute.all _ _).pow_eq_pow_iff_of_coprime hmn

lemma pow_mem_range_pow_of_coprime (hmn : m.Coprime n) (a : α) :
    a ^ m ∈ Set.range (· ^ n : α → α) ↔ a ∈ Set.range (· ^ n : α → α) := by
  simp [pow_eq_pow_iff_of_coprime hmn.symm]; aesop

end CommGroupWithZero
