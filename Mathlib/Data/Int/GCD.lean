/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.int.gcd
! leanprover-community/mathlib commit 47a1a73351de8dd6c8d3d32b569c8e434b03ca47
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.NormNum

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcd_a x y` and `gcd_b x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcd_a x y + y * gcd_b x y`.

## Tags

Bézout's lemma, Bezout's lemma
-/


/-! ### Extended Euclidean algorithm -/


namespace Nat

/-- Helper function for the extended GCD algorithm (`Nat.xgcd`). -/
def xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
  | 0, _, _, r', s', t' => (r', s', t')
  | succ k, s, t, r', s', t' =>
    have : r' % succ k < succ k := mod_lt _ <| (succ_pos _).gt
    let q := r' / succ k
    xgcdAux (r' % succ k) (s' - q * s) (t' - q * t) (succ k) s t
#align nat.xgcd_aux Nat.xgcdAux

-- porting note: these are not in mathlib3; these equation lemmas are to fix
-- complaints by the Lean 4 `unusedHavesSuffices` linter obtained when `simp [xgcdAux]` is used.
theorem xgcdAux_zero : xgcdAux 0 s t r' s' t' = (r', s', t') := rfl

theorem xgcdAux_succ : xgcdAux (succ k) s t r' s' t' =
  xgcdAux (r' % succ k) (s' - (r' / succ k) * s) (t' - (r' / succ k) * t) (succ k) s t := rfl

@[simp]
theorem xgcd_zero_left {s t r' s' t'} : xgcdAux 0 s t r' s' t' = (r', s', t') := by simp [xgcdAux]
#align nat.xgcd_zero_left Nat.xgcd_zero_left

theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rfl
#align nat.xgcd_aux_rec Nat.xgcd_aux_rec

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ :=
  (xgcdAux x 1 0 y 0 1).2
#align nat.xgcd Nat.xgcd

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : ℕ) : ℤ :=
  (xgcd x y).1
#align nat.gcd_a Nat.gcdA

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : ℕ) : ℤ :=
  (xgcd x y).2
#align nat.gcd_b Nat.gcdB

@[simp]
theorem gcdA_zero_left {s : ℕ} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]
#align nat.gcd_a_zero_left Nat.gcdA_zero_left

@[simp]
theorem gcdB_zero_left {s : ℕ} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]
#align nat.gcd_b_zero_left Nat.gcdB_zero_left

@[simp]
theorem gcdA_zero_right {s : ℕ} (h : s ≠ 0) : gcdA s 0 = 1 := by
  unfold gcdA xgcd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  -- Porting note: `simp [xgcdAux_succ]` crashes Lean here
  rw [xgcdAux_succ]
  rfl
#align nat.gcd_a_zero_right Nat.gcdA_zero_right

@[simp]
theorem gcdB_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by
  unfold gcdB xgcd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  -- Porting note: `simp [xgcdAux_succ]` crashes Lean here
  rw [xgcdAux_succ]
  rfl
#align nat.gcd_b_zero_right Nat.gcdB_zero_right

@[simp]
theorem xgcd_aux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp [xgcd_aux_rec, h, IH]
    rw [← gcd_rec]
#align nat.xgcd_aux_fst Nat.xgcd_aux_fst

theorem xgcd_aux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]
#align nat.xgcd_aux_val Nat.xgcd_aux_val

theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcdA gcdB; cases xgcd x y; rfl
#align nat.xgcd_val Nat.xgcd_val

section

variable (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
  | (r, s, t) => (r : ℤ) = x * s + y * t

theorem xgcd_aux_P {r r'} :
    ∀ {s t s' t'}, P x y (r, s, t) → P x y (r', s', t') → P x y (xgcdAux r s t r' s' t') := by
  induction r, r' using gcd.induction with
  | H0 => simp
  | H1 a b h IH =>
    intro s t s' t' p p'
    rw [xgcd_aux_rec h]; refine' IH _ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : ℤ) = k
    rw [p, p', mul_sub, sub_add_eq_add_sub, mul_sub, add_mul, mul_comm k t, mul_comm k s,
      ← mul_assoc, ← mul_assoc, add_comm (x * s * k), ← add_sub_assoc, sub_sub]
set_option linter.uppercaseLean3 false in
#align nat.xgcd_aux_P Nat.xgcd_aux_P

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by
  have := @xgcd_aux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcd_aux_val, xgcd_val] at this
#align nat.gcd_eq_gcd_ab Nat.gcd_eq_gcd_ab

end

theorem exists_mul_emod_eq_gcd {k n : ℕ} (hk : gcd n k < k) : ∃ m, n * m % k = gcd n k := by
  have hk' := Int.ofNat_ne_zero.2 (ne_of_gt (lt_of_le_of_lt (zero_le (gcd n k)) hk))
  have key := congr_arg (fun (m : ℤ) => (m % k).toNat) (gcd_eq_gcd_ab n k)
  simp only at key
  rw [Int.add_mul_emod_self_left, ← Int.coe_nat_mod, Int.toNat_coe_nat, mod_eq_of_lt hk] at key
  refine' ⟨(n.gcdA k % k).toNat, Eq.trans (Int.ofNat.inj _) key.symm⟩
  rw [Int.ofNat_eq_coe, Int.coe_nat_mod, Int.ofNat_mul, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'),
    Int.ofNat_eq_coe, Int.toNat_of_nonneg (Int.emod_nonneg _ hk'), Int.mul_emod, Int.emod_emod,
    ← Int.mul_emod]
#align nat.exists_mul_mod_eq_gcd Nat.exists_mul_emod_eq_gcd

theorem exists_mul_emod_eq_one_of_coprime {k n : ℕ} (hkn : coprime n k) (hk : 1 < k) :
    ∃ m, n * m % k = 1 :=
  Exists.recOn (exists_mul_emod_eq_gcd (lt_of_le_of_lt (le_of_eq hkn) hk)) fun m hm ↦
    ⟨m, hm.trans hkn⟩
#align nat.exists_mul_mod_eq_one_of_coprime Nat.exists_mul_emod_eq_one_of_coprime

end Nat

/-! ### Divisibility over ℤ -/


namespace Int

theorem gcd_def (i j : ℤ) : gcd i j = Nat.gcd i.natAbs j.natAbs := rfl

protected theorem coe_nat_gcd (m n : ℕ) : Int.gcd ↑m ↑n = Nat.gcd m n :=
  rfl
#align int.coe_nat_gcd Int.coe_nat_gcd

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA : ℤ → ℤ → ℤ
  | ofNat m, n => m.gcdA n.natAbs
  | -[m+1], n => -m.succ.gcdA n.natAbs
#align int.gcd_a Int.gcdA

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB : ℤ → ℤ → ℤ
  | m, ofNat n => m.natAbs.gcdB n
  | m, -[n+1] => -m.natAbs.gcdB n.succ
#align int.gcd_b Int.gcdB

/-- **Bézout's lemma** -/
theorem gcd_eq_gcd_ab : ∀ x y : ℤ, (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y
  | (m : ℕ), (n : ℕ) => Nat.gcd_eq_gcd_ab _ _
  | (m : ℕ), -[n+1] =>
    show (_ : ℤ) = _ + -(n + 1) * -_ by rw [neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], (n : ℕ) =>
    show (_ : ℤ) = -(m + 1) * -_ + _ by rw [neg_mul_neg]; apply Nat.gcd_eq_gcd_ab
  | -[m+1], -[n+1] =>
    show (_ : ℤ) = -(m + 1) * -_ + -(n + 1) * -_ by
      rw [neg_mul_neg, neg_mul_neg]
      apply Nat.gcd_eq_gcd_ab
#align int.gcd_eq_gcd_ab Int.gcd_eq_gcd_ab

theorem natAbs_ediv (a b : ℤ) (H : b ∣ a) : natAbs (a / b) = natAbs a / natAbs b := by
  rcases Nat.eq_zero_or_pos (natAbs b) with (h | h)
  rw [natAbs_eq_zero.1 h]
  simp [Int.ediv_zero]
  calc
    natAbs (a / b) = natAbs (a / b) * 1 := by rw [mul_one]
    _ = natAbs (a / b) * (natAbs b / natAbs b) := by rw [Nat.div_self h]
    _ = natAbs (a / b) * natAbs b / natAbs b := by rw [Nat.mul_div_assoc _ dvd_rfl]
    _ = natAbs (a / b * b) / natAbs b := by rw [natAbs_mul (a / b) b]
    _ = natAbs a / natAbs b := by rw [Int.ediv_mul_cancel H]
#align int.nat_abs_div Int.natAbs_ediv

theorem dvd_of_mul_dvd_mul_left {i j k : ℤ} (k_non_zero : k ≠ 0) (H : k * i ∣ k * j) : i ∣ j :=
  Dvd.elim H fun l H1 => by rw [mul_assoc] at H1; exact ⟨_, mul_left_cancel₀ k_non_zero H1⟩
#align int.dvd_of_mul_dvd_mul_left Int.dvd_of_mul_dvd_mul_left

theorem dvd_of_mul_dvd_mul_right {i j k : ℤ} (k_non_zero : k ≠ 0) (H : i * k ∣ j * k) : i ∣ j := by
  rw [mul_comm i k, mul_comm j k] at H; exact dvd_of_mul_dvd_mul_left k_non_zero H
#align int.dvd_of_mul_dvd_mul_right Int.dvd_of_mul_dvd_mul_right

/-- ℤ specific version of least common multiple. -/
def lcm (i j : ℤ) : ℕ :=
  Nat.lcm (natAbs i) (natAbs j)
#align int.lcm Int.lcm

theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl
#align int.lcm_def Int.lcm_def

protected theorem coe_nat_lcm (m n : ℕ) : Int.lcm ↑m ↑n = Nat.lcm m n :=
  rfl
#align int.coe_nat_lcm Int.coe_nat_lcm

theorem gcd_dvd_left (i j : ℤ) : (gcd i j : ℤ) ∣ i :=
  dvd_natAbs.mp <| coe_nat_dvd.mpr <| Nat.gcd_dvd_left _ _
#align int.gcd_dvd_left Int.gcd_dvd_left

theorem gcd_dvd_right (i j : ℤ) : (gcd i j : ℤ) ∣ j :=
  dvd_natAbs.mp <| coe_nat_dvd.mpr <| Nat.gcd_dvd_right _ _
#align int.gcd_dvd_right Int.gcd_dvd_right

theorem dvd_gcd {i j k : ℤ} (h1 : k ∣ i) (h2 : k ∣ j) : k ∣ gcd i j :=
  natAbs_dvd.1 <|
    coe_nat_dvd.2 <| Nat.dvd_gcd (natAbs_dvd_natAbs.2 h1) (natAbs_dvd_natAbs.2 h2)
#align int.dvd_gcd Int.dvd_gcd

theorem gcd_mul_lcm (i j : ℤ) : gcd i j * lcm i j = natAbs (i * j) := by
  rw [Int.gcd, Int.lcm, Nat.gcd_mul_lcm, natAbs_mul]
#align int.gcd_mul_lcm Int.gcd_mul_lcm

theorem gcd_comm (i j : ℤ) : gcd i j = gcd j i :=
  Nat.gcd_comm _ _
#align int.gcd_comm Int.gcd_comm

theorem gcd_assoc (i j k : ℤ) : gcd (gcd i j) k = gcd i (gcd j k) :=
  Nat.gcd_assoc _ _ _
#align int.gcd_assoc Int.gcd_assoc

@[simp]
theorem gcd_self (i : ℤ) : gcd i i = natAbs i := by simp [gcd]
#align int.gcd_self Int.gcd_self

@[simp]
theorem gcd_zero_left (i : ℤ) : gcd 0 i = natAbs i := by simp [gcd]
#align int.gcd_zero_left Int.gcd_zero_left

@[simp]
theorem gcd_zero_right (i : ℤ) : gcd i 0 = natAbs i := by simp [gcd]
#align int.gcd_zero_right Int.gcd_zero_right

@[simp]
theorem gcd_one_left (i : ℤ) : gcd 1 i = 1 :=
  Nat.gcd_one_left _
#align int.gcd_one_left Int.gcd_one_left

@[simp]
theorem gcd_one_right (i : ℤ) : gcd i 1 = 1 :=
  Nat.gcd_one_right _
#align int.gcd_one_right Int.gcd_one_right

@[simp]
theorem gcd_neg_right {x y : ℤ} : gcd x (-y) = gcd x y := by rw [Int.gcd, Int.gcd, natAbs_neg]
#align int.gcd_neg_right Int.gcd_neg_right

@[simp]
theorem gcd_neg_left {x y : ℤ} : gcd (-x) y = gcd x y := by rw [Int.gcd, Int.gcd, natAbs_neg]
#align int.gcd_neg_left Int.gcd_neg_left

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = natAbs i * gcd j k := by
  rw [Int.gcd, Int.gcd, natAbs_mul, natAbs_mul]
  apply Nat.gcd_mul_left
#align int.gcd_mul_left Int.gcd_mul_left

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * natAbs j := by
  rw [Int.gcd, Int.gcd, natAbs_mul, natAbs_mul]
  apply Nat.gcd_mul_right
#align int.gcd_mul_right Int.gcd_mul_right

theorem gcd_pos_of_ne_zero_left {i : ℤ} (j : ℤ) (hi : i ≠ 0) : 0 < gcd i j :=
  Nat.gcd_pos_of_pos_left _ $ natAbs_pos.2 hi
#align int.gcd_pos_of_ne_zero_left Int.gcd_pos_of_ne_zero_left

theorem gcd_pos_of_ne_zero_right (i : ℤ) {j : ℤ} (hj : j ≠ 0) : 0 < gcd i j :=
  Nat.gcd_pos_of_pos_right _ $ natAbs_pos.2 hj
#align int.gcd_pos_of_ne_zero_right Int.gcd_pos_of_ne_zero_right

theorem gcd_eq_zero_iff {i j : ℤ} : gcd i j = 0 ↔ i = 0 ∧ j = 0 := by
  rw [gcd, Nat.gcd_eq_zero_iff, natAbs_eq_zero, natAbs_eq_zero]
#align int.gcd_eq_zero_iff Int.gcd_eq_zero_iff

theorem gcd_pos_iff {i j : ℤ} : 0 < gcd i j ↔ i ≠ 0 ∨ j ≠ 0 :=
  pos_iff_ne_zero.trans <| gcd_eq_zero_iff.not.trans not_and_or
#align int.gcd_pos_iff Int.gcd_pos_iff

theorem gcd_div {i j k : ℤ} (H1 : k ∣ i) (H2 : k ∣ j) :
    gcd (i / k) (j / k) = gcd i j / natAbs k := by
  rw [gcd, natAbs_ediv i k H1, natAbs_ediv j k H2]
  exact Nat.gcd_div (natAbs_dvd_natAbs.mpr H1) (natAbs_dvd_natAbs.mpr H2)
#align int.gcd_div Int.gcd_div

theorem gcd_div_gcd_div_gcd {i j : ℤ} (H : 0 < gcd i j) : gcd (i / gcd i j) (j / gcd i j) = 1 := by
  rw [gcd_div (gcd_dvd_left i j) (gcd_dvd_right i j), natAbs_ofNat, Nat.div_self H]
#align int.gcd_div_gcd_div_gcd Int.gcd_div_gcd_div_gcd

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
  Int.coe_nat_dvd.1 <| dvd_gcd ((gcd_dvd_left i j).trans H) (gcd_dvd_right i j)
#align int.gcd_dvd_gcd_of_dvd_left Int.gcd_dvd_gcd_of_dvd_left

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
  Int.coe_nat_dvd.1 <| dvd_gcd (gcd_dvd_left j i) ((gcd_dvd_right j i).trans H)
#align int.gcd_dvd_gcd_of_dvd_right Int.gcd_dvd_gcd_of_dvd_right

theorem gcd_dvd_gcd_mul_left (i j k : ℤ) : gcd i j ∣ gcd (k * i) j :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_left _ _)
#align int.gcd_dvd_gcd_mul_left Int.gcd_dvd_gcd_mul_left

theorem gcd_dvd_gcd_mul_right (i j k : ℤ) : gcd i j ∣ gcd (i * k) j :=
  gcd_dvd_gcd_of_dvd_left _ (dvd_mul_right _ _)
#align int.gcd_dvd_gcd_mul_right Int.gcd_dvd_gcd_mul_right

theorem gcd_dvd_gcd_mul_left_right (i j k : ℤ) : gcd i j ∣ gcd i (k * j) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_left _ _)
#align int.gcd_dvd_gcd_mul_left_right Int.gcd_dvd_gcd_mul_left_right

theorem gcd_dvd_gcd_mul_right_right (i j k : ℤ) : gcd i j ∣ gcd i (j * k) :=
  gcd_dvd_gcd_of_dvd_right _ (dvd_mul_right _ _)
#align int.gcd_dvd_gcd_mul_right_right Int.gcd_dvd_gcd_mul_right_right

theorem gcd_eq_left {i j : ℤ} (H : i ∣ j) : gcd i j = natAbs i :=
  Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd dvd_rfl (natAbs_dvd_natAbs.mpr H))
#align int.gcd_eq_left Int.gcd_eq_left

theorem gcd_eq_right {i j : ℤ} (H : j ∣ i) : gcd i j = natAbs j := by rw [gcd_comm, gcd_eq_left H]
#align int.gcd_eq_right Int.gcd_eq_right

theorem ne_zero_of_gcd {x y : ℤ} (hc : gcd x y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  contrapose! hc
  rw [hc.left, hc.right, gcd_zero_right, natAbs_zero]
#align int.ne_zero_of_gcd Int.ne_zero_of_gcd

theorem exists_gcd_one {m n : ℤ} (H : 0 < gcd m n) :
    ∃ m' n' : ℤ, gcd m' n' = 1 ∧ m = m' * gcd m n ∧ n = n' * gcd m n :=
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel (gcd_dvd_left m n)).symm,
    (Int.ediv_mul_cancel (gcd_dvd_right m n)).symm⟩
#align int.exists_gcd_one Int.exists_gcd_one

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ)(m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_gcd_one H
  ⟨_, m', n', H, h⟩
#align int.exists_gcd_one' Int.exists_gcd_one'

theorem pow_dvd_pow_iff {m n : ℤ} {k : ℕ} (k0 : 0 < k) : m ^ k ∣ n ^ k ↔ m ∣ n := by
  refine' ⟨fun h => _, fun h => pow_dvd_pow_of_dvd h _⟩
  rwa [← natAbs_dvd_natAbs, ← Nat.pow_dvd_pow_iff k0, ← Int.natAbs_pow, ← Int.natAbs_pow,
    natAbs_dvd_natAbs]
#align int.pow_dvd_pow_iff Int.pow_dvd_pow_iff

theorem gcd_dvd_iff {a b : ℤ} {n : ℕ} : gcd a b ∣ n ↔ ∃ x y : ℤ, ↑n = a * x + b * y := by
  constructor
  · intro h
    rw [← Nat.mul_div_cancel' h, Int.ofNat_mul, gcd_eq_gcd_ab, add_mul, mul_assoc, mul_assoc]
    exact ⟨_, _, rfl⟩
  · rintro ⟨x, y, h⟩
    rw [← Int.coe_nat_dvd, h]
    exact
      dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) _) (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)
#align int.gcd_dvd_iff Int.gcd_dvd_iff

theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (ofNat_zero_le (gcd a b)) (dvd_gcd hda hdb)
    (hd _ (gcd_dvd_left a b) (gcd_dvd_right a b))
#align int.gcd_greatest Int.gcd_greatest

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a c = 1` then `a ∣ b`.
Compare with `IsCoprime.dvd_of_dvd_mul_left` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_left_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a c = 1) :
    a ∣ b := by
  have := gcd_eq_gcd_ab a c
  simp only [hab, Int.ofNat_zero, Int.ofNat_succ, zero_add] at this
  have : b * a * gcdA a c + b * c * gcdB a c = b := by simp [mul_assoc, ← mul_add, ← this]
  rw [← this]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left a b) _) (dvd_mul_of_dvd_left habc _)
#align int.dvd_of_dvd_mul_left_of_gcd_one Int.dvd_of_dvd_mul_left_of_gcd_one

/-- Euclid's lemma: if `a ∣ b * c` and `gcd a b = 1` then `a ∣ c`.
Compare with `IsCoprime.dvd_of_dvd_mul_right` and
`UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors` -/
theorem dvd_of_dvd_mul_right_of_gcd_one {a b c : ℤ} (habc : a ∣ b * c) (hab : gcd a b = 1) :
    a ∣ c := by
  rw [mul_comm] at habc
  exact dvd_of_dvd_mul_left_of_gcd_one habc hab
#align int.dvd_of_dvd_mul_right_of_gcd_one Int.dvd_of_dvd_mul_right_of_gcd_one

/-- For nonzero integers `a` and `b`, `gcd a b` is the smallest positive natural number that can be
written in the form `a * x + b * y` for some pair of integers `x` and `y` -/
theorem gcd_least_linear {a b : ℤ} (ha : a ≠ 0) :
    IsLeast { n : ℕ | 0 < n ∧ ∃ x y : ℤ, ↑n = a * x + b * y } (a.gcd b) := by
  simp_rw [← gcd_dvd_iff]
  constructor
  · simpa [and_true_iff, dvd_refl, Set.mem_setOf_eq] using gcd_pos_of_ne_zero_left b ha
  · simp only [lowerBounds, and_imp, Set.mem_setOf_eq]
    exact fun n hn_pos hn => Nat.le_of_dvd hn_pos hn
#align int.gcd_least_linear Int.gcd_least_linear

/-! ### lcm -/


theorem lcm_comm (i j : ℤ) : lcm i j = lcm j i := by
  rw [Int.lcm, Int.lcm]
  exact Nat.lcm_comm _ _
#align int.lcm_comm Int.lcm_comm

theorem lcm_assoc (i j k : ℤ) : lcm (lcm i j) k = lcm i (lcm j k) := by
  rw [Int.lcm, Int.lcm, Int.lcm, Int.lcm, natAbs_ofNat, natAbs_ofNat]
  apply Nat.lcm_assoc
#align int.lcm_assoc Int.lcm_assoc

@[simp]
theorem lcm_zero_left (i : ℤ) : lcm 0 i = 0 := by
  rw [Int.lcm]
  apply Nat.lcm_zero_left
#align int.lcm_zero_left Int.lcm_zero_left

@[simp]
theorem lcm_zero_right (i : ℤ) : lcm i 0 = 0 := by
  rw [Int.lcm]
  apply Nat.lcm_zero_right
#align int.lcm_zero_right Int.lcm_zero_right

@[simp]
theorem lcm_one_left (i : ℤ) : lcm 1 i = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_one_left
#align int.lcm_one_left Int.lcm_one_left

@[simp]
theorem lcm_one_right (i : ℤ) : lcm i 1 = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_one_right
#align int.lcm_one_right Int.lcm_one_right

@[simp]
theorem lcm_self (i : ℤ) : lcm i i = natAbs i := by
  rw [Int.lcm]
  apply Nat.lcm_self
#align int.lcm_self Int.lcm_self

theorem dvd_lcm_left (i j : ℤ) : i ∣ lcm i j := by
  rw [Int.lcm]
  apply coe_nat_dvd_right.mpr
  apply Nat.dvd_lcm_left
#align int.dvd_lcm_left Int.dvd_lcm_left

theorem dvd_lcm_right (i j : ℤ) : j ∣ lcm i j := by
  rw [Int.lcm]
  apply coe_nat_dvd_right.mpr
  apply Nat.dvd_lcm_right
#align int.dvd_lcm_right Int.dvd_lcm_right

theorem lcm_dvd {i j k : ℤ} : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k := by
  rw [Int.lcm]
  intro hi hj
  exact coe_nat_dvd_left.mpr (Nat.lcm_dvd (natAbs_dvd_natAbs.mpr hi) (natAbs_dvd_natAbs.mpr hj))
#align int.lcm_dvd Int.lcm_dvd

end Int

@[to_additive gcd_nsmul_eq_zero]
theorem pow_gcd_eq_one {M : Type _} [Monoid M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
    x ^ m.gcd n = 1 := by
  rcases m with (rfl | m); · simp [hn]
  obtain ⟨y, rfl⟩ := isUnit_ofPowEqOne hm m.succ_ne_zero
  simp only [← Units.val_pow_eq_pow_val] at *
  rw [← Units.val_one, ← zpow_coe_nat, ← Units.ext_iff] at *
  simp only [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, hm, hn, one_zpow, one_mul]
#align pow_gcd_eq_one pow_gcd_eq_one
#align gcd_nsmul_eq_zero gcd_nsmul_eq_zero

/-! ### GCD prover -/

namespace Tactic

namespace NormNum

theorem int_gcd_helper' {d : ℕ} {x y a b : ℤ} (h₁ : (d : ℤ) ∣ x) (h₂ : (d : ℤ) ∣ y)
    (h₃ : x * a + y * b = d) : Int.gcd x y = d := by
  refine' Nat.dvd_antisymm _ (Int.coe_nat_dvd.1 (Int.dvd_gcd h₁ h₂))
  rw [← Int.coe_nat_dvd, ← h₃]
  apply dvd_add
  · exact (Int.gcd_dvd_left _ _).mul_right _
  · exact (Int.gcd_dvd_right _ _).mul_right _
#align tactic.norm_num.int_gcd_helper' Tactic.NormNum.int_gcd_helper'

theorem nat_gcd_helper_dvd_left (x y a : ℕ) (h : x * a = y) : Nat.gcd x y = x :=
  Nat.gcd_eq_left ⟨a, h.symm⟩
#align tactic.norm_num.nat_gcd_helper_dvd_left Tactic.NormNum.nat_gcd_helper_dvd_left

theorem nat_gcd_helper_dvd_right (x y a : ℕ) (h : y * a = x) : Nat.gcd x y = y :=
  Nat.gcd_eq_right ⟨a, h.symm⟩
#align tactic.norm_num.nat_gcd_helper_dvd_right Tactic.NormNum.nat_gcd_helper_dvd_right

theorem nat_gcd_helper_2 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
    (hx : x * a = tx) (hy : y * b = ty) (h : ty + d = tx) : Nat.gcd x y = d := by
  rw [← Int.coe_nat_gcd];
  apply
    @int_gcd_helper' _ _ _ a (-b) (Int.coe_nat_dvd.2 ⟨_, hu.symm⟩) (Int.coe_nat_dvd.2
     ⟨_, hv.symm⟩)
  rw [mul_neg, ← sub_eq_add_neg, sub_eq_iff_eq_add']
  norm_cast; rw [hx, hy, h]
#align tactic.norm_num.nat_gcd_helper_2 Tactic.NormNum.nat_gcd_helper_2

theorem nat_gcd_helper_1 (d x y a b u v tx ty : ℕ) (hu : d * u = x) (hv : d * v = y)
    (hx : x * a = tx) (hy : y * b = ty) (h : tx + d = ty) : Nat.gcd x y = d :=
  (Nat.gcd_comm _ _).trans <| nat_gcd_helper_2 _ _ _ _ _ _ _ _ _ hv hu hy hx h
#align tactic.norm_num.nat_gcd_helper_1 Tactic.NormNum.nat_gcd_helper_1

--Porting note: the `simp only` was not necessary in Lean3.
theorem nat_lcm_helper (x y d m n : ℕ) (hd : Nat.gcd x y = d) (d0 : 0 < d) (xy : x * y = n)
    (dm : d * m = n) : Nat.lcm x y = m :=
  mul_right_injective₀ d0.ne' <| by simp only; rw [dm, ← xy, ← hd, Nat.gcd_mul_lcm]
#align tactic.norm_num.nat_lcm_helper Tactic.NormNum.nat_lcm_helper

theorem not_coprime_helper {x y d : Nat} (h : Nat.gcd x y = d) (h' : Nat.beq d 1 = false) :
    ¬ Nat.coprime x y :=
  by cases h; exact fun h'' => Nat.ne_of_beq_eq_false h' (Nat.coprime_iff_gcd_eq_one.mp h'')

theorem int_gcd_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.gcd x' y' = d) :
    Int.gcd x y = d := by subst_vars; rw [Int.gcd_def]

theorem int_lcm_helper {x y : ℤ} {x' y' d : ℕ}
    (hx : x.natAbs = x') (hy : y.natAbs = y') (h : Nat.lcm x' y' = d) :
    Int.lcm x y = d := by subst_vars; rw [Int.lcm_def]

#noalign tactic.norm_num.nat_coprime_helper_zero_left
#noalign tactic.norm_num.nat_coprime_helper_zero_right
#noalign tactic.norm_num.nat_coprime_helper_1
#noalign tactic.norm_num.nat_coprime_helper_2
#noalign tactic.norm_num.nat_not_coprime_helper
#noalign tactic.norm_num.int_gcd_helper''
#noalign tactic.norm_num.int_gcd_helper_neg_left
#noalign tactic.norm_num.int_gcd_helper_neg_right
#noalign tactic.norm_num.int_lcm_helper
#noalign tactic.norm_num.int_lcm_helper_neg_left
#noalign tactic.norm_num.int_lcm_helper_neg_right

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

theorem isNat_gcd : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.gcd nx ny = z → IsNat (Nat.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isNat_lcm : {x y nx ny z : ℕ} →
    IsNat x nx → IsNat y ny → Nat.lcm nx ny = z → IsNat (Nat.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isNat_coprime : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → Nat.coprime nx ny → Nat.coprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isNat_not_coprime : {x y nx ny : ℕ} →
    IsNat x nx → IsNat y ny → ¬ Nat.coprime nx ny → ¬ Nat.coprime x y
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => h

theorem isInt_gcd : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.gcd nx ny = z → IsNat (Int.gcd x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

theorem isInt_lcm : {x y nx ny : ℤ} → {z : ℕ} →
    IsInt x nx → IsInt y ny → Int.lcm nx ny = z → IsNat (Int.lcm x y) z
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨rfl⟩

/-- Supporting definition for `proveNatGCD`. Returns the GCD and an equality proof. -/
def proveNatGCD' (x y : ℕ) : ((d : ℕ) × Q(Nat.gcd $x $y = $d)) :=
  match x, y with
  | 0, y => ⟨y, q(Nat.gcd_zero_left $y)⟩
  | x, 0 => ⟨x, q(Nat.gcd_zero_right $x)⟩
  | 1, y => ⟨1, q(Nat.gcd_one_left $y)⟩
  | x, 1 => ⟨1, q(Nat.gcd_one_right $x)⟩
  | x, y =>
    let (d, a, b) := Nat.xgcdAux x 1 0 y 0 1
    if d = x then
      have q : ℕ := y / x
      have pq : Q(Nat.mul $x $q = $y) := (q(Eq.refl $y) : Expr)
      ⟨x, q(nat_gcd_helper_dvd_left $x $y $q $pq)⟩
    else if d = y then
      have q : ℕ := x / y
      have pq : Q(Nat.mul $y $q = $x) := (q(Eq.refl $x) : Expr)
      ⟨y, q(nat_gcd_helper_dvd_right $x $y $q $pq)⟩
    else
      have a' : ℕ := a.natAbs
      have b' : ℕ := b.natAbs
      have u : ℕ := x / d
      have v : ℕ := y / d
      have pu : Q(Nat.mul $d $u = $x) := (q(Eq.refl $x) : Expr)
      have pv : Q(Nat.mul $d $v = $y) := (q(Eq.refl $y) : Expr)
      have tx : ℕ := x * a'
      have ty : ℕ := y * b'
      have px : Q(Nat.mul $x $a' = $tx) := (q(Eq.refl $tx) : Expr)
      have py : Q(Nat.mul $y $b' = $ty) := (q(Eq.refl $ty) : Expr)
      if a ≥ 0 then
        have pt : Q(Nat.add $ty $d = $tx) := (q(Eq.refl $tx) : Expr)
        ⟨d, q(nat_gcd_helper_2 $d $x $y $a' $b' $u $v $tx $ty $pu $pv $px $py $pt)⟩
      else
        have pt : Q(Nat.add $tx $d = $ty) := (q(Eq.refl $ty) : Expr)
        ⟨d, q(nat_gcd_helper_1 $d $x $y $a' $b' $u $v $tx $ty $pu $pv $px $py $pt)⟩

/-- Given natural number literals `nx` and `ny`, return their GCD as a natural number literal
and an equality proof. -/
def proveNatGCD (nx ny : Q(ℕ)) : Option ((d : Q(ℕ)) × Q(Nat.gcd $nx $ny = $d)) := do
  let x ← nx.natLit?
  let y ← ny.natLit?
  let ⟨c, pf⟩ := proveNatGCD' x y
  return ⟨mkRawNatLit c, pf⟩
#align tactic.norm_num.prove_gcd_nat Tactic.NormNum.proveNatGCD

@[norm_num Nat.gcd _ _]
def evalNatGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nx, p⟩ ← deriveNat x sℕ
  let ⟨ny, q⟩ ← deriveNat y sℕ
  let ⟨cd, pf⟩ ← proveNatGCD nx ny
  let pf' : Q(IsNat (Nat.gcd $x $y) $cd) := q(isNat_gcd $p $q $pf)
  return .isNat sℕ cd pf'

/-- Supporting definition for `proveNatLCM`. Returns the LCM and an equality proof. -/
def proveNatLCM' (x y : ℕ) : ((d : ℕ) × Q(Nat.lcm $x $y = $d)) :=
  match x, y with
  | 0, y => ⟨0, q(Nat.lcm_zero_left $y)⟩
  | x, 0 => ⟨0, q(Nat.lcm_zero_right $x)⟩
  | 1, y => ⟨y, q(Nat.lcm_one_left $y)⟩
  | x, 1 => ⟨x, q(Nat.lcm_one_right $x)⟩
  | x, y =>
    let ⟨d, pd⟩ := proveNatGCD' x y
    have p0 : Q(Nat.blt 0 $d = true) := (q(Eq.refl true) : Expr)
    have n : ℕ := x * y
    have pxy : Q(Nat.mul $x $y = $n) := (q(Eq.refl $n) : Expr)
    have m : ℕ := x * y / d
    have pm : Q(Nat.mul $d $m = $n) := (q(Eq.refl $n) : Expr)
    ⟨m, q(nat_lcm_helper $x $y $d $m $n $pd (Eq.mp Nat.blt_eq $p0) $pxy $pm)⟩

/-- Given natural number literals `nx` and `ny`, return their GCD as a natural number literal
and an equality proof. -/
def proveNatLCM (nx ny : Q(ℕ)) : Option ((d : Q(ℕ)) × Q(Nat.lcm $nx $ny = $d)) := do
  let x ← nx.natLit?
  let y ← ny.natLit?
  let ⟨c, pf⟩ := proveNatLCM' x y
  return ⟨mkRawNatLit c, pf⟩
#align tactic.norm_num.prove_lcm_nat Tactic.NormNum.proveNatLCM

/-- Evaluates the `Nat.lcm` function. -/
@[norm_num Nat.lcm _ _]
def evalNatLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nx, p⟩ ← deriveNat x sℕ
  let ⟨ny, q⟩ ← deriveNat y sℕ
  let ⟨cd, pf⟩ ← proveNatLCM nx ny
  let pf' : Q(IsNat (Nat.lcm $x $y) $cd) := q(isNat_lcm $p $q $pf)
  return .isNat sℕ cd pf'

/-- Helper for `proveNatCoprime`. Evaluates `Nat.coprime` given the given natural numbers. -/
def proveNatCoprime' (x y : ℕ) : Q(Nat.coprime $x $y) ⊕ Q(¬ Nat.coprime $x $y) :=
  let ⟨cd, pf⟩ := proveNatGCD' x y
  match cd with
  | 1 => Sum.inl q(Nat.coprime_iff_gcd_eq_one.mpr $pf)
  | cd =>
    have cdne : Q(Nat.beq $cd 1 = false) := (q(Eq.refl false) : Expr)
    Sum.inr q(not_coprime_helper $pf $cdne)

/-- Evaluates `Nat.coprime` for the given natural number literals. -/
def proveNatCoprime (nx ny : Q(ℕ)) : Option (Q(Nat.coprime $nx $ny) ⊕ Q(¬ Nat.coprime $nx $ny)) := do
  let x ← nx.natLit?
  let y ← ny.natLit?
  return proveNatCoprime' x y
#align tactic.norm_num.prove_coprime_nat Tactic.NormNum.proveNatCoprime

/-- Evaluates the `Nat.coprime` function. -/
@[norm_num Nat.coprime _ _]
def evalNatCoprime : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℕ))) (y : Q(ℕ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nx, p⟩ ← deriveNat x sℕ
  let ⟨ny, q⟩ ← deriveNat y sℕ
  match ← proveNatCoprime nx ny with
  | .inl pf =>
    have pf' : Q(Nat.coprime $x $y) := q(isNat_coprime $p $q $pf)
    return .isTrue pf'
  | .inr pf =>
    have pf' : Q(¬ Nat.coprime $x $y) := q(isNat_not_coprime $p $q $pf)
    return .isFalse pf'

/-- Given two integers, return their GCD and an equality proof. -/
def proveIntGCD' (x y : ℤ) : (d : ℕ) × Q(Int.gcd $x $y = $d) :=
  let x' : ℕ := x.natAbs
  let y' : ℕ := y.natAbs
  have hx : Q(($x).natAbs = $x') := (q(Eq.refl $x') : Expr)
  have hy : Q(($y).natAbs = $y') := (q(Eq.refl $y') : Expr)
  let ⟨d, pf⟩ := proveNatGCD' x.natAbs y.natAbs
  have pf' : Q(Int.gcd $x $y = $d) := q(int_gcd_helper $hx $hy $pf)
  ⟨d, pf'⟩
#align tactic.norm_num.prove_gcd_int Tactic.NormNum.proveIntGCD'

/-- Evaluates the `Int.gcd` function. -/
@[norm_num Int.gcd _ _]
def evalIntGCD : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let sℤ : Q(Ring ℤ) := q(Int.instRingInt)
  let ⟨cx, nx, p⟩ ← (← derive x).toInt
  let ⟨cy, ny, q⟩ ← (← derive y).toInt
  let ⟨cd, pf⟩ := proveIntGCD' cx cy
  have pf : Q(Int.gcd $nx $ny = $cd) := pf
  have pf' : Q(IsNat (Int.gcd $x $y) $cd) := q(isInt_gcd $p $q $pf)
  return .isNat sℕ (mkRawNatLit cd) pf'

/-- Given two integers numbers, return their LCM and an equality proof. -/
def proveIntLCM' (x y : ℤ) : (d : ℕ) × Q(Int.lcm $x $y = $d) :=
  let x' : ℕ := x.natAbs
  let y' : ℕ := y.natAbs
  have hx : Q(($x).natAbs = $x') := (q(Eq.refl $x') : Expr)
  have hy : Q(($y).natAbs = $y') := (q(Eq.refl $y') : Expr)
  let ⟨d, pf⟩ := proveNatLCM' x.natAbs y.natAbs
  have pf' : Q(Int.lcm $x $y = $d) := q(int_lcm_helper $hx $hy $pf)
  ⟨d, pf'⟩
#align tactic.norm_num.prove_lcm_int Tactic.NormNum.proveIntLCM'

/-- Evaluates the `Int.lcm` function. -/
@[norm_num Int.lcm _ _]
def evalIntLCM : NormNumExt where eval {u α} e := do
  let .app (.app _ (x : Q(ℤ))) (y : Q(ℤ)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let sℤ : Q(Ring ℤ) := q(Int.instRingInt)
  let ⟨cx, nx, p⟩ ← (← derive x).toInt
  let ⟨cy, ny, q⟩ ← (← derive y).toInt
  let ⟨cd, pf⟩ := proveIntLCM' cx cy
  have pf : Q(Int.lcm $nx $ny = $cd) := pf
  have pf' : Q(IsNat (Int.lcm $x $y) $cd) := q(isInt_lcm $p $q $pf)
  return .isNat sℕ (mkRawNatLit cd) pf'

#noalign tactic.norm_num.eval_gcd

end NormNum

end Tactic
