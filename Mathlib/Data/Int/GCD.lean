/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.GroupWithZero.Power
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Int.Dvd.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Bounds.Basic

#align_import data.int.gcd from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

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

set_option autoImplicit true


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

theorem xgcdAux_rec {r s t r' s' t'} (h : 0 < r) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  rfl
#align nat.xgcd_aux_rec Nat.xgcdAux_rec

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
  -- Porting note (https://github.com/leanprover/lean4/issues/2330):
  -- `simp [xgcdAux_succ]` crashes Lean here
  rw [xgcdAux_succ]
  rfl
#align nat.gcd_a_zero_right Nat.gcdA_zero_right

@[simp]
theorem gcdB_zero_right {s : ℕ} (h : s ≠ 0) : gcdB s 0 = 0 := by
  unfold gcdB xgcd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  -- Porting note (https://github.com/leanprover/lean4/issues/2330):
  -- `simp [xgcdAux_succ]` crashes Lean here
  rw [xgcdAux_succ]
  rfl
#align nat.gcd_b_zero_right Nat.gcdB_zero_right

@[simp]
theorem xgcdAux_fst (x y) : ∀ s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  gcd.induction x y (by simp) fun x y h IH s t s' t' => by
    simp only [h, xgcdAux_rec, IH]
    rw [← gcd_rec]
#align nat.xgcd_aux_fst Nat.xgcdAux_fst

theorem xgcdAux_val (x y) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd, ← xgcdAux_fst x y 1 0 0 1]
#align nat.xgcd_aux_val Nat.xgcdAux_val

theorem xgcd_val (x y) : xgcd x y = (gcdA x y, gcdB x y) := by
  unfold gcdA gcdB; cases xgcd x y; rfl
#align nat.xgcd_val Nat.xgcd_val

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
    rw [xgcdAux_rec h]; refine' IH _ p; dsimp [P] at *
    rw [Int.emod_def]; generalize (b / a : ℤ) = k
    rw [p, p', mul_sub, sub_add_eq_add_sub, mul_sub, add_mul, mul_comm k t, mul_comm k s,
      ← mul_assoc, ← mul_assoc, add_comm (x * s * k), ← add_sub_assoc, sub_sub]
set_option linter.uppercaseLean3 false in
#align nat.xgcd_aux_P Nat.xgcdAux_P

/-- **Bézout's lemma**: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcdA x y + y * gcdB x y := by
  have := @xgcdAux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P])
  rwa [xgcdAux_val, xgcd_val] at this
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

theorem exists_mul_emod_eq_one_of_coprime {k n : ℕ} (hkn : Coprime n k) (hk : 1 < k) :
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
  · rw [natAbs_eq_zero.1 h]
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

#align int.lcm Int.lcm

theorem lcm_def (i j : ℤ) : lcm i j = Nat.lcm (natAbs i) (natAbs j) :=
  rfl
#align int.lcm_def Int.lcm_def

protected theorem coe_nat_lcm (m n : ℕ) : Int.lcm ↑m ↑n = Nat.lcm m n :=
  rfl
#align int.coe_nat_lcm Int.coe_nat_lcm

#align int.gcd_dvd_left Int.gcd_dvd_left
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

#align int.gcd_one_left Int.one_gcd
#align int.gcd_one_right Int.gcd_one
#align int.gcd_neg_right Int.gcd_neg
#align int.gcd_neg_left Int.neg_gcd

theorem gcd_mul_left (i j k : ℤ) : gcd (i * j) (i * k) = natAbs i * gcd j k := by
  rw [Int.gcd, Int.gcd, natAbs_mul, natAbs_mul]
  apply Nat.gcd_mul_left
#align int.gcd_mul_left Int.gcd_mul_left

theorem gcd_mul_right (i j k : ℤ) : gcd (i * j) (k * j) = gcd i k * natAbs j := by
  rw [Int.gcd, Int.gcd, natAbs_mul, natAbs_mul]
  apply Nat.gcd_mul_right
#align int.gcd_mul_right Int.gcd_mul_right

theorem gcd_pos_of_ne_zero_left {i : ℤ} (j : ℤ) (hi : i ≠ 0) : 0 < gcd i j :=
  Nat.gcd_pos_of_pos_left _ <| natAbs_pos.2 hi
#align int.gcd_pos_of_ne_zero_left Int.gcd_pos_of_ne_zero_left

theorem gcd_pos_of_ne_zero_right (i : ℤ) {j : ℤ} (hj : j ≠ 0) : 0 < gcd i j :=
  Nat.gcd_pos_of_pos_right _ <| natAbs_pos.2 hj
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
  rw [gcd_div gcd_dvd_left gcd_dvd_right, natAbs_ofNat, Nat.div_self H]
#align int.gcd_div_gcd_div_gcd Int.gcd_div_gcd_div_gcd

theorem gcd_dvd_gcd_of_dvd_left {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd i j ∣ gcd k j :=
  Int.coe_nat_dvd.1 <| dvd_gcd (gcd_dvd_left.trans H) gcd_dvd_right
#align int.gcd_dvd_gcd_of_dvd_left Int.gcd_dvd_gcd_of_dvd_left

theorem gcd_dvd_gcd_of_dvd_right {i k : ℤ} (j : ℤ) (H : i ∣ k) : gcd j i ∣ gcd j k :=
  Int.coe_nat_dvd.1 <| dvd_gcd gcd_dvd_left (gcd_dvd_right.trans H)
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
  ⟨_, _, gcd_div_gcd_div_gcd H, (Int.ediv_mul_cancel gcd_dvd_left).symm,
    (Int.ediv_mul_cancel gcd_dvd_right).symm⟩
#align int.exists_gcd_one Int.exists_gcd_one

theorem exists_gcd_one' {m n : ℤ} (H : 0 < gcd m n) :
    ∃ (g : ℕ) (m' n' : ℤ), 0 < g ∧ gcd m' n' = 1 ∧ m = m' * g ∧ n = n' * g :=
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
      dvd_add (dvd_mul_of_dvd_left gcd_dvd_left _) (dvd_mul_of_dvd_left gcd_dvd_right y)
#align int.gcd_dvd_iff Int.gcd_dvd_iff

theorem gcd_greatest {a b d : ℤ} (hd_pos : 0 ≤ d) (hda : d ∣ a) (hdb : d ∣ b)
    (hd : ∀ e : ℤ, e ∣ a → e ∣ b → e ∣ d) : d = gcd a b :=
  dvd_antisymm hd_pos (ofNat_zero_le (gcd a b)) (dvd_gcd hda hdb)
    (hd _ gcd_dvd_left gcd_dvd_right)
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

#align int.lcm_self Int.lcm_self
#align int.dvd_lcm_left Int.dvd_lcm_left
#align int.dvd_lcm_right Int.dvd_lcm_right

theorem lcm_dvd {i j k : ℤ} : i ∣ k → j ∣ k → (lcm i j : ℤ) ∣ k := by
  rw [Int.lcm]
  intro hi hj
  exact coe_nat_dvd_left.mpr (Nat.lcm_dvd (natAbs_dvd_natAbs.mpr hi) (natAbs_dvd_natAbs.mpr hj))
#align int.lcm_dvd Int.lcm_dvd

theorem lcm_mul_left {m n k : ℤ} : (m * n).lcm (m * k) = natAbs m * n.lcm k := by
  simp_rw [Int.lcm, natAbs_mul, Nat.lcm_mul_left]

theorem lcm_mul_right {m n k : ℤ} : (m * n).lcm (k * n) = m.lcm k * natAbs n := by
  simp_rw [Int.lcm, natAbs_mul, Nat.lcm_mul_right]

end Int

@[to_additive gcd_nsmul_eq_zero]
theorem pow_gcd_eq_one {M : Type*} [Monoid M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
    x ^ m.gcd n = 1 := by
  rcases m with (rfl | m); · simp [hn]
  obtain ⟨y, rfl⟩ := isUnit_ofPowEqOne hm m.succ_ne_zero
  simp only [← Units.val_pow_eq_pow_val] at *
  rw [← Units.val_one, ← zpow_coe_nat, ← Units.ext_iff] at *
  simp only [Nat.gcd_eq_gcd_ab, zpow_add, zpow_mul, hm, hn, one_zpow, one_mul]
#align pow_gcd_eq_one pow_gcd_eq_one
#align gcd_nsmul_eq_zero gcd_nsmul_eq_zero

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
    conv_lhs => rw [← zpow_ofNat, ← hmn, Nat.gcd_eq_gcd_ab]
    simp only [zpow_add₀ ha, zpow_add₀ hb, ← zpow_ofNat, (hab.zpow_zpow₀ _ _).mul_zpow, ← zpow_mul,
      mul_comm (Nat.gcdB m n), mul_comm (Nat.gcdA m n)]
    simp only [zpow_mul, zpow_ofNat, h]
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
