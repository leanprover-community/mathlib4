/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modEq_and_modEq_iff_modEq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `nat.ModEq n a b`, which is defined to mean `a % n = b % n`.

## Tags

ModEq, congruence, mod, MOD, modulo
-/

assert_not_exists OrderedAddCommMonoid Function.support

namespace Nat

/-- Modular equality. `n.ModEq a b`, or `a ≡ b [MOD n]`, means that `a - b` is a multiple of `n`. -/
def ModEq (n a b : ℕ) :=
  a % n = b % n

@[inherit_doc]
notation:50 a " ≡ " b " [MOD " n "]" => ModEq n a b

variable {m n a b c d : ℕ}

-- Since `ModEq` is semi-reducible, we need to provide the decidable instance manually
instance : Decidable (ModEq n a b) := inferInstanceAs <| Decidable (a % n = b % n)

namespace ModEq

@[refl]
protected theorem refl (a : ℕ) : a ≡ a [MOD n] := rfl

protected theorem rfl : a ≡ a [MOD n] :=
  ModEq.refl _

instance : IsRefl _ (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] :=
  Eq.symm

@[trans]
protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] :=
  Eq.trans

instance : Trans (ModEq n) (ModEq n) (ModEq n) where
  trans := Nat.ModEq.trans

protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] :=
  ⟨ModEq.symm, ModEq.symm⟩

end ModEq

theorem modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a := by rw [ModEq, zero_mod, dvd_iff_mod_eq_zero]

theorem _root_.Dvd.dvd.modEq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] :=
  modEq_zero_iff_dvd.2 h

theorem _root_.Dvd.dvd.zero_modEq_nat (h : n ∣ a) : 0 ≡ a [MOD n] :=
  h.modEq_zero_nat.symm

theorem modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : ℤ) ∣ b - a := by
  rw [ModEq, eq_comm, ← Int.natCast_inj, Int.natCast_mod, Int.natCast_mod,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

/-- A variant of `modEq_iff_dvd` with `Nat` divisibility -/
theorem modEq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a := by
  rw [modEq_iff_dvd, ← Int.natCast_dvd_natCast, Int.ofNat_sub h]

theorem mod_modEq (a n) : a % n ≡ a [MOD n] :=
  mod_mod _ _

namespace ModEq

lemma of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
  modEq_of_dvd <| Int.ofNat_dvd.mpr d |>.trans h.dvd

protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD c * n] := by
  unfold ModEq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

@[gcongr]
protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
  (h.mul_left' _).of_dvd (dvd_mul_left _ _)

protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' c

@[gcongr]
protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] := by
  rw [mul_comm a, mul_comm b]; exact h.mul_left c

@[gcongr]
protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr]
protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] := by
  induction m with
  | zero => rfl
  | succ d hd =>
    rw [Nat.pow_succ, Nat.pow_succ]
    exact hd.mul h

@[gcongr]
protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] := by
  rw [modEq_iff_dvd, Int.natCast_add, Int.natCast_add, add_sub_add_comm]
  exact Int.dvd_add h₁.dvd h₂.dvd

@[gcongr]
protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
  ModEq.rfl.add h

@[gcongr]
protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
  h.add ModEq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    c ≡ d [MOD n] := by
  simp only [modEq_iff_dvd, Int.natCast_add] at *
  rw [add_sub_add_comm] at h₂
  convert Int.dvd_sub h₂ h₁ using 1
  rw [add_sub_cancel_left]

protected theorem add_left_cancel' (c : ℕ) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
    a ≡ b [MOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂

protected theorem add_right_cancel' (c : ℕ) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
  ModEq.rfl.add_right_cancel h

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Nat.ModEq.of_mul_left`. -/
protected theorem mul_left_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] → a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.mul_sub]
  exact fun h => (Int.dvd_of_mul_dvd_mul_left (Int.ofNat_ne_zero.mpr hc) h)

protected theorem mul_left_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    c * a ≡ c * b [MOD c * m] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_left_cancel' hc, ModEq.mul_left' _⟩

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Nat.ModEq.of_mul_right`. -/
protected theorem mul_right_cancel' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] → a ≡ b [MOD m] := by
  simp only [modEq_iff_dvd, Int.natCast_mul, ← Int.sub_mul]
  exact fun h => (Int.dvd_of_mul_dvd_mul_right (Int.ofNat_ne_zero.mpr hc) h)

protected theorem mul_right_cancel_iff' {a b c m : ℕ} (hc : c ≠ 0) :
    a * c ≡ b * c [MOD m * c] ↔ a ≡ b [MOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right' _⟩

/-- Cancel left multiplication in the modulus.

For cancelling left multiplication on both sides of the `≡`, see `nat.modeq.mul_left_cancel'`. -/
lemma of_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] := by
  rw [modEq_iff_dvd] at *
  exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h

/-- Cancel right multiplication in the modulus.

For cancelling right multiplication on both sides of the `≡`, see `nat.modeq.mul_right_cancel'`. -/
lemma of_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] := mul_comm m n ▸ of_mul_left _

theorem of_div (h : a / c ≡ b / c [MOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [MOD m] := by convert h.mul_left' c <;> rwa [Nat.mul_div_cancel']

end ModEq

lemma modEq_sub (h : b ≤ a) : a ≡ b [MOD a - b] := (modEq_of_dvd <| by rw [Int.ofNat_sub h]).symm

lemma modEq_one : a ≡ b [MOD 1] := modEq_of_dvd <| one_dvd _

@[simp] lemma modEq_zero_iff : a ≡ b [MOD 0] ↔ a = b := by rw [ModEq, mod_zero, mod_zero]

@[simp] lemma add_modEq_left : n + a ≡ a [MOD n] := by rw [ModEq, add_mod_left]

@[simp] lemma add_modEq_right : a + n ≡ a [MOD n] := by rw [ModEq, add_mod_right]

namespace ModEq

theorem le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a ≤ b :=
  (le_total a b).elim id fun h3 =>
    Nat.le_of_sub_eq_zero
      (eq_zero_of_dvd_of_lt ((modEq_iff_dvd' h3).mp h1.symm) (by omega))

theorem add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m ≤ b :=
  le_of_lt_add (add_modEq_right.trans h1) (by omega)

theorem dvd_iff (h : a ≡ b [MOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

theorem gcd_eq (h : a ≡ b [MOD m]) : gcd a m = gcd b m := by
  have h1 := gcd_dvd_right a m
  have h2 := gcd_dvd_right b m
  exact
    dvd_antisymm (dvd_gcd ((h.dvd_iff h1).mp (gcd_dvd_left a m)) h1)
      (dvd_gcd ((h.dvd_iff h2).mpr (gcd_dvd_left b m)) h2)

lemma eq_of_abs_lt (h : a ≡ b [MOD m]) (h2 : |(b : ℤ) - a| < m) : a = b := by
  apply Int.ofNat.inj
  rw [eq_comm, ← sub_eq_zero]
  exact Int.eq_zero_of_abs_lt_dvd h.dvd h2

lemma eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m) (hb : b < m) : a = b :=
  h.eq_of_abs_lt <| Int.abs_sub_lt_of_lt_lt ha hb

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [MOD m]) :  a ≡ b [MOD m / gcd m c] := by
  let d := gcd m c
  have hmd := gcd_dvd_left m c
  have hcd := gcd_dvd_right m c
  rw [modEq_iff_dvd]
  refine @Int.dvd_of_dvd_mul_right_of_gcd_one (m / d) (c / d) (b - a) ?_ ?_
  · show (m / d : ℤ) ∣ c / d * (b - a)
    rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (Int.natCast_dvd_natCast.mpr hcd), mul_comm]
    apply Int.ediv_dvd_ediv (Int.natCast_dvd_natCast.mpr hmd)
    rw [Int.mul_sub]
    exact modEq_iff_dvd.mp h
  · show Int.gcd (m / d) (c / d) = 1
    simp only [d, ← Int.natCast_div, Int.gcd_natCast_natCast (m / d) (c / d),
      gcd_div hmd hcd, Nat.div_self (gcd_pos_of_pos_left c hm)]

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c` -/
lemma cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m / gcd m c] := by
  apply cancel_left_div_gcd hm
  simpa [mul_comm] using h

lemma cancel_left_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : c * a ≡ d * b [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_right b).cancel_left_div_gcd hm

lemma cancel_right_div_gcd' (hm : 0 < m) (hcd : c ≡ d [MOD m]) (h : a * c ≡ b * d [MOD m]) :
    a ≡ b [MOD m / gcd m c] :=
  (h.trans <| hcd.symm.mul_left b).cancel_right_div_gcd hm

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
lemma cancel_left_of_coprime (hmc : gcd m c = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · simp only [gcd_zero_left] at hmc
    simp only [gcd_zero_left, hmc, one_mul, modEq_zero_iff] at h
    subst h
    rfl
  simpa [hmc] using h.cancel_left_div_gcd hm

/-- A common factor that's coprime with the modulus can be cancelled from a `ModEq` -/
lemma cancel_right_of_coprime (hmc : gcd m c = 1) (h : a * c ≡ b * c [MOD m]) : a ≡ b [MOD m] :=
  cancel_left_of_coprime hmc <| by simpa [mul_comm] using h

end ModEq

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chineseRemainder' (h : a ≡ b [MOD gcd n m]) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  if hn : n = 0 then ⟨a, by
    rw [hn, gcd_zero_left] at h; constructor
    · rfl
    · exact h⟩
  else
    if hm : m = 0 then ⟨b, by
      rw [hm, gcd_zero_right] at h; constructor
      · exact h.symm
      · rfl⟩
    else
      ⟨let (c, d) := xgcd n m; Int.toNat ((n * c * b + m * d * a) / gcd n m % lcm n m), by
        rw [xgcd_val]
        dsimp
        rw [modEq_iff_dvd, modEq_iff_dvd,
          Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.2 (lcm_ne_zero hn hm)))]
        have hnonzero : (gcd n m : ℤ) ≠ 0 := by
          norm_cast
          rw [Nat.gcd_eq_zero_iff, not_and]
          exact fun _ => hm
        have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t * (b - a) := fun t => h.dvd.mul_left _
        have := gcd_eq_gcd_ab n m
        constructor <;> rw [Int.emod_def, ← sub_add] <;>
            refine Int.dvd_add ?_ (dvd_mul_of_dvd_left ?_ _) <;>
          try norm_cast
        · rw [← sub_eq_iff_eq_add'] at this
          rw [← this, Int.sub_mul, ← add_sub_assoc, add_comm, add_sub_assoc, ← Int.mul_sub,
            Int.add_ediv_of_dvd_left, Int.mul_ediv_cancel_left _ hnonzero,
            Int.mul_ediv_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, Int.dvd_neg, mul_assoc]
          · exact dvd_mul_right _ _
          norm_cast
          exact dvd_mul_right _ _
        · exact dvd_lcm_left n m
        · rw [← sub_eq_iff_eq_add] at this
          rw [← this, Int.sub_mul, sub_add, ← Int.mul_sub, Int.sub_ediv_of_dvd,
            Int.mul_ediv_cancel_left _ hnonzero, Int.mul_ediv_assoc _ h.dvd, ← sub_add, sub_self,
            zero_add, mul_assoc]
          · exact dvd_mul_right _ _
          · exact hcoedvd _
        · exact dvd_lcm_right n m⟩

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chineseRemainder (co : n.Coprime m) (a b : ℕ) : { k // k ≡ a [MOD n] ∧ k ≡ b [MOD m] } :=
  chineseRemainder' (by convert @modEq_one a b)

theorem chineseRemainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder' h) < lcm n m := by
  dsimp only [chineseRemainder']
  rw [dif_neg hn, dif_neg hm, Subtype.coe_mk, xgcd_val, ← Int.toNat_natCast (lcm n m)]
  have lcm_pos := Int.natCast_pos.mpr (Nat.pos_of_ne_zero (lcm_ne_zero hn hm))
  exact (Int.toNat_lt_toNat lcm_pos).mpr (Int.emod_lt_of_pos _ lcm_pos)

theorem chineseRemainder_lt_mul (co : n.Coprime m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
    ↑(chineseRemainder co a b) < n * m :=
  lt_of_lt_of_le (chineseRemainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

theorem mod_lcm (hn : a ≡ b [MOD n]) (hm : a ≡ b [MOD m]) : a ≡ b [MOD lcm n m] :=
  Nat.modEq_iff_dvd.mpr <| Int.coe_lcm_dvd (Nat.modEq_iff_dvd.mp hn) (Nat.modEq_iff_dvd.mp hm)

theorem chineseRemainder_modEq_unique (co : n.Coprime m) {a b z}
    (hzan : z ≡ a [MOD n]) (hzbm : z ≡ b [MOD m]) : z ≡ chineseRemainder co a b [MOD n*m] := by
  simpa [Nat.Coprime.lcm_eq_mul co] using
    mod_lcm (hzan.trans ((chineseRemainder co a b).prop.1).symm)
      (hzbm.trans ((chineseRemainder co a b).prop.2).symm)

theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℕ} (hmn : m.Coprime n) :
    a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ a ≡ b [MOD m * n] :=
  ⟨fun h => by
    rw [Nat.modEq_iff_dvd, Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast,
      ← Int.dvd_natAbs, Int.natCast_dvd_natCast] at h
    rw [Nat.modEq_iff_dvd, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2,
   fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

theorem coprime_of_mul_modEq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : a.Coprime n := by
  obtain ⟨g, hh⟩ := Nat.gcd_dvd_right a n
  rw [Nat.coprime_iff_gcd_eq_one, ← Nat.dvd_one, ← Nat.modEq_zero_iff_dvd]
  calc
    1 ≡ a * b [MOD a.gcd n] := (hh ▸ h).symm.of_mul_right g
    _ ≡ 0 * b [MOD a.gcd n] := (Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_left _ _)).mul_right b
    _ = 0 := by rw [zero_mul]

theorem add_mod_add_ite (a b c : ℕ) :
    ((a + b) % c + if c ≤ a % c + b % c then c else 0) = a % c + b % c :=
  have : (a + b) % c = (a % c + b % c) % c := ((mod_modEq _ _).add <| mod_modEq _ _).symm
  if hc0 : c = 0 then by simp [hc0, Nat.mod_zero]
  else by
    rw [this]
    split_ifs with h
    · have h2 : (a % c + b % c) / c < 2 :=
        Nat.div_lt_of_lt_mul
          (by
            rw [mul_two]
            exact
              add_lt_add (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0))
                (Nat.mod_lt _ (Nat.pos_of_ne_zero hc0)))
      have h0 : 0 < (a % c + b % c) / c := Nat.div_pos h (Nat.pos_of_ne_zero hc0)
      rw [← @add_right_cancel_iff _ _ _ (c * ((a % c + b % c) / c)), add_comm _ c, add_assoc,
        mod_add_div, le_antisymm (le_of_lt_succ h2) h0, mul_one, add_comm]
    · rw [Nat.mod_eq_of_lt (lt_of_not_ge h), add_zero]

theorem add_mod_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
    (a + b) % c = a % c + b % c := by rw [← add_mod_add_ite, if_neg (not_le_of_gt hc), add_zero]

theorem add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) :
    (a + b) % c + c = a % c + b % c := by rw [← add_mod_add_ite, if_pos hc]

theorem add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
    (a + b) / c = a / c + b / c :=
  if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0), if_neg (not_le_of_gt hc), add_zero]

protected theorem add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) : (a + b) / c = a / c + b / c :=
  if h : c = 0 then by simp [h]
  else
    add_div_eq_of_add_mod_lt
      (by
        rw [Nat.mod_eq_zero_of_dvd hca, zero_add]
        exact Nat.mod_lt _ (zero_lt_of_ne_zero h))

protected theorem add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) : (a + b) / c = a / c + b / c := by
  rwa [add_comm, Nat.add_div_of_dvd_right, add_comm]

theorem add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) :
    (a + b) / c = a / c + b / c + 1 := by rw [Nat.add_div hc0, if_pos hc]

theorem add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
  if hc0 : c = 0 then by simp [hc0]
  else by rw [Nat.add_div (Nat.pos_of_ne_zero hc0)]; exact Nat.le_add_right _ _

theorem le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c ≤ a % c + b % c :=
  by_contradiction fun hc => by
    have : (a + b) % c = a % c + b % c := add_mod_of_add_mod_lt (lt_of_not_ge hc)
    simp_all [dvd_iff_mod_eq_zero]

theorem odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → n * m % 2 = 1 := by
  simpa [Nat.ModEq] using @ModEq.mul 2 n 1 m 1

theorem odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
    m * n / 2 = m * (n / 2) + m / 2 :=
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => by simp_all
  mul_right_injective₀ two_ne_zero <| by
    dsimp
    rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
      two_mul_odd_div_two (Nat.odd_mul_odd hm1 hn1), Nat.mul_sub, mul_one, ←
      Nat.add_sub_assoc (by omega), Nat.sub_add_cancel (Nat.le_mul_of_pos_right m hn0)]

theorem odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 1 2

theorem odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 := by
  simpa [ModEq] using @ModEq.of_mul_left 2 n 3 2

/-- A natural number is odd iff it has residue `1` or `3` mod `4`. -/
theorem odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 :=
  have help : ∀ m : ℕ, m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := by decide
  ⟨fun hn =>
    help (n % 4) (mod_lt n (by omega)) <| (mod_mod_of_dvd n (by decide : 2 ∣ 4)).trans hn,
    fun h => Or.elim h odd_of_mod_four_eq_one odd_of_mod_four_eq_three⟩

lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b :=
  Eq.trans h (mod_eq_of_lt hb)

end Nat
