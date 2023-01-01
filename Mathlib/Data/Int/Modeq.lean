/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

! This file was ported from Lean 3 source module data.int.modeq
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Modeq
import Mathbin.Tactic.Ring

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`data.nat.modeq` defines them for the natural numbers. The notation is short for `n.modeq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/


namespace Int

/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
def Modeq (n a b : ℤ) :=
  a % n = b % n deriving Decidable
#align int.modeq Int.Modeq

-- mathport name: «expr ≡ [ZMOD ]»
notation:50 a " ≡ " b " [ZMOD " n "]" => Modeq n a b

variable {m n a b c d : ℤ}

namespace Modeq

@[refl]
protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] :=
  @rfl _ _
#align int.modeq.refl Int.Modeq.refl

protected theorem rfl : a ≡ a [ZMOD n] :=
  Modeq.refl _
#align int.modeq.rfl Int.Modeq.rfl

instance : IsRefl _ (Modeq n) :=
  ⟨Modeq.refl⟩

@[symm]
protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
  Eq.symm
#align int.modeq.symm Int.Modeq.symm

@[trans]
protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
  Eq.trans
#align int.modeq.trans Int.Modeq.trans

end Modeq

theorem coe_nat_modeq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold modeq Nat.Modeq <;> rw [← Int.ofNat_inj] <;> simp [coe_nat_mod]
#align int.coe_nat_modeq_iff Int.coe_nat_modeq_iff

theorem modeq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]
#align int.modeq_zero_iff_dvd Int.modeq_zero_iff_dvd

theorem Dvd.Dvd.modeq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modeq_zero_iff_dvd.2 h
#align has_dvd.dvd.modeq_zero_int Dvd.Dvd.modeq_zero_int

theorem Dvd.Dvd.zero_modeq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modeq_zero_int.symm
#align has_dvd.dvd.zero_modeq_int Dvd.Dvd.zero_modeq_int

theorem modeq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [modeq, eq_comm] <;> simp [mod_eq_mod_iff_mod_sub_eq_zero, dvd_iff_mod_eq_zero]
#align int.modeq_iff_dvd Int.modeq_iff_dvd

theorem modeq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t :=
  by
  rw [modeq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'
#align int.modeq_iff_add_fac Int.modeq_iff_add_fac

theorem Modeq.dvd : a ≡ b [ZMOD n] → n ∣ b - a :=
  modeq_iff_dvd.1
#align int.modeq.dvd Int.Modeq.dvd

theorem modeq_of_dvd : n ∣ b - a → a ≡ b [ZMOD n] :=
  modeq_iff_dvd.2
#align int.modeq_of_dvd Int.modeq_of_dvd

theorem mod_modeq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _
#align int.mod_modeq Int.mod_modeq

namespace Modeq

protected theorem modeq_of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
  modeq_iff_dvd.2 <| d.trans h.Dvd
#align int.modeq.modeq_of_dvd Int.Modeq.modeq_of_dvd

protected theorem mul_left' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] :=
  Or.cases_on hc.lt_or_eq
    (fun hc => by unfold modeq <;> simp [mul_mod_mul_of_pos hc, show _ = _ from h]) fun hc => by
    simp [hc.symm]
#align int.modeq.mul_left' Int.Modeq.mul_left'

protected theorem mul_right' (hc : 0 ≤ c) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n] <;> exact h.mul_left' hc
#align int.modeq.mul_right' Int.Modeq.mul_right'

protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modeq_iff_dvd.2 <| by
    convert dvd_add h₁.dvd h₂.dvd
    ring
#align int.modeq.add Int.Modeq.add

protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  Modeq.rfl.add h
#align int.modeq.add_left Int.Modeq.add_left

protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add Modeq.rfl
#align int.modeq.add_right Int.Modeq.add_right

protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by ring
  modeq_iff_dvd.2 <| by
    rw [this]
    exact dvd_sub h₂.dvd h₁.dvd
#align int.modeq.add_left_cancel Int.Modeq.add_left_cancel

protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  Modeq.rfl.add_left_cancel h
#align int.modeq.add_left_cancel' Int.Modeq.add_left_cancel'

protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂
#align int.modeq.add_right_cancel Int.Modeq.add_right_cancel

protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  Modeq.rfl.add_right_cancel h
#align int.modeq.add_right_cancel' Int.Modeq.add_right_cancel'

protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self])
#align int.modeq.neg Int.Modeq.neg

protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] :=
  by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg
#align int.modeq.sub Int.Modeq.sub

protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  Modeq.rfl.sub h
#align int.modeq.sub_left Int.Modeq.sub_left

protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub Modeq.rfl
#align int.modeq.sub_right Int.Modeq.sub_right

protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
  Or.cases_on (le_total 0 c) (fun hc => (h.mul_left' hc).modeq_of_dvd (dvd_mul_left _ _)) fun hc =>
    by
    rw [← neg_neg c, neg_mul, neg_mul _ b] <;>
      exact ((h.mul_left' <| neg_nonneg.2 hc).modeq_of_dvd (dvd_mul_left _ _)).neg
#align int.modeq.mul_left Int.Modeq.mul_left

protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
  by
  rw [mul_comm a, mul_comm b]
  exact h.mul_left c
#align int.modeq.mul_right Int.Modeq.mul_right

protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)
#align int.modeq.mul Int.Modeq.mul

protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] :=
  by
  induction' m with d hd; · rfl
  rw [pow_succ, pow_succ]
  exact h.mul hd
#align int.modeq.pow Int.Modeq.pow

theorem of_modeq_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modeq_iff_dvd] at * <;> exact (dvd_mul_left n m).trans h
#align int.modeq.of_modeq_mul_left Int.Modeq.of_modeq_mul_left

theorem of_modeq_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_modeq_mul_left _
#align int.modeq.of_modeq_mul_right Int.Modeq.of_modeq_mul_right

end Modeq

theorem modeq_one : a ≡ b [ZMOD 1] :=
  modeq_of_dvd (one_dvd _)
#align int.modeq_one Int.modeq_one

theorem modeq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
  (modeq_of_dvd dvd_rfl).symm
#align int.modeq_sub Int.modeq_sub

theorem modeq_and_modeq_iff_modeq_mul {a b m n : ℤ} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] :=
  ⟨fun h => by
    rw [modeq_iff_dvd, modeq_iff_dvd] at h
    rw [modeq_iff_dvd, ← nat_abs_dvd, ← dvd_nat_abs, coe_nat_dvd, nat_abs_mul]
    refine' hmn.mul_dvd_of_dvd_of_dvd _ _ <;> rw [← coe_nat_dvd, nat_abs_dvd, dvd_nat_abs] <;>
      tauto,
    fun h => ⟨h.of_modeq_mul_right _, h.of_modeq_mul_left _⟩⟩
#align int.modeq_and_modeq_iff_modeq_mul Int.modeq_and_modeq_iff_modeq_mul

theorem gcd_a_modeq (a b : ℕ) : (a : ℤ) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] :=
  by
  rw [← add_zero ((a : ℤ) * _), Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modeq_int.add_left _
#align int.gcd_a_modeq Int.gcd_a_modeq

theorem modeq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n * c ≡ b [ZMOD n] :=
  calc
    a + n * c ≡ b + n * c [ZMOD n] := ha.add_right _
    _ ≡ b + 0 [ZMOD n] := (dvd_mul_right _ _).modeq_zero_int.add_left _
    _ ≡ b [ZMOD n] := by rw [add_zero]
    
#align int.modeq_add_fac Int.modeq_add_fac

theorem modeq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
  modeq_add_fac _ Modeq.rfl
#align int.modeq_add_fac_self Int.modeq_add_fac_self

theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] :=
        modeq.symm <| modeq_add_fac _ <| Modeq.refl _
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd] <;> rfl
      ⟩
#align int.mod_coprime Int.mod_coprime

theorem exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
    have : a % b < |b| := emod_lt _ (ne_of_gt hb)
    rwa [abs_of_pos hb] at this, by simp [modeq]⟩
#align int.exists_unique_equiv Int.exists_unique_equiv

theorem exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [← of_nat_eq_coe, of_nat_nat_abs_eq_of_nonneg hz1] <;> assumption⟩
#align int.exists_unique_equiv_nat Int.exists_unique_equiv_nat

@[simp]
theorem mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
  (mod_modeq _ _).of_modeq_mul_right _
#align int.mod_mul_right_mod Int.mod_mul_right_mod

@[simp]
theorem mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
  (mod_modeq _ _).of_modeq_mul_left _
#align int.mod_mul_left_mod Int.mod_mul_left_mod

end Int

