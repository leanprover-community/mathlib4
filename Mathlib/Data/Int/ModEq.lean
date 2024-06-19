/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr.Core

#align_import data.int.modeq from "leanprover-community/mathlib"@"47a1a73351de8dd6c8d3d32b569c8e434b03ca47"

/-!

# Congruences modulo an integer

This file defines the equivalence relation `a ≡ b [ZMOD n]` on the integers, similarly to how
`Data.Nat.ModEq` defines them for the natural numbers. The notation is short for `n.ModEq a b`,
which is defined to be `a % n = b % n` for integers `a b n`.

## Tags

modeq, congruence, mod, MOD, modulo, integers

-/


namespace Int

/-- `a ≡ b [ZMOD n]` when `a % n = b % n`. -/
def ModEq (n a b : ℤ) :=
  a % n = b % n
#align int.modeq Int.ModEq

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => ModEq n a b

variable {m n a b c d : ℤ}

-- Porting note: This instance should be derivable automatically
instance : Decidable (ModEq n a b) := decEq (a % n) (b % n)

namespace ModEq

@[refl, simp]
protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] :=
  @rfl _ _
#align int.modeq.refl Int.ModEq.refl

protected theorem rfl : a ≡ a [ZMOD n] :=
  ModEq.refl _
#align int.modeq.rfl Int.ModEq.rfl

instance : IsRefl _ (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
  Eq.symm
#align int.modeq.symm Int.ModEq.symm

@[trans]
protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
  Eq.trans
#align int.modeq.trans Int.ModEq.trans

instance : IsTrans ℤ (ModEq n) where
  trans := @Int.ModEq.trans n

protected theorem eq : a ≡ b [ZMOD n] → a % n = b % n := id
#align int.modeq.eq Int.ModEq.eq

end ModEq

theorem modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n] := ⟨ModEq.symm, ModEq.symm⟩
#align int.modeq_comm Int.modEq_comm

theorem natCast_modEq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp [natCast_mod]
#align int.coe_nat_modeq_iff Int.natCast_modEq_iff

theorem modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by
  rw [ModEq, zero_emod, dvd_iff_emod_eq_zero]
#align int.modeq_zero_iff_dvd Int.modEq_zero_iff_dvd

theorem _root_.Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h
#align has_dvd.dvd.modeq_zero_int Dvd.dvd.modEq_zero_int

theorem _root_.Dvd.dvd.zero_modEq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modEq_zero_int.symm
#align has_dvd.dvd.zero_modeq_int Dvd.dvd.zero_modEq_int

theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [ModEq, eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]
#align int.modeq_iff_dvd Int.modEq_iff_dvd

theorem modEq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t := by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'
#align int.modeq_iff_add_fac Int.modEq_iff_add_fac

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd
#align int.modeq.dvd Int.ModEq.dvd
#align int.modeq_of_dvd Int.modEq_of_dvd

theorem mod_modEq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _
#align int.mod_modeq Int.mod_modEq

@[simp]
theorem neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
-- Porting note: Restore old proof once #3309 is through
  simp [-sub_neg_eq_add, neg_sub_neg, modEq_iff_dvd, dvd_sub_comm]
#align int.neg_modeq_neg Int.neg_modEq_neg

@[simp]
theorem modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n] := by simp [modEq_iff_dvd]
#align int.modeq_neg Int.modEq_neg

namespace ModEq

protected theorem of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
  modEq_iff_dvd.2 <| d.trans h.dvd
#align int.modeq.of_dvd Int.ModEq.of_dvd

protected theorem mul_left' (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] := by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← neg_mul, ← neg_mul, ← neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]
#align int.modeq.mul_left' Int.ModEq.mul_left'

protected theorem mul_right' (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left'
#align int.modeq.mul_right' Int.ModEq.mul_right'

@[gcongr]
protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modEq_iff_dvd.2 <| by convert dvd_add h₁.dvd h₂.dvd using 1; abel
#align int.modeq.add Int.ModEq.add

@[gcongr] protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  ModEq.rfl.add h
#align int.modeq.add_left Int.ModEq.add_left

@[gcongr] protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add ModEq.rfl
#align int.modeq.add_right Int.ModEq.add_right

protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by abel
  modEq_iff_dvd.2 <| by
    rw [this]
    exact dvd_sub h₂.dvd h₁.dvd
#align int.modeq.add_left_cancel Int.ModEq.add_left_cancel

protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_left_cancel h
#align int.modeq.add_left_cancel' Int.ModEq.add_left_cancel'

protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂
#align int.modeq.add_right_cancel Int.ModEq.add_right_cancel

protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_right_cancel h
#align int.modeq.add_right_cancel' Int.ModEq.add_right_cancel'

@[gcongr] protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)
#align int.modeq.neg Int.ModEq.neg

@[gcongr]
protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg
#align int.modeq.sub Int.ModEq.sub

@[gcongr] protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  ModEq.rfl.sub h
#align int.modeq.sub_left Int.ModEq.sub_left

@[gcongr] protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub ModEq.rfl
#align int.modeq.sub_right Int.ModEq.sub_right

@[gcongr] protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
  h.mul_left'.of_dvd <| dvd_mul_left _ _
#align int.modeq.mul_left Int.ModEq.mul_left

@[gcongr] protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
  h.mul_right'.of_dvd <| dvd_mul_right _ _
#align int.modeq.mul_right Int.ModEq.mul_right

@[gcongr]
protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)
#align int.modeq.mul Int.ModEq.mul

@[gcongr] protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] := by
  induction' m with d hd; · rfl
  rw [pow_succ, pow_succ]
  exact hd.mul h
#align int.modeq.pow Int.ModEq.pow

lemma of_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h
#align int.modeq.of_mul_left Int.ModEq.of_mul_left

lemma of_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_mul_left _
#align int.modeq.of_mul_right Int.ModEq.of_mul_right

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
theorem cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) :
    a ≡ b [ZMOD m / gcd m c] := by
  letI d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  -- Porting note: removed `show` due to leanprover-community/mathlib4#3305
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) gcd_dvd_right, sub_mul]
    exact Int.ediv_dvd_ediv gcd_dvd_left h
  · rw [gcd_div gcd_dvd_left gcd_dvd_right, natAbs_ofNat,
      Nat.div_self (gcd_pos_of_ne_zero_left c hm.ne')]
#align int.modeq.cancel_right_div_gcd Int.ModEq.cancel_right_div_gcd

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
theorem cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
  cancel_right_div_gcd hm <| by simpa [mul_comm] using h
#align int.modeq.cancel_left_div_gcd Int.ModEq.cancel_left_div_gcd

theorem of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [ZMOD m] := by convert h.mul_left' <;> rwa [Int.mul_ediv_cancel']
#align int.modeq.of_div Int.ModEq.of_div

end ModEq

theorem modEq_one : a ≡ b [ZMOD 1] :=
  modEq_of_dvd (one_dvd _)
#align int.modeq_one Int.modEq_one

theorem modEq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
  (modEq_of_dvd dvd_rfl).symm
#align int.modeq_sub Int.modEq_sub

@[simp]
theorem modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b := by rw [ModEq, emod_zero, emod_zero]
#align int.modeq_zero_iff Int.modEq_zero_iff

@[simp]
theorem add_modEq_left : n + a ≡ a [ZMOD n] := ModEq.symm <| modEq_iff_dvd.2 <| by simp
#align int.add_modeq_left Int.add_modEq_left

@[simp]
theorem add_modEq_right : a + n ≡ a [ZMOD n] := ModEq.symm <| modEq_iff_dvd.2 <| by simp
#align int.add_modeq_right Int.add_modEq_right

theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℤ} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] :=
  ⟨fun h => by
    rw [modEq_iff_dvd, modEq_iff_dvd] at h
    rw [modEq_iff_dvd, ← natAbs_dvd, ← dvd_natAbs, natCast_dvd_natCast, natAbs_mul]
    refine hmn.mul_dvd_of_dvd_of_dvd ?_ ?_ <;>
      rw [← natCast_dvd_natCast, natAbs_dvd, dvd_natAbs] <;>
      tauto,
    fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩
#align int.modeq_and_modeq_iff_modeq_mul Int.modEq_and_modEq_iff_modEq_mul

theorem gcd_a_modEq (a b : ℕ) : (a : ℤ) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] := by
  rw [← add_zero ((a : ℤ) * _), Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _
#align int.gcd_a_modeq Int.gcd_a_modEq

theorem modEq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n * c ≡ b [ZMOD n] :=
  calc
    a + n * c ≡ b + n * c [ZMOD n] := ha.add_right _
    _ ≡ b + 0 [ZMOD n] := (dvd_mul_right _ _).modEq_zero_int.add_left _
    _ ≡ b [ZMOD n] := by rw [add_zero]
#align int.modeq_add_fac Int.modEq_add_fac

theorem modEq_sub_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a - n * c ≡ b [ZMOD n] := by
  convert Int.modEq_add_fac (-c) ha using 1; rw [mul_neg, sub_eq_add_neg]

theorem modEq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
  modEq_add_fac _ ModEq.rfl
#align int.modeq_add_fac_self Int.modEq_add_fac_self

theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] :=
        ModEq.symm <| modEq_add_fac _ <| ModEq.refl _
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩
#align int.mod_coprime Int.mod_coprime

theorem exists_unique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩
#align int.exists_unique_equiv Int.exists_unique_equiv

theorem exists_unique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := exists_unique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩
#align int.exists_unique_equiv_nat Int.exists_unique_equiv_nat

theorem mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_mul_right _
#align int.mod_mul_right_mod Int.mod_mul_right_mod

theorem mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_mul_left _
#align int.mod_mul_left_mod Int.mod_mul_left_mod

@[deprecated (since := "2024-04-02")] alias coe_nat_modEq_iff := natCast_modEq_iff

end Int
