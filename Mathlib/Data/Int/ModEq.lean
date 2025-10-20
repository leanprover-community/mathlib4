/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Data.Nat.ModEq

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

@[inherit_doc]
notation:50 a " ≡ " b " [ZMOD " n "]" => ModEq n a b

variable {m n a b c d : ℤ}

instance : Decidable (ModEq n a b) := decEq (a % n) (b % n)

namespace ModEq

@[refl, simp]
protected theorem refl (a : ℤ) : a ≡ a [ZMOD n] :=
  @rfl _ _

protected theorem rfl : a ≡ a [ZMOD n] :=
  ModEq.refl _

instance : IsRefl _ (ModEq n) :=
  ⟨ModEq.refl⟩

@[symm]
protected theorem symm : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] :=
  Eq.symm

@[trans]
protected theorem trans : a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ c [ZMOD n] :=
  Eq.trans

instance : IsTrans ℤ (ModEq n) where
  trans := @Int.ModEq.trans n

protected theorem eq : a ≡ b [ZMOD n] → a % n = b % n := id

end ModEq

theorem modEq_comm : a ≡ b [ZMOD n] ↔ b ≡ a [ZMOD n] := ⟨ModEq.symm, ModEq.symm⟩

@[simp, norm_cast]
theorem natCast_modEq_iff {a b n : ℕ} : a ≡ b [ZMOD n] ↔ a ≡ b [MOD n] := by
  unfold ModEq Nat.ModEq; rw [← Int.ofNat_inj]; simp

theorem modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a := by
  rw [ModEq, zero_emod, dvd_iff_emod_eq_zero]

theorem _root_.Dvd.dvd.modEq_zero_int (h : n ∣ a) : a ≡ 0 [ZMOD n] :=
  modEq_zero_iff_dvd.2 h

theorem _root_.Dvd.dvd.zero_modEq_int (h : n ∣ a) : 0 ≡ a [ZMOD n] :=
  h.modEq_zero_int.symm

theorem modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a := by
  rw [ModEq, eq_comm]
  simp [emod_eq_emod_iff_emod_sub_eq_zero, dvd_iff_emod_eq_zero]

theorem modEq_iff_add_fac {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ t, b = a + n * t := by
  rw [modEq_iff_dvd]
  exact exists_congr fun t => sub_eq_iff_eq_add'

alias ⟨ModEq.dvd, modEq_of_dvd⟩ := modEq_iff_dvd

theorem mod_modEq (a n) : a % n ≡ a [ZMOD n] :=
  emod_emod _ _

@[simp]
theorem neg_modEq_neg : -a ≡ -b [ZMOD n] ↔ a ≡ b [ZMOD n] := by
  simp only [modEq_iff_dvd, (by cutsat : -b - -a = -(b - a)), Int.dvd_neg]

@[simp]
theorem modEq_neg : a ≡ b [ZMOD -n] ↔ a ≡ b [ZMOD n] := by simp [modEq_iff_dvd]

namespace ModEq

protected theorem of_dvd (d : m ∣ n) (h : a ≡ b [ZMOD n]) : a ≡ b [ZMOD m] :=
  modEq_iff_dvd.2 <| d.trans h.dvd

protected theorem mul_left' (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD c * n] := by
  obtain hc | rfl | hc := lt_trichotomy c 0
  · rw [← neg_modEq_neg, ← modEq_neg, ← Int.neg_mul, ← Int.neg_mul, ← Int.neg_mul]
    simp only [ModEq, mul_emod_mul_of_pos _ _ (neg_pos.2 hc), h.eq]
  · simp only [Int.zero_mul, ModEq.rfl]
  · simp only [ModEq, mul_emod_mul_of_pos _ _ hc, h.eq]

protected theorem mul_right' (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n * c] := by
  rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left'

@[gcongr]
protected theorem add (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a + c ≡ b + d [ZMOD n] :=
  modEq_iff_dvd.2 <| by convert Int.dvd_add h₁.dvd h₂.dvd using 1; cutsat

protected theorem add_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c + a ≡ c + b [ZMOD n] :=
  ModEq.rfl.add h

protected theorem add_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n] :=
  h.add ModEq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    c ≡ d [ZMOD n] :=
  have : d - c = b + d - (a + c) - (b - a) := by cutsat
  modEq_iff_dvd.2 <| by
    rw [this]
    exact Int.dvd_sub h₂.dvd h₁.dvd

protected theorem add_left_cancel' (c : ℤ) (h : c + a ≡ c + b [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [ZMOD n]) (h₂ : a + c ≡ b + d [ZMOD n]) :
    a ≡ b [ZMOD n] := by
  rw [add_comm a, add_comm b] at h₂
  exact h₁.add_left_cancel h₂

protected theorem add_right_cancel' (c : ℤ) (h : a + c ≡ b + c [ZMOD n]) : a ≡ b [ZMOD n] :=
  ModEq.rfl.add_right_cancel h

@[gcongr] protected theorem neg (h : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] :=
  h.add_left_cancel (by simp_rw [← sub_eq_add_neg, sub_self]; rfl)

@[gcongr]
protected theorem sub (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a - c ≡ b - d [ZMOD n] := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h₁.add h₂.neg

protected theorem sub_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c - a ≡ c - b [ZMOD n] :=
  ModEq.rfl.sub h

protected theorem sub_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a - c ≡ b - c [ZMOD n] :=
  h.sub ModEq.rfl

protected theorem mul_left (c : ℤ) (h : a ≡ b [ZMOD n]) : c * a ≡ c * b [ZMOD n] :=
  h.mul_left'.of_dvd <| dvd_mul_left _ _

protected theorem mul_right (c : ℤ) (h : a ≡ b [ZMOD n]) : a * c ≡ b * c [ZMOD n] :=
  h.mul_right'.of_dvd <| dvd_mul_right _ _

@[gcongr]
protected theorem mul (h₁ : a ≡ b [ZMOD n]) (h₂ : c ≡ d [ZMOD n]) : a * c ≡ b * d [ZMOD n] :=
  (h₂.mul_left _).trans (h₁.mul_right _)

@[gcongr] protected theorem pow (m : ℕ) (h : a ≡ b [ZMOD n]) : a ^ m ≡ b ^ m [ZMOD n] := by
  induction m with
  | zero => rfl
  | succ d hd => rw [pow_succ, pow_succ]; exact hd.mul h

lemma of_mul_left (m : ℤ) (h : a ≡ b [ZMOD m * n]) : a ≡ b [ZMOD n] := by
  rw [modEq_iff_dvd] at *; exact (dvd_mul_left n m).trans h

lemma of_mul_right (m : ℤ) : a ≡ b [ZMOD n * m] → a ≡ b [ZMOD n] :=
  mul_comm m n ▸ of_mul_left _

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
theorem cancel_right_div_gcd (hm : 0 < m) (h : a * c ≡ b * c [ZMOD m]) :
    a ≡ b [ZMOD m / gcd m c] := by
  letI d := gcd m c
  rw [modEq_iff_dvd] at h ⊢
  refine Int.dvd_of_dvd_mul_right_of_gcd_one (?_ : m / d ∣ c / d * (b - a)) ?_
  · rw [mul_comm, ← Int.mul_ediv_assoc (b - a) (gcd_dvd_right ..), Int.sub_mul]
    exact Int.ediv_dvd_ediv (gcd_dvd_left ..) h
  · rw [gcd_div (gcd_dvd_left ..) (gcd_dvd_right ..), natAbs_natCast,
      Nat.div_self (gcd_pos_of_ne_zero_left c hm.ne')]

/-- To cancel a common factor `c` from a `ModEq` we must divide the modulus `m` by `gcd m c`. -/
theorem cancel_left_div_gcd (hm : 0 < m) (h : c * a ≡ c * b [ZMOD m]) : a ≡ b [ZMOD m / gcd m c] :=
  cancel_right_div_gcd hm <| by simpa [mul_comm] using h

theorem of_div (h : a / c ≡ b / c [ZMOD m / c]) (ha : c ∣ a) (ha : c ∣ b) (ha : c ∣ m) :
    a ≡ b [ZMOD m] := by convert h.mul_left' <;> rwa [Int.mul_ediv_cancel']

/-- Cancel left multiplication on both sides of the `≡` and in the modulus.

For cancelling left multiplication in the modulus, see `Int.ModEq.of_mul_left`. -/
protected theorem mul_left_cancel' (hc : c ≠ 0) :
    c * a ≡ c * b [ZMOD c * m] → a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.mul_sub]
  exact Int.dvd_of_mul_dvd_mul_left hc

protected theorem mul_left_cancel_iff' (hc : c ≠ 0) :
    c * a ≡ c * b [ZMOD c * m] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_left_cancel' hc, Int.ModEq.mul_left'⟩

/-- Cancel right multiplication on both sides of the `≡` and in the modulus.

For cancelling right multiplication in the modulus, see `Int.ModEq.of_mul_right`. -/
protected theorem mul_right_cancel' (hc : c ≠ 0) :
    a * c ≡ b * c [ZMOD m * c] → a ≡ b [ZMOD m] := by
  simp only [modEq_iff_dvd, ← Int.sub_mul]
  exact Int.dvd_of_mul_dvd_mul_right hc

protected theorem mul_right_cancel_iff' (hc : c ≠ 0) :
    a * c ≡ b * c [ZMOD m * c] ↔ a ≡ b [ZMOD m] :=
  ⟨ModEq.mul_right_cancel' hc, ModEq.mul_right'⟩

end ModEq

theorem modEq_one : a ≡ b [ZMOD 1] :=
  modEq_of_dvd (one_dvd _)

theorem modEq_sub (a b : ℤ) : a ≡ b [ZMOD a - b] :=
  (modEq_of_dvd dvd_rfl).symm

@[simp]
theorem modEq_zero_iff : a ≡ b [ZMOD 0] ↔ a = b := by rw [ModEq, emod_zero, emod_zero]

@[simp]
theorem add_modEq_left : n + a ≡ a [ZMOD n] := ModEq.symm <| modEq_iff_dvd.2 <| by simp

@[simp]
theorem add_modEq_right : a + n ≡ a [ZMOD n] := ModEq.symm <| modEq_iff_dvd.2 <| by simp

theorem modEq_and_modEq_iff_modEq_mul {a b m n : ℤ} (hmn : m.natAbs.Coprime n.natAbs) :
    a ≡ b [ZMOD m] ∧ a ≡ b [ZMOD n] ↔ a ≡ b [ZMOD m * n] :=
  ⟨fun h => by
    rw [modEq_iff_dvd, modEq_iff_dvd] at h
    rw [modEq_iff_dvd, ← natAbs_dvd, ← dvd_natAbs, natCast_dvd_natCast, natAbs_mul]
    refine hmn.mul_dvd_of_dvd_of_dvd ?_ ?_ <;>
      rw [← natCast_dvd_natCast, natAbs_dvd, dvd_natAbs] <;>
      tauto,
    fun h => ⟨h.of_mul_right _, h.of_mul_left _⟩⟩

theorem gcd_a_modEq (a b : ℕ) : (a : ℤ) * Nat.gcdA a b ≡ Nat.gcd a b [ZMOD b] := by
  rw [← add_zero ((a : ℤ) * _), Nat.gcd_eq_gcd_ab]
  exact (dvd_mul_right _ _).zero_modEq_int.add_left _

theorem modEq_add_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a + n * c ≡ b [ZMOD n] :=
  calc
    a + n * c ≡ b + n * c [ZMOD n] := ha.add_right _
    _ ≡ b + 0 [ZMOD n] := (dvd_mul_right _ _).modEq_zero_int.add_left _
    _ ≡ b [ZMOD n] := by rw [add_zero]

theorem modEq_sub_fac {a b n : ℤ} (c : ℤ) (ha : a ≡ b [ZMOD n]) : a - n * c ≡ b [ZMOD n] := by
  convert Int.modEq_add_fac (-c) ha using 1; rw [Int.mul_neg, sub_eq_add_neg]

theorem modEq_add_fac_self {a t n : ℤ} : a + n * t ≡ a [ZMOD n] :=
  modEq_add_fac _ ModEq.rfl

theorem mod_coprime {a b : ℕ} (hab : Nat.Coprime a b) : ∃ y : ℤ, a * y ≡ 1 [ZMOD b] :=
  ⟨Nat.gcdA a b,
    have hgcd : Nat.gcd a b = 1 := Nat.Coprime.gcd_eq_one hab
    calc
      ↑a * Nat.gcdA a b ≡ ↑a * Nat.gcdA a b + ↑b * Nat.gcdB a b [ZMOD ↑b] :=
        ModEq.symm <| modEq_add_fac _ <| ModEq.refl _
      _ ≡ 1 [ZMOD ↑b] := by rw [← Nat.gcd_eq_gcd_ab, hgcd]; rfl
      ⟩

theorem existsUnique_equiv (a : ℤ) {b : ℤ} (hb : 0 < b) :
    ∃ z : ℤ, 0 ≤ z ∧ z < b ∧ z ≡ a [ZMOD b] :=
  ⟨a % b, emod_nonneg _ (ne_of_gt hb),
    by
      have : a % b < |b| := emod_lt_abs _ (ne_of_gt hb)
      rwa [abs_of_pos hb] at this, by simp [ModEq]⟩

theorem existsUnique_equiv_nat (a : ℤ) {b : ℤ} (hb : 0 < b) : ∃ z : ℕ, ↑z < b ∧ ↑z ≡ a [ZMOD b] :=
  let ⟨z, hz1, hz2, hz3⟩ := existsUnique_equiv a hb
  ⟨z.natAbs, by
    constructor <;> rw [natAbs_of_nonneg hz1] <;> assumption⟩

theorem mod_mul_right_mod (a b c : ℤ) : a % (b * c) % b = a % b :=
  (mod_modEq _ _).of_mul_right _

theorem mod_mul_left_mod (a b c : ℤ) : a % (b * c) % c = a % c :=
  (mod_modEq _ _).of_mul_left _

end Int
