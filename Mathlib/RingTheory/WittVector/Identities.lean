/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.identities
! leanprover-community/mathlib commit 0798037604b2d91748f9b43925fb7570a5f3256c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.WittVector.Frobenius
import Mathbin.RingTheory.WittVector.Verschiebung
import Mathbin.RingTheory.WittVector.MulP

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/


namespace WittVector

variable {p : ℕ} {R : Type _} [hp : Fact p.Prime] [CommRing R]

local notation "𝕎" => WittVector p

-- type as `\bbW`
noncomputable section

/-- The composition of Frobenius and Verschiebung is multiplication by `p`. -/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by ghost_calc x;
  ghost_simp [mul_comm]
#align witt_vector.frobenius_verschiebung WittVector.frobenius_verschiebung

/-- Verschiebung is the same as multiplication by `p` on the ring of Witt vectors of `zmod p`. -/
theorem verschiebung_zMod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung, frobenius_zmodp]
#align witt_vector.verschiebung_zmod WittVector.verschiebung_zMod

variable (p R)

theorem coeff_p_pow [CharP R p] (i : ℕ) : (p ^ i : 𝕎 R).coeff i = 1 :=
  by
  induction' i with i h
  · simp only [one_coeff_zero, Ne.def, pow_zero]
  ·
    rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_succ, h,
      one_pow]
#align witt_vector.coeff_p_pow WittVector.coeff_p_pow

theorem coeff_p_pow_eq_zero [CharP R p] {i j : ℕ} (hj : j ≠ i) : (p ^ i : 𝕎 R).coeff j = 0 :=
  by
  induction' i with i hi generalizing j
  · rw [pow_zero, one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  · rw [pow_succ', ← frobenius_verschiebung, coeff_frobenius_char_p]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow]
      exact Nat.Prime.pos hp.out
    · rw [verschiebung_coeff_succ, hi, zero_pow]
      · exact Nat.Prime.pos hp.out
      · exact ne_of_apply_ne (fun j : ℕ => j.succ) hj
#align witt_vector.coeff_p_pow_eq_zero WittVector.coeff_p_pow_eq_zero

theorem coeff_p [CharP R p] (i : ℕ) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 :=
  by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi
#align witt_vector.coeff_p WittVector.coeff_p

@[simp]
theorem coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0 := by rw [coeff_p, if_neg];
  exact zero_ne_one
#align witt_vector.coeff_p_zero WittVector.coeff_p_zero

@[simp]
theorem coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1 := by rw [coeff_p, if_pos rfl]
#align witt_vector.coeff_p_one WittVector.coeff_p_one

theorem p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) ≠ 0 := by intro h;
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R
#align witt_vector.p_nonzero WittVector.p_nonzero

theorem FractionRing.p_nonzero [Nontrivial R] [CharP R p] : (p : FractionRing (𝕎 R)) ≠ 0 := by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).Ne (p_nonzero _ _)
#align witt_vector.fraction_ring.p_nonzero WittVector.FractionRing.p_nonzero

variable {p R}

/-- The “projection formula” for Frobenius and Verschiebung. -/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by ghost_calc x y;
  rintro ⟨⟩ <;> ghost_simp [mul_assoc]
#align witt_vector.verschiebung_mul_frobenius WittVector.verschiebung_mul_frobenius

theorem mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 :=
  by
  rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_zero, zero_pow]
  exact Nat.Prime.pos hp.out
#align witt_vector.mul_char_p_coeff_zero WittVector.mul_charP_coeff_zero

theorem mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : ℕ) :
    (x * p).coeff (i + 1) = x.coeff i ^ p := by
  rw [← frobenius_verschiebung, coeff_frobenius_char_p, verschiebung_coeff_succ]
#align witt_vector.mul_char_p_coeff_succ WittVector.mul_charP_coeff_succ

theorem verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) = x * p :=
  by
  ext ⟨i⟩
  · rw [mul_char_p_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_char_p_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_char_p]
#align witt_vector.verschiebung_frobenius WittVector.verschiebung_frobenius

theorem verschiebung_frobenius_comm [CharP R p] :
    Function.Commute (verschiebung : 𝕎 R → 𝕎 R) frobenius := fun x => by
  rw [verschiebung_frobenius, frobenius_verschiebung]
#align witt_vector.verschiebung_frobenius_comm WittVector.verschiebung_frobenius_comm

/-!
## Iteration lemmas
-/


open Function

theorem iterate_verschiebung_coeff (x : 𝕎 R) (n k : ℕ) :
    ((verschiebung^[n]) x).coeff (k + n) = x.coeff k :=
  by
  induction' n with k ih
  · simp
  · rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]
    exact ih
#align witt_vector.iterate_verschiebung_coeff WittVector.iterate_verschiebung_coeff

theorem iterate_verschiebung_mul_left (x y : 𝕎 R) (i : ℕ) :
    (verschiebung^[i]) x * y = (verschiebung^[i]) (x * (frobenius^[i]) y) :=
  by
  induction' i with i ih generalizing y
  · simp
  · rw [iterate_succ_apply', ← verschiebung_mul_frobenius, ih, iterate_succ_apply']; rfl
#align witt_vector.iterate_verschiebung_mul_left WittVector.iterate_verschiebung_mul_left

section CharP

variable [CharP R p]

theorem iterate_verschiebung_mul (x y : 𝕎 R) (i j : ℕ) :
    (verschiebung^[i]) x * (verschiebung^[j]) y =
      (verschiebung^[i + j]) ((frobenius^[j]) x * (frobenius^[i]) y) :=
  by
  calc
    _ = (verschiebung^[i]) (x * (frobenius^[i]) ((verschiebung^[j]) y)) := _
    _ = (verschiebung^[i]) (x * (verschiebung^[j]) ((frobenius^[i]) y)) := _
    _ = (verschiebung^[i]) ((verschiebung^[j]) ((frobenius^[i]) y) * x) := _
    _ = (verschiebung^[i]) ((verschiebung^[j]) ((frobenius^[i]) y * (frobenius^[j]) x)) := _
    _ = (verschiebung^[i + j]) ((frobenius^[i]) y * (frobenius^[j]) x) := _
    _ = _ := _
  · apply iterate_verschiebung_mul_left
  · rw [verschiebung_frobenius_comm.iterate_iterate] <;> infer_instance
  · rw [mul_comm]
  · rw [iterate_verschiebung_mul_left]
  · rw [iterate_add_apply]
  · rw [mul_comm]
#align witt_vector.iterate_verschiebung_mul WittVector.iterate_verschiebung_mul

theorem iterate_frobenius_coeff (x : 𝕎 R) (i k : ℕ) :
    ((frobenius^[i]) x).coeff k = x.coeff k ^ p ^ i :=
  by
  induction' i with i ih
  · simp
  · rw [iterate_succ_apply', coeff_frobenius_char_p, ih]
    ring
#align witt_vector.iterate_frobenius_coeff WittVector.iterate_frobenius_coeff

/-- This is a slightly specialized form of [Hazewinkel, *Witt Vectors*][Haze09] 6.2 equation 5. -/
theorem iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : ℕ) :
    ((verschiebung^[i]) x * (verschiebung^[j]) y).coeff (i + j) =
      x.coeff 0 ^ p ^ j * y.coeff 0 ^ p ^ i :=
  by
  calc
    _ = ((verschiebung^[i + j]) ((frobenius^[j]) x * (frobenius^[i]) y)).coeff (i + j) := _
    _ = ((frobenius^[j]) x * (frobenius^[i]) y).coeff 0 := _
    _ = ((frobenius^[j]) x).coeff 0 * ((frobenius^[i]) y).coeff 0 := _
    _ = _ := _
  · rw [iterate_verschiebung_mul]
  · convert iterate_verschiebung_coeff _ _ _ using 2
    rw [zero_add]
  · apply mul_coeff_zero
  · simp only [iterate_frobenius_coeff]
#align witt_vector.iterate_verschiebung_mul_coeff WittVector.iterate_verschiebung_mul_coeff

end CharP

end WittVector

