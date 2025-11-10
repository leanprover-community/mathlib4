/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# First digits of a natural number

This file provides a basic API for extracting the first `l` digits of a natural number `n` in a
given base `b` as a function `Fin l → ℕ`.

This is useful for computations with natural numbers of bounded length. For example, we provide a
proof that the natural numbers `< b ^ l` are in bijection with the functions
`Fin l → Finset.range b`, see `Nat.digitsFin_bijOn`. See also `Nat.sum_digits_sum_eq` for an
application.

## Main definitions and results

* `Nat.digitsFin`: the function that return the first `l` digits of `n` in some base `b`.
  Unlike `Nat.digits`, the last digits can be equal to `0` (this happens if `n < b ^ l`).
* `Nat.digitsFin_eq_append`: `b.digitsFin l n` is the concatenation of the list of digits of `n`
  in base `b` and some `0`'s.
* `Nat.digitsFin_bijOn`: the map `Nat.digitsFin l b` gives a bijection between the set of
  natural numbers `< b ^ l` and the set of functions `Fin l → Finset.range b`.
* `Nat.sum_digits_sum_eq`: formula for the sum of the sum of digits in base `b` of all natural
  integers `< b ^ l`.
-/

namespace Nat

open List

variable (b l n : ℕ)

theorem ofDigits_ofFn (f : Fin l → ℕ) :
    ofDigits b (ofFn f) = ∑ i, f i * b ^ i.val := by
  induction l with
  | zero => simp
  | succ n hn =>
      rw [ofFn_succ, ofDigits_cons, Fin.sum_univ_succ, hn, Finset.mul_sum, Fin.val_zero, pow_zero,
        mul_one]
      simp_rw [Nat.mul_left_comm b, ← pow_succ', Fin.val_succ]

/--
The first `l` digits, in little-endian order, of a natural number `n` in a specified base `b`.
Unlike `Nat.digits`, the last digits can be equal to `0` if `n` is too small.
-/
def digitsFin : ℕ → Fin l → ℕ := fun x i ↦ (b.digits x)[i]?.getD 0

variable {b}

/--
If `i` is such that `b ^ i ≤ n`, the `i`-th component of `b.digitsFin l n` is the `i`-th digit
of `n` in base `b`.
-/
@[simp]
theorem digitsFin_apply_of_le (hb : 1 < b) (i : Fin l) (hn : b ^ i.val ≤ n) :
    haveI : i < (b.digits n).length := (lt_digits_length_iff hb _).mpr hn
    b.digitsFin l n i = (b.digits n)[i] := by
  rw [digitsFin, getElem?_pos, Option.getD_some]

/--
If `i` is such that `b ^ i > n`, the `i`-th component of `b.digitsFin l n` is `0`.
-/
@[simp]
theorem digitsFin_apply_of_lt (hb : 1 < b) (i : Fin l) (hn : n < b ^ i.val) :
    b.digitsFin l n i = 0 := by
  rw [digitsFin, getElem?_neg _ _ (by rwa [lt_digits_length_iff hb, not_le]), Option.getD_none]

@[simp]
theorem digitsFin_lt (hb : 1 < b) (i : Fin l) : b.digitsFin l n i < b := by
  by_cases hn : b ^ i.val ≤ n
  · rw [digitsFin_apply_of_le _ _ hb _ hn]
    exact Nat.digits_lt_base hb <| List.mem_of_getElem rfl
  · rw [digitsFin_apply_of_lt _ _ hb _ (by rwa [← not_le])]
    exact zero_lt_of_lt hb

/--
If `n < b ^ l`, then, as a list, `b.digitsFin l n` is the concatenation of the list of
the digits of `n` in base `b` and some `0`'s.
-/
theorem digitsFin_eq_append (hb : 1 < b) (hn : n < b ^ l) :
    ofFn (b.digitsFin l n) = b.digits n ++ replicate (l - (b.digits n).length) 0 := by
  refine ext_getElem ?_ fun _ _ _ ↦ ?_
  · rw [length_ofFn, length_append, length_replicate,
      Nat.add_sub_cancel' (by rwa [digits_length_le_iff hb])]
  · rw [List.getElem_ofFn, List.getElem_append]
    split_ifs with h
    · rw [digitsFin_apply_of_le l n hb _ (by rwa [← lt_digits_length_iff hb]), Fin.getElem_fin]
    · rw [getElem_replicate, digitsFin_apply_of_lt _ _ hb]
      rwa [← digits_length_le_iff hb, ← not_lt]

theorem ofDigits_digitsFin (hb : 1 < b) (hn : n < b ^ l) :
    ofDigits b (ofFn (b.digitsFin l n)) = n := by
  rw [digitsFin_eq_append _ _ hb hn, ofDigits_append_replicate_zero, ofDigits_digits]

theorem sum_digitsFin_mul_pow (hb : 1 < b) (hn : n < b ^ l) :
    ∑ i, b.digitsFin l n i * b ^ i.val = n := by
  rw [← ofDigits_ofFn, ofDigits_digitsFin _ _ hb hn]

theorem digitsFin_sum (hb : 1 < b) (hn : n < b ^ l) :
    ∑ i, b.digitsFin l n i = (b.digits n).sum := by
  rw [← Fin.sum_ofFn, digitsFin_eq_append _ _ hb hn, sum_append_nat, sum_replicate, nsmul_zero,
    add_zero]

/--
`b.digitsFin l` is injective on the set of natural numbers `< b ^ l`.
-/
theorem digitsFin_injOn (hb : 1 < b) :
    Set.InjOn (b.digitsFin l) (Finset.range (b ^l)) := by
  rintro x hx y hy hxy
  rw [Finset.coe_range] at hx hy
  have := congr_arg (fun x ↦ ofDigits b (List.ofFn x)) hxy
  simpa [ofDigits_digitsFin _ _ hb hx, ofDigits_digitsFin _ _ hb hy] using this

/--
`b.digitsFin l` maps the set of natural numbers `< b ^ l` to the set of functions
`Fin l → Finset.range b`.
-/
theorem digitsFin_mapsTo (hb : 1 < b) :
    Set.MapsTo (b.digitsFin l) (Finset.range (b ^ l))
      (Fintype.piFinset fun _ : Fin l ↦ Finset.range b) := by
  exact fun n hn ↦ Fintype.mem_piFinset.mpr fun _ ↦ Finset.mem_range.mpr <| digitsFin_lt l n hb _

/--
The map from the set of natural numbers `< b ^ l` to the set of functions `Fin l → Finset.range b`
induced by `b.digitsFin l` is surjective.
-/
theorem digitsFin_surjOn (hb : 1 < b) :
    Set.SurjOn (digitsFin b l) (Finset.range (b ^ l))
      (Fintype.piFinset fun _ : Fin l ↦ Finset.range b) := by
  intro f hf
  refine ⟨ofDigits b (List.ofFn f), ?_, ?_⟩
  · rw [Finset.coe_range, Set.mem_Iio]
    convert Nat.ofDigits_lt_base_pow_length hb ?_
    · rw [length_ofFn]
    · grind [Fintype.coe_piFinset]
  · rw [← List.ofFn_inj]
    refine Nat.ofDigits_inj_of_len_eq hb (by simp) (by aesop) (by aesop) ?_
    rw [ofDigits_digitsFin _ _ hb]
    convert Nat.ofDigits_lt_base_pow_length hb (l := List.ofFn f) (by simpa using hf)
    rw [length_ofFn]

/--
The map `Nat.digitsFin l b` gives a bijection between the set of natural numbers `< b ^ l` and
the set of functions `Fin l → Finset.range b`.
-/
theorem digitsFin_bijOn (hb : 1 < b) :
    Set.BijOn (b.digitsFin l) (Finset.range (b ^ l))
      (Fintype.piFinset fun _ : Fin l ↦ Finset.range b) :=
  ⟨digitsFin_mapsTo l hb, digitsFin_injOn l hb, digitsFin_surjOn l hb⟩

/--
Formula for the sum of the sum of digits in base `b` of all natural integers `< b ^ l`.
-/
theorem sum_digits_sum_eq (hb : 1 < b) :
    ∑ x ∈ Finset.range (b ^ l), (b.digits x).sum = l * b ^ (l - 1) * (b * (b - 1) / 2) := by
  rw [Finset.sum_nbij (b.digitsFin l) (by exact b.digitsFin_mapsTo l hb)
    (Nat.digitsFin_injOn l hb) (Nat.digitsFin_surjOn l hb)
    (fun x hx ↦ (Nat.digitsFin_sum l x hb (List.mem_range.mp hx)).symm)]
  rw [Finset.sum_comm]
  simp_rw +contextual [fun i ↦ Finset.sum_comp
    (s := Fintype.piFinset fun x : Fin l ↦ Finset.range b) (f := fun x ↦ x) (g := fun x ↦ x i),
    Fintype.eval_image_piFinset_const, Fintype.card_filter_piFinset_const_eq_of_mem,
    Finset.card_range, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_range_id, Fintype.card_fin]
  ring

end Nat
