/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sylvester's sequence

This file introduces the Sylvester's sequence.
This is sequence [A000058](https://oeis.org/A000058) in [oeis].

## Implementation notes

We follow the presentantion from [Wikipedia](https://en.wikipedia.org/wiki/Sylvester%27s_sequence).

## Main results

- Basic facts: the first terms of the sequence are 2, 3, 7, 43.
- `sylvester_prod_finset_add_one`: each term of the sequence is one plus the product of its
  predecessors.
- `sylvester_strictMono`: the sequence is strictly monotonic.
- `sylvester_coprime`: Pairwise co-primality.
- `sylvester_eq_floor_constant_pow`: explicit non-recursive formula.

## References

* <https://en.wikipedia.org/wiki/Sylvester%27s_sequence>
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

open Nat

/-- Sylvester's sequence: https://oeis.org/A000058. -/
def sylvesterSequence : ℕ → ℕ
  | 0 => 2
  | n + 1 => (sylvesterSequence n) * (sylvesterSequence n - 1) + 1

@[simp]
theorem sylvester_zero : sylvesterSequence 0 = 2 := rfl

@[simp]
theorem sylvester_one : sylvesterSequence 1 = 3 := rfl

@[simp]
theorem sylvester_two : sylvesterSequence 2 = 7 := rfl

@[simp]
theorem sylvester_three : sylvesterSequence 3 = 43 := rfl

theorem two_le_sylvester (n : ℕ) : 2 ≤ sylvesterSequence n := by
  induction' n with n ih
  · simp
  · simp only [sylvesterSequence, reduceLeDiff]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

/--
This recurrence motivates the alternative name of **Euclid numbers**:
$$
\mathrm{sylvester}~n = 1 + \prod_{i=0}^{n-1} \mathrm{sylvester}~i,
$$
assuming the product over the empty set to be 1.
-/
theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvesterSequence n = ∏ i ∈ Finset.range n, sylvesterSequence i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvesterSequence n - 1)]
  · exact (Nat.sub_one_add_one (by linarith [two_le_sylvester n])).symm
  · norm_num
  · simp [sylvesterSequence, mul_comm]

theorem sylvester_strictMono : StrictMono sylvesterSequence := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sylvesterSequence]
  calc
    sylvesterSequence n * (sylvesterSequence n - 1) + 1 >
      sylvesterSequence n * (sylvesterSequence n - 1) := by linarith
    _ ≥ sylvesterSequence n := Nat.le_mul_of_pos_right _ <| le_sub_one_of_lt <| two_le_sylvester n

/-!
### Coprimality
-/

theorem sylvester_mod_eq_one {m n : ℕ} (h : m < n) :
    sylvesterSequence n % sylvesterSequence m = 1 := by
  rw [sylvester_prod_finset_add_one, ← mod_add_mod,
    dvd_iff_mod_eq_zero.mp (Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr h)]
  exact Nat.mod_eq_of_lt <| two_le_sylvester _

private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvesterSequence m) (sylvesterSequence n) := by
  rw [Coprime, Nat.gcd_rec, sylvester_mod_eq_one h, gcd_one_left]

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) :
    Coprime (sylvesterSequence m) (sylvesterSequence n) := by
  rcases h.lt_or_lt with c | c
  · exact sylvester_coprime_of_lt c
  · exact (sylvester_coprime_of_lt c).symm

/-!
### Explicit formula
-/

-- These two auxiliary sequences converge (from below and from above, respectively) to the constant
-- that appears in the explicit formula for the Sylvester's sequence.
-- The strategy of the proof of `sylvester n = ⌊ E ^ (2 ^ (n + 1)) + 1 / 2 ⌋₀` is proving that
-- `sylvesterBelow n < sylvesterAbove m` for any `n`, and `m`, and then defining the constant `E`
-- as the limit of `sylvesterBelow n`.
private noncomputable def sylvesterBelow (n : ℕ) : ℝ :=
  (sylvester n - 2⁻¹) ^ (((2 : ℝ) ^ (n + 1))⁻¹)
private noncomputable def sylvesterAbove (n : ℕ) : ℝ :=
  (sylvester n + 2⁻¹) ^ (((2 : ℝ) ^ (n + 1))⁻¹)

private theorem cast_one_lt_sylvester (n : ℕ) : (1 : ℝ) < sylvester n :=
  Nat.one_lt_cast.mpr <| two_le_sylvester n

private theorem sylvesterBelow_pos (n : ℕ) : 0 < sylvesterBelow n :=
  Real.rpow_pos_of_pos (by linarith [cast_one_lt_sylvester n]) _

private theorem sylvesterBelow_monotone : Monotone sylvesterBelow := by
  refine monotone_nat_of_le_succ <| fun m ↦ ?_
  let ha := cast_one_lt_sylvester m
  let hb := cast_one_lt_sylvester (m + 1)
  dsimp only [sylvesterBelow]
  refine (Real.rpow_le_rpow_iff ?_ ?_ ((by positivity) : 0 < (2 : ℝ) ^ (m + 2))).mp ?_
  any_goals exact Real.rpow_nonneg (by linarith) _
  rw [← Real.rpow_mul, ← Real.rpow_mul, inv_mul_cancel_of_invertible, mul_comm, ← pow_sub₀,
    ← Nat.eq_sub_of_add_eq' (c := 1), pow_one, Real.rpow_one, sylvester, cast_add, cast_mul,
    cast_pred (by linarith [two_le_sylvester m]), Real.rpow_two] <;> linarith

private theorem sylvesterAbove_strictAnti : StrictAnti sylvesterAbove := by
  refine strictAnti_nat_of_succ_lt <| fun m ↦ ?_
  let ha := cast_one_lt_sylvester m
  let hb := cast_one_lt_sylvester (m + 1)
  simp only [sylvesterAbove]
  refine (Real.rpow_lt_rpow_iff ?_ ?_ ((by positivity) : 0 < (2 : ℝ) ^ (m + 2))).mp ?_
  any_goals exact Real.rpow_nonneg (by linarith) _
  rw [← Real.rpow_mul, ← Real.rpow_mul, inv_mul_cancel_of_invertible, mul_comm, ← pow_sub₀,
    ← Nat.eq_sub_of_add_eq' (c := 1), pow_one, Real.rpow_one, sylvester, cast_add, cast_mul,
    cast_pred (by linarith [two_le_sylvester m]), Real.rpow_two] <;> linarith

private theorem sylvesterBelow_le_sylvesterAbove (n m : ℕ) :
    sylvesterBelow n ≤ sylvesterAbove m := by
  trans sylvesterBelow (n ⊔ m)
  · exact sylvesterBelow_monotone <| Nat.le_max_left n m
  · trans sylvesterAbove (n ⊔ m)
    · rw [sylvesterBelow, sylvesterAbove]
      gcongr <;> linarith [cast_one_lt_sylvester (n ⊔ m)]
    · exact StrictAnti.antitone sylvesterAbove_strictAnti <| Nat.le_max_right n m

/--
The constant that gives an explicit formula for the Sylvester's sequence:
$$
\mathrm{sylvester}~n = \left\lfloor\mathrm{sylvesterConstant}^{2^{n+1}} +
  \frac{1}{2}\right\rfloor,
$$
for all natural $n$. The constant is approximately $1.2640847\ldots$.
-/
noncomputable def sylvesterConstant : ℝ := ⨆ i, sylvesterBelow i

private theorem sylvesterBelow_bddAbove : BddAbove (Set.range sylvesterBelow) := by
  use sylvesterAbove 0
  rintro _ ⟨z, _⟩
  linarith [sylvesterBelow_le_sylvesterAbove z 0]

theorem sylvesterConstant_pos : 0 < sylvesterConstant := by
  suffices h : sylvesterBelow 0 ≤ sylvesterConstant by linarith [sylvesterBelow_pos 0]
  exact le_ciSup sylvesterBelow_bddAbove 0

private theorem sylvester_le_const_pow {n : ℕ} :
    sylvester n ≤ sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 := by
  rw [← tsub_le_iff_right, one_div]
  exact_mod_cast (Real.rpow_inv_le_iff_of_pos (by linarith [cast_one_lt_sylvester n])
    (by linarith! [sylvesterConstant_pos]) (by positivity)).mp <| le_ciSup sylvesterBelow_bddAbove _

private theorem const_pow_lt_sylvester_add_one {n : ℕ} :
    sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 < sylvester n + 1 := by
  rw [← lt_tsub_iff_right, add_sub_assoc, sub_self_div_two, one_div]
  exact_mod_cast (Real.lt_rpow_inv_iff_of_pos
    (by linarith! [sylvesterConstant_pos]) (by positivity) (by positivity)).mp
    <| lt_of_le_of_lt (ciSup_le (sylvesterBelow_le_sylvesterAbove · (n + 1)))
      (sylvesterAbove_strictAnti ((by linarith) : n < n + 1))

/--
Explicit formula for the Sylvester's sequence:
$$
\mathrm{sylvester}~n = \left\lfloor\mathrm{sylvesterConstant}^{2^{n+1}} +
  \frac{1}{2}\right\rfloor,
$$
for all natural $n$.
-/
theorem sylvester_eq_floor_constant_pow {n : ℕ} :
    sylvester n = ⌊sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2⌋₊ := by
  refine ((Nat.floor_eq_iff ?_).mpr ?_).symm
  · linarith [pow_pos sylvesterConstant_pos (2 ^ (n + 1))]
  · exact ⟨sylvester_le_const_pow, const_pow_lt_sylvester_add_one⟩
