/-
Copyright (c) 2025 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Init.Data.List.Nat.Pairwise
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

## References

* <https://en.wikipedia.org/wiki/Sylvester%27s_sequence>
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

open Nat

/-- Sylvester's sequence: https://oeis.org/A000058. -/
def sylvester : ℕ → ℕ
  | 0 => 2
  | n + 1 => (sylvester n) * (sylvester n - 1) + 1

@[simp]
theorem sylvester_zero : sylvester 0 = 2 := rfl

@[simp]
theorem sylvester_one : sylvester 1 = 3 := rfl

@[simp]
theorem sylvester_two : sylvester 2 = 7 := rfl

@[simp]
theorem sylvester_three : sylvester 3 = 43 := rfl

theorem sylvester_ge_two (n : ℕ) : 2 ≤ sylvester n := by
  induction' n with n ih
  · simp
  · simp only [sylvester, reduceLeDiff]
    exact one_le_mul_of_one_le_of_one_le (by linarith) (by omega)

/--
This recurrence motivates the alternative name of **Euclid numbers**:
$$
\mathrm{sylvester}~n = 1 + \prod_{i=0}^{n-1} \mathrm{sylvester}~i,
$$
assuming the product over the empty set to be 1.
-/
theorem sylvester_prod_finset_add_one {n : ℕ} :
    sylvester n = ∏ i ∈ Finset.range n, sylvester i + 1 := by
  rw [Finset.prod_range_induction _ (fun n => sylvester n - 1)]
  · exact (Nat.sub_one_add_one (by linarith [sylvester_ge_two n])).symm
  · norm_num
  · simp [sylvester, mul_comm]

theorem sylvester_strictMono : StrictMono sylvester := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [sylvester]
  calc
    sylvester n * (sylvester n - 1) + 1 > sylvester n * (sylvester n - 1) := by linarith
    _ ≥ sylvester n := Nat.le_mul_of_pos_right _ <| le_sub_one_of_lt <| sylvester_ge_two n

-- Coprimality

theorem sylvester_mod_eq_one {m n : ℕ} (h : m < n) :
    sylvester n % sylvester m = 1 := by
  rw [sylvester_prod_finset_add_one, ← mod_add_mod,
    dvd_iff_mod_eq_zero.mp (Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr h)]
  exact Nat.mod_eq_of_lt <| sylvester_ge_two _

private theorem sylvester_coprime_of_lt {m n : ℕ} (h : m < n) :
    Coprime (sylvester m) (sylvester n) := by
  rw [Coprime, Nat.gcd_rec, sylvester_mod_eq_one h, gcd_one_left]

theorem sylvester_coprime {m n : ℕ} (h : m ≠ n) : Coprime (sylvester m) (sylvester n) := by
  rcases h.lt_or_lt with c | c
  · exact sylvester_coprime_of_lt c
  · exact (sylvester_coprime_of_lt c).symm

-- Explicit formula

/-
These two auxiliary sequences converge (from below and from above, respectively) to the constant
that appears in the explicit formula for the Sylvester sequence.
-/
private noncomputable def sylvesterBelow (n : ℕ) : ℝ :=
  (sylvester n - 2⁻¹) ^ (((2 : ℝ) ^ (n + 1))⁻¹)
private noncomputable def sylvesterAbove (n : ℕ) : ℝ :=
  (sylvester n + 2⁻¹) ^ (((2 : ℝ) ^ (n + 1))⁻¹)

private theorem rsylvester_gt_one (n : ℕ) : (1 : ℝ) < sylvester n :=
  Nat.one_lt_cast.mpr <| sylvester_ge_two n

private theorem sylvesterBelow_pos (n : ℕ) : 0 < sylvesterBelow n :=
  Real.rpow_pos_of_pos (by linarith [rsylvester_gt_one n]) _

private theorem sylvesterBelow_monotone : Monotone sylvesterBelow := by
  refine monotone_nat_of_le_succ ?h
  intro m
  let ha := rsylvester_gt_one m
  let hb := rsylvester_gt_one (m + 1)
  simp only [sylvesterBelow]
  refine le_of_pow_le_pow_left₀ ((by simp) : 2 ^ (m + 1 + 1) ≠ 0) ?_ ?_
  · exact Real.rpow_nonneg (by linarith) _
  · repeat rw [← Real.rpow_mul_natCast (by linarith) _]
    push_cast
    rw [inv_mul_cancel_of_invertible, mul_comm, ← pow_sub₀, Nat.add_sub_cancel_left,
      pow_one, Real.rpow_one, Real.rpow_two, sylvester] <;> try linarith
    have h : 1 < sylvester m := sylvester_ge_two _
    push_cast [h]
    rw [sub_sq]
    ring_nf
    linarith

private theorem sylvesterAbove_strictAnti : StrictAnti sylvesterAbove := by
  refine strictAnti_nat_of_succ_lt ?h
  intro m
  let ha := rsylvester_gt_one m
  let hb := rsylvester_gt_one (m + 1)
  simp only [sylvesterAbove]
  refine lt_of_pow_lt_pow_left₀ (2 ^ (m + 1 + 1)) (by positivity) ?_
  repeat rw [← Real.rpow_mul_natCast (by linarith) _]
  push_cast
  rw [inv_mul_cancel_of_invertible, mul_comm, ← pow_sub₀, Nat.add_sub_cancel_left,
    pow_one, Real.rpow_one, Real.rpow_two, sylvester] <;> try linarith
  have h : 1 < sylvester m := sylvester_ge_two _
  push_cast [h]
  rw [add_sq]
  ring_nf
  linarith

private theorem sylvesterBelow_le_sylvesterAbove (n m : ℕ) :
    sylvesterBelow n ≤ sylvesterAbove m := by
  trans sylvesterBelow (n ⊔ m)
  · exact sylvesterBelow_monotone <| Nat.le_max_left n m
  · trans sylvesterAbove (n ⊔ m)
    · rw [sylvesterBelow, sylvesterAbove]
      gcongr
      all_goals linarith [rsylvester_gt_one (n ⊔ m)]
    · exact StrictAnti.antitone sylvesterAbove_strictAnti <| Nat.le_max_right n m

/--
The constant that gives an explicit formula for the Sylvester sequence:
$$
\mathrm{sylvester}~n = \left\lfloor\mathrm{sylvesterConstant}^{2^{n+1}} +
  \frac{1}{2}\right\rfloor,
$$
for all natural $n$. The constant is approximately $1.2640847\ldots$.
-/
noncomputable def sylvesterConstant : ℝ := ⨆ i, sylvesterBelow i

private theorem sylvesterBelow_bddAbove : BddAbove (Set.range sylvesterBelow) := by
  use sylvesterAbove 0
  intro _ h
  obtain ⟨z, hz⟩ := h
  linarith [sylvesterBelow_le_sylvesterAbove z 0]

theorem sylvesterConstant_pos : 0 < sylvesterConstant := by
  suffices h : sylvesterBelow 0 ≤ sylvesterConstant by linarith [sylvesterBelow_pos 0]
  exact le_ciSup sylvesterBelow_bddAbove 0

private theorem sylvester_le_const_pow {n : ℕ} :
    sylvester n ≤ sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 := by
  suffices h : sylvesterBelow n ≤ sylvesterConstant by
    rw [← tsub_le_iff_right, one_div]
    exact_mod_cast (Real.rpow_inv_le_iff_of_pos (by linarith [rsylvester_gt_one n])
      (by linarith [sylvesterConstant_pos]) (by positivity)).mp h
  exact le_ciSup sylvesterBelow_bddAbove _

private theorem const_pow_lt_sylvester_add_one {n : ℕ} :
    sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2 < sylvester n + 1 := by
  suffices h : sylvesterConstant < sylvesterAbove n by
    rw [← lt_tsub_iff_right, add_sub_assoc, sub_self_div_two, one_div]
    exact_mod_cast (Real.lt_rpow_inv_iff_of_pos (by linarith [sylvesterConstant_pos])
      (by positivity) (by positivity)).mp h
  suffices h : sylvesterConstant ≤ sylvesterAbove (n + 1) by
    linarith [sylvesterAbove_strictAnti ((by linarith) : n < n + 1)]
  exact ciSup_le <| fun _ => sylvesterBelow_le_sylvesterAbove _ _

/--
Explicit formula for the Sylvester sequence:
$$
\mathrm{sylvester}~n = \left\lfloor\mathrm{sylvesterConstant}^{2^{n+1}} +
  \frac{1}{2}\right\rfloor,
$$
for all natural $n$.
-/
theorem sylvester_eq_floor_constant_pow {n : ℕ} :
    sylvester n = ⌊sylvesterConstant ^ (2 ^ (n + 1)) + 1 / 2⌋₊ := by
  refine ((Nat.floor_eq_iff ?h).mpr ?hb).symm
  · linarith [pow_pos sylvesterConstant_pos (2 ^ (n + 1))]
  · exact ⟨sylvester_le_const_pow, const_pow_lt_sylvester_add_one⟩
