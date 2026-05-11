/-
Copyright (c) 2026 Meta Platforms, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kiezun
-/
module

public import Mathlib.NumberTheory.SylvesterSchur.ErdosPowerBounds
public import Mathlib.NumberTheory.SylvesterSchur.ResidualLarge.ScaledTernaryBound

import Mathlib.Tactic.Linarith

/-!
# Central-offset bound for the Sylvester-Schur large residual estimate

This file contains the large residual estimate for the central-offset range
`k + n - 1 < 3 * n`.
-/

@[expose] public section

namespace Nat.SylvesterSchur
namespace Internal

private lemma central_layers_le_four_pow_of_lt_three_mul {n N : ℕ}
    (hn : 945 ≤ n) (_hNlo : 2 * n ≤ N) (hNlt : N < 3 * n) :
    (∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) ≤
      4 ^ (N / 3 + n / 15 + n / 5) := by
  have hsqrt : Nat.sqrt N ≤ n / 15 :=
    sqrt_le_div_fifteen_of_le_four_mul (by omega : 900 ≤ n) (by omega : N ≤ 4 * n)
  have hroot_log : Nat.nthRoot 3 N * Nat.log 2 N ≤ n / 5 :=
    nthRoot_three_mul_log_le_one_fifth_of_le_four_mul hn (by omega : N ≤ 4 * n)
  have hlayers := erdos_layers_le_four_pow_three_layers N (N / 3)
  calc
    (∏ j ∈ Finset.range (Nat.log 2 N),
        if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N))
        ≤ 4 ^ (N / 3 + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := hlayers
    _ ≤ 4 ^ (N / 3 + n / 15 + n / 5) := by
      apply Nat.pow_le_pow_right (by norm_num : 0 < 4)
      omega

/-- Large-`n` residual estimate in the central-offset range `k + n - 1 < 3 * n`. -/
lemma second_residual_large_central_offset_bound {n k : ℕ}
    (hn : 945 ≤ n) (hk : n < k) (hcentral : k + n - 1 < 3 * n) :
    n * (2 ^ (k - n - 1) *
      (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)),
        if j = 0 then primorial ((k + n - 1) / 3)
        else primorial (Nat.nthRoot (j + 1) (k + n - 1)))) <
      3 ^ (k - n - 1) * 4 ^ n := by
  let N := k + n - 1
  let i := k - n - 1
  let D := n / 128 + 1
  let E := N / 3 + n / 15 + n / 5
  have hNlo : 2 * n ≤ N := by
    dsimp [N]
    omega
  have hprod :
      (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N)) ≤
        4 ^ E := by
    dsimp [E]
    exact central_layers_le_four_pow_of_lt_three_mul hn hNlo (by simpa [N] using hcentral)
  have hnfac : n ≤ 4 ^ D := by
    dsimp [D]
    exact self_le_four_pow_div_one_twenty_eight_add_one (by omega : 512 ≤ n)
  have hleft :
      n * (2 ^ i *
        (∏ j ∈ Finset.range (Nat.log 2 N),
          if j = 0 then primorial (N / 3) else primorial (Nat.nthRoot (j + 1) N))) ≤
        4 ^ D * (2 ^ i * 4 ^ E) :=
    Nat.mul_le_mul hnfac (Nat.mul_le_mul_left (2 ^ i) hprod)
  have hexp : 2 * D + i + 2 * E < 19 * (i / 12) + 2 * n := by
    dsimp [D, E, i, N]
    omega
  have hright : 4 ^ D * (2 ^ i * 4 ^ E) < 3 ^ i * 4 ^ n :=
    four_pow_mul_two_pow_mul_four_pow_lt_three_pow_mul_four_pow hexp
  simpa [N, i] using hleft.trans_lt hright


end Internal
end Nat.SylvesterSchur
