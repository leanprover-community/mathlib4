/-
Copyright (c) 2021 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.LegendreSymbol

/-!
# Tests for `norm_num` extensions

Some tests of unported extensions are still commented out.
-/

-- set_option profiler true
-- set_option trace.profiler true
-- set_option trace.Tactic.norm_num true

-- coverage tests

example : Nat.sqrt 0 = 0 := by norm_num1
example : Nat.sqrt 1 = 1 := by norm_num1
example : Nat.sqrt 2 = 1 := by norm_num1
example : Nat.sqrt 3 = 1 := by norm_num1
example : Nat.sqrt 4 = 2 := by norm_num1
example : Nat.sqrt 8 = 2 := by norm_num1
example : Nat.sqrt 9 = 3 := by norm_num1
example : Nat.sqrt 10 = 3 := by norm_num1
example : Nat.sqrt 99 = 9 := by norm_num1
example : Nat.sqrt 100 = 10 := by norm_num1
example : Nat.sqrt 120 = 10 := by norm_num1
example : Nat.sqrt 121 = 11 := by norm_num1
example : Nat.sqrt 122 = 11 := by norm_num1
example : Nat.sqrt (123456^2) = 123456 := by norm_num1
example : Nat.sqrt (123456^2 + 123456) = 123456 := by norm_num1

theorem ex11 : Nat.Coprime 1 2 := by norm_num1
theorem ex12 : Nat.Coprime 2 1 := by norm_num1
theorem ex13 : ¬ Nat.Coprime 0 0 := by norm_num1
theorem ex14 : ¬ Nat.Coprime 0 3 := by norm_num1
theorem ex15 : ¬ Nat.Coprime 2 0 := by norm_num1
theorem ex16 : Nat.Coprime 2 3 := by norm_num1
theorem ex16' : Nat.Coprime 3 2 := by norm_num1
theorem ex17 : ¬ Nat.Coprime 2 4 := by norm_num1

theorem ex21 : Nat.gcd 1 2 = 1 := by norm_num1
theorem ex22 : Nat.gcd 2 1 = 1 := by norm_num1
theorem ex23 : Nat.gcd 0 0 = 0 := by norm_num1
theorem ex24 : Nat.gcd 0 3 = 3 := by norm_num1
theorem ex25 : Nat.gcd 2 0 = 2 := by norm_num1
theorem ex26 : Nat.gcd 2 3 = 1 := by norm_num1
theorem ex27 : Nat.gcd 2 4 = 2 := by norm_num1

theorem ex31 : Nat.lcm 1 2 = 2 := by norm_num1
theorem ex32 : Nat.lcm 2 1 = 2 := by norm_num1
theorem ex33 : Nat.lcm 0 0 = 0 := by norm_num1
theorem ex34 : Nat.lcm 0 3 = 0 := by norm_num1
theorem ex35 : Nat.lcm 2 0 = 0 := by norm_num1
theorem ex36 : Nat.lcm 2 3 = 6 := by norm_num1
theorem ex37 : Nat.lcm 2 4 = 4 := by norm_num1

theorem ex41 : Int.gcd 2 3 = 1 := by norm_num1
theorem ex42 : Int.gcd (-2) 3 = 1 := by norm_num1
theorem ex43 : Int.gcd 2 (-3) = 1 := by norm_num1
theorem ex44 : Int.gcd (-2) (-3) = 1 := by norm_num1

theorem ex51 : Int.lcm 2 3 = 6 := by norm_num1
theorem ex52 : Int.lcm (-2) 3 = 6 := by norm_num1
theorem ex53 : Int.lcm 2 (-3) = 6 := by norm_num1
theorem ex54 : Int.lcm (-2) (-3) = 6 := by norm_num1

theorem ex61 : Nat.gcd (553105253 * 776531401) (553105253 * 920419823) = 553105253 := by norm_num1
theorem ex62 : Nat.gcd (2^1000 - 1) (2^1001 - 1) = 1 := by norm_num1
theorem ex62' : Nat.gcd (2^1001 - 1) (2^1000 - 1) = 1 := by norm_num1
theorem ex63 : Nat.gcd (2^500 - 1) (2^510 - 1) = 2^10 - 1 := by norm_num1
theorem ex64 : Int.gcd (1 - 2^500) (2^510 - 1) = 2^10 - 1 := by norm_num1
theorem ex64' : Int.gcd (1 - 2^500) (2^510 - 1) + 1 = 2^10 := by norm_num1

example : IsCoprime (1 : ℤ) 2 := by norm_num1
example : IsCoprime (2 : ℤ) 1 := by norm_num1
example : ¬ IsCoprime (0 : ℤ) 0 := by norm_num1
example : ¬ IsCoprime (0 : ℤ) 3 := by norm_num1
example : ¬ IsCoprime (2 : ℤ) 0 := by norm_num1
example : IsCoprime (2 : ℤ) 3 := by norm_num1
example : IsCoprime (3 : ℤ) 2 := by norm_num1
example : ¬ IsCoprime (2 : ℤ) 4 := by norm_num1

example : ¬ Nat.Prime 0 := by norm_num1
example : ¬ Nat.Prime 1 := by norm_num1
example : Nat.Prime 2 := by norm_num1
example : Nat.Prime 3 := by norm_num1
example : ¬ Nat.Prime 4 := by norm_num1
example : Nat.Prime 5 := by norm_num1
example : Nat.Prime 109 := by norm_num1
example : Nat.Prime 1277 := by norm_num1
example : ¬ Nat.Prime (10 ^ 1000) := by norm_num1
example : Nat.Prime (2 ^ 19 - 1) := by norm_num1
set_option maxRecDepth 8000 in
example : Nat.Prime (2 ^ 25 - 39) := by norm_num1
example : ¬ Nat.Prime ((2 ^ 19 - 1) * (2 ^ 25 - 39)) := by norm_num1

example : Nat.minFac 0 = 2 := by norm_num1
example : Nat.minFac 1 = 1 := by norm_num1
example : Nat.minFac (9 - 7) = 2 := by norm_num1
example : Nat.minFac 3 = 3 := by norm_num1
example : Nat.minFac 4 = 2 := by norm_num1
example : Nat.minFac 121 = 11 := by norm_num1
example : Nat.minFac 221 = 13 := by norm_num1
example : Nat.minFac (2 ^ 19 - 1) = 2 ^ 19 - 1 := by norm_num1

/-
example : Nat.factors 0 = [] := by norm_num1
example : Nat.factors 1 = [] := by norm_num1
example : Nat.factors 2 = [2] := by norm_num1
example : Nat.factors 3 = [3] := by norm_num1
example : Nat.factors 4 = [2, 2] := by norm_num1
example : Nat.factors 12 = [2, 2, 3] := by norm_num1
example : Nat.factors 221 = [13, 17] := by norm_num1
-/

-- randomized tests
example : Nat.gcd 35 29 = 1 := by norm_num1
example : Int.gcd 35 29 = 1 := by norm_num1
example : Nat.lcm 35 29 = 1015 := by norm_num1
example : Int.gcd 35 29 = 1 := by norm_num1
example : Nat.Coprime 35 29 := by norm_num1

example : Nat.gcd 80 2 = 2 := by norm_num1
example : Int.gcd 80 2 = 2 := by norm_num1
example : Nat.lcm 80 2 = 80 := by norm_num1
example : Int.gcd 80 2 = 2 := by norm_num1
example : ¬ Nat.Coprime 80 2 := by norm_num1

example : Nat.gcd 19 17 = 1 := by norm_num1
example : Int.gcd 19 17 = 1 := by norm_num1
example : Nat.lcm 19 17 = 323 := by norm_num1
example : Int.gcd 19 17 = 1 := by norm_num1
example : Nat.Coprime 19 17 := by norm_num1

example : Nat.gcd 11 18 = 1 := by norm_num1
example : Int.gcd 11 18 = 1 := by norm_num1
example : Nat.lcm 11 18 = 198 := by norm_num1
example : Int.gcd 11 18 = 1 := by norm_num1
example : Nat.Coprime 11 18 := by norm_num1

example : Nat.gcd 23 73 = 1 := by norm_num1
example : Int.gcd 23 73 = 1 := by norm_num1
example : Nat.lcm 23 73 = 1679 := by norm_num1
example : Int.gcd 23 73 = 1 := by norm_num1
example : Nat.Coprime 23 73 := by norm_num1

example : Nat.gcd 73 68 = 1 := by norm_num1
example : Int.gcd 73 68 = 1 := by norm_num1
example : Nat.lcm 73 68 = 4964 := by norm_num1
example : Int.gcd 73 68 = 1 := by norm_num1
example : Nat.Coprime 73 68 := by norm_num1

example : Nat.gcd 28 16 = 4 := by norm_num1
example : Int.gcd 28 16 = 4 := by norm_num1
example : Nat.lcm 28 16 = 112 := by norm_num1
example : Int.gcd 28 16 = 4 := by norm_num1
example : ¬ Nat.Coprime 28 16 := by norm_num1

example : Nat.gcd 44 98 = 2 := by norm_num1
example : Int.gcd 44 98 = 2 := by norm_num1
example : Nat.lcm 44 98 = 2156 := by norm_num1
example : Int.gcd 44 98 = 2 := by norm_num1
example : ¬ Nat.Coprime 44 98 := by norm_num1

example : Nat.gcd 21 79 = 1 := by norm_num1
example : Int.gcd 21 79 = 1 := by norm_num1
example : Nat.lcm 21 79 = 1659 := by norm_num1
example : Int.gcd 21 79 = 1 := by norm_num1
example : Nat.Coprime 21 79 := by norm_num1

example : Nat.gcd 93 34 = 1 := by norm_num1
example : Int.gcd 93 34 = 1 := by norm_num1
example : Nat.lcm 93 34 = 3162 := by norm_num1
example : Int.gcd 93 34 = 1 := by norm_num1
example : Nat.Coprime 93 34 := by norm_num1

example : ¬ Nat.Prime 912 := by norm_num1
example : Nat.minFac 912 = 2 := by norm_num1
-- example : Nat.factors 912 = [2, 2, 2, 2, 3, 19] := by norm_num1

example : ¬ Nat.Prime 681 := by norm_num1
example : Nat.minFac 681 = 3 := by norm_num1
-- example : Nat.factors 681 = [3, 227] := by norm_num1

example : ¬ Nat.Prime 728 := by norm_num1
example : Nat.minFac 728 = 2 := by norm_num1
-- example : Nat.factors 728 = [2, 2, 2, 7, 13] := by norm_num1

example : ¬ Nat.Prime 248 := by norm_num1
example : Nat.minFac 248 = 2 := by norm_num1
-- example : Nat.factors 248 = [2, 2, 2, 31] := by norm_num1

example : ¬ Nat.Prime 682 := by norm_num1
example : Nat.minFac 682 = 2 := by norm_num1
-- example : Nat.factors 682 = [2, 11, 31] := by norm_num1

example : ¬ Nat.Prime 115 := by norm_num1
example : Nat.minFac 115 = 5 := by norm_num1
-- example : Nat.factors 115 = [5, 23] := by norm_num1

example : ¬ Nat.Prime 824 := by norm_num1
example : Nat.minFac 824 = 2 := by norm_num1
-- example : Nat.factors 824 = [2, 2, 2, 103] := by norm_num1

example : ¬ Nat.Prime 942 := by norm_num1
example : Nat.minFac 942 = 2 := by norm_num1
-- example : Nat.factors 942 = [2, 3, 157] := by norm_num1

example : ¬ Nat.Prime 34 := by norm_num1
example : Nat.minFac 34 = 2 := by norm_num1
-- example : Nat.factors 34 = [2, 17] := by norm_num1

example : ¬ Nat.Prime 754 := by norm_num1
example : Nat.minFac 754 = 2 := by norm_num1
-- example : Nat.factors 754 = [2, 13, 29] := by norm_num1

example : ¬ Nat.Prime 663 := by norm_num1
example : Nat.minFac 663 = 3 := by norm_num1
-- example : Nat.factors 663 = [3, 13, 17] := by norm_num1

example : ¬ Nat.Prime 923 := by norm_num1
example : Nat.minFac 923 = 13 := by norm_num1
-- example : Nat.factors 923 = [13, 71] := by norm_num1

example : ¬ Nat.Prime 77 := by norm_num1
example : Nat.minFac 77 = 7 := by norm_num1
-- example : Nat.factors 77 = [7, 11] := by norm_num1

example : ¬ Nat.Prime 162 := by norm_num1
example : Nat.minFac 162 = 2 := by norm_num1
-- example : Nat.factors 162 = [2, 3, 3, 3, 3] := by norm_num1

example : ¬ Nat.Prime 669 := by norm_num1
example : Nat.minFac 669 = 3 := by norm_num1
-- example : Nat.factors 669 = [3, 223] := by norm_num1

example : ¬ Nat.Prime 476 := by norm_num1
example : Nat.minFac 476 = 2 := by norm_num1
-- example : Nat.factors 476 = [2, 2, 7, 17] := by norm_num1

example : Nat.Prime 251 := by norm_num1
example : Nat.minFac 251 = 251 := by norm_num1
-- example : Nat.factors 251 = [251] := by norm_num1

example : ¬ Nat.Prime 129 := by norm_num1
example : Nat.minFac 129 = 3 := by norm_num1
-- example : Nat.factors 129 = [3, 43] := by norm_num1

example : ¬ Nat.Prime 471 := by norm_num1
example : Nat.minFac 471 = 3 := by norm_num1
-- example : Nat.factors 471 = [3, 157] := by norm_num1

example : ¬ Nat.Prime 851 := by norm_num1
example : Nat.minFac 851 = 23 := by norm_num1
-- example : Nat.factors 851 = [23, 37] := by norm_num1

/-
example : ¬ squarefree 0 := by norm_num
example : squarefree 1 := by norm_num
example : squarefree 2 := by norm_num
example : squarefree 3 := by norm_num
example : ¬ squarefree 4 := by norm_num
example : squarefree 5 := by norm_num
example : squarefree 6 := by norm_num
example : squarefree 7 := by norm_num
example : ¬ squarefree 8 := by norm_num
example : ¬ squarefree 9 := by norm_num
example : squarefree 10 := by norm_num
example : squarefree (2*3*5*17) := by norm_num
example : ¬ squarefree (2*3*5*5*17) := by norm_num
example : squarefree 251 := by norm_num
example : squarefree (3 : ℤ) :=
begin
  -- `norm_num` should fail on this example, instead of producing an incorrect proof.
  success_if_fail { norm_num },
  exact irreducible.squarefree (prime.irreducible
    (Int.prime_iff_Nat_abs_prime.mpr (by norm_num)))
end
example : @squarefree ℕ multiplicative.monoid 1 :=
begin
  -- `norm_num` should fail on this example, instead of producing an incorrect proof.
  success_if_fail { norm_num },
  -- the statement was deliberately wacky, let's fix it
  change squarefree (multiplicative.of_add 1 : multiplicative ℕ),
  rIntros x ⟨dx, hd⟩,
  revert x dx,
  rw multiplicative.of_add.surjective.forall₂,
  Intros x dx h,
  simp_rw [←of_add_add, multiplicative.of_add.injective.eq_iff] at h,
  cases x,
  { simp [is_unit_one], exact is_unit_one },
  { simp only [Nat.succ_add, Nat.add_succ] at h,
    cases h },
end
-/

example : Nat.fib 0 = 0 := by norm_num1
example : Nat.fib 1 = 1 := by norm_num1
example : Nat.fib 2 = 1 := by norm_num1
example : Nat.fib 3 = 2 := by norm_num1
example : Nat.fib 4 = 3 := by norm_num1
example : Nat.fib 5 = 5 := by norm_num1
example : Nat.fib 6 = 8 := by norm_num1
example : Nat.fib 7 = 13 := by norm_num1
example : Nat.fib 8 = 21 := by norm_num1
example : Nat.fib 9 = 34 := by norm_num1
example : Nat.fib 10 = 55 := by norm_num1
example : Nat.fib 37 = 24157817 := by norm_num1
example : Nat.fib 63 = 6557470319842 := by norm_num1
example : Nat.fib 64 = 10610209857723 := by norm_num1
example : Nat.fib 65 = 17167680177565 := by norm_num1
example : Nat.fib 100 + Nat.fib 101 = Nat.fib 102 := by norm_num1
example : Nat.fib 1000 + Nat.fib 1001 = Nat.fib 1002 := by norm_num1

/-
example : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
example : (1 : ℝ) ^ (20 : ℝ) = 1 := by norm_num
example : (2 : ℝ) ^ (-3 : ℝ) = 1/8 := by norm_num
-/

section big_operators

variable {α : Type _} [CommRing α]

open BigOperators

-- Lists:
example : ([1, 2, 1, 3]).sum = 7 := by norm_num only
-- example : (([1, 2, 1, 3] : List ℚ).map (fun i => i^2)).sum = 15 := by norm_num [-List.map] --TODO
example : (List.range 10).sum = 45 := by norm_num only
example : (List.finRange 10).sum = 45 := by norm_num only

-- Multisets:
example : (1 ::ₘ 2 ::ₘ 1 ::ₘ 3 ::ₘ {}).sum = 7 := by norm_num only
example : ((1 ::ₘ 2 ::ₘ 1 ::ₘ 3 ::ₘ {}).map (fun i => i^2)).sum = 15 := by norm_num only
-- example : (({1, 2, 1, 3} : Multiset ℚ).map (fun i => i^2)).sum = 15 := by -- TODO
--   norm_num [-Multiset.map_cons]
example : (Multiset.range 10).sum = 45 := by norm_num only
example : (↑[1, 2, 1, 3] : Multiset ℕ).sum = 7 := by norm_num only

-- Finsets:
example : Finset.prod (Finset.cons 2 ∅ (Finset.not_mem_empty _)) (λ x => x) = 2 := by norm_num1
example : Finset.prod
    (Finset.cons 6 (Finset.cons 2 ∅ (Finset.not_mem_empty _)) (by norm_num))
    (λ x => x) =
  12 := by norm_num1

example (f : ℕ → α) : ∏ i in Finset.range 0, f i = 1 := by norm_num1
example (f : Fin 0 → α) : ∏ i : Fin 0, f i = 1 := by norm_num1
example (f : Fin 0 → α) : ∑ i : Fin 0, f i = 0 := by norm_num1
example (f : ℕ → α) : ∑ i in (∅ : Finset ℕ), f i = 0 := by norm_num1
example : ∑ i : Fin 3, 1 = 3 := by norm_num1
/-
example : ∑ i : Fin 3, (i : ℕ) = 3 := by norm_num1
example : ((0 : Fin 3) : ℕ) = 0 := by norm_num1
example (f : Fin 3 → α) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by norm_num <;> ring
example (f : Fin 4 → α) : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3 := by norm_num <;> ring
example (f : ℕ → α) : ∑ i in {0, 1, 2}, f i = f 0 + f 1 + f 2 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 2, 2, 3, 1, 0}, f i = f 0 + f 1 + f 2 + f 3 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 2, 2 - 3, 3 - 1, 1, 0}, f i = f 0 + f 1 + f 2 := by norm_num; ring
-/
example : (∑ i in Finset.range 10, (i^2 : ℕ)) = 285 := by norm_num1
example : (∏ i in Finset.range 4, ((i+1)^2 : ℕ)) = 576 := by norm_num1
/-
example : (∑ i in Finset.Icc 5 10, (i^2 : ℕ)) = 355 := by norm_num
example : (∑ i in Finset.Ico 5 10, (i^2 : ℕ)) = 255 := by norm_num
example : (∑ i in Finset.Ioc 5 10, (i^2 : ℕ)) = 330 := by norm_num
example : (∑ i in Finset.Ioo 5 10, (i^2 : ℕ)) = 230 := by norm_num
example : (∑ i : ℤ in Finset.Ioo (-5) 5, i^2) = 60 := by norm_num
example (f : ℕ → α) : ∑ i in Finset.mk {0, 1, 2} dec_trivial, f i = f 0 + f 1 + f 2 :=
  by norm_num; ring
-/

-- Combined with other `norm_num` extensions:
/-
example : ∏ i in Finset.range 9, Nat.sqrt (i + 1) = 96 := by norm_num1
example : ∏ i in {1, 4, 9, 16}, Nat.sqrt i = 24 := by norm_num1
example : ∏ i in Finset.Icc 0 8, Nat.sqrt (i + 1) = 96 := by norm_num1

-- Nested operations:
example : ∑ i : Fin 2, ∑ j : Fin 2, ![![0, 1], ![2, 3]] i j = 6 := by norm_num1
-/

end big_operators

section jacobi

-- Jacobi and Legendre symbols

open scoped NumberTheorySymbols

example : J(123 | 335) = -1 := by norm_num1
example : J(-2345 | 6789) = -1 := by norm_num1
example : J(-1 | 1655801) = 1 := by norm_num1
example : J(-102334155 | 165580141) = -1 := by norm_num1

example : J(58378362899022564339483801989973056405585914719065 |
            53974350278769849773003214636618718468638750007307) = -1 := by norm_num1

example : J(3 + 4 | 3 * 5) = -1 := by norm_num1
example : J(J(-1 | 7) | 11) = -1 := by norm_num1

instance prime_1000003 : Fact (Nat.Prime 1000003) := ⟨by norm_num1⟩
example : legendreSym 1000003 7 = -1 := by norm_num1

end jacobi
