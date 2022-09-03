/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Mario Carneiro
-/

import Mathlib.Tactic.NormNum

/-!
# Tests for `norm_num` extensions
-/

-- constant real : Type
-- notation `ℝ` := real
-- @[instance] constant real.linear_ordered_ring : linear_ordered_field ℝ

-- constant complex : Type
-- notation `ℂ` := complex
-- @[instance] constant complex.field : field ℂ
-- @[instance] constant complex.char_zero : char_zero ℂ

example : 374 + (32 - (2 * 8123) : ℤ) - 61 * 50 = 86 + 32 * 32 - 4 * 5000
      ∧ 43 ≤ 74 + (33 : ℤ) := by norm_num1; trivial -- [fixme] defeq doing the work not norm_num

-- example : ¬ (7-2)/(2*3) ≥ (1:ℝ) + 2/(3^2) := by norm_num
-- example : (6:real) + 9 = 15 := by norm_num
-- example : (2:real)/4 + 4 = 3*3/2 := by norm_num
-- example : (((3:real)/4)-12)<6 := by norm_num
-- example : (5:real) ≠ 8 := by norm_num
-- example : (10:real) > 7 := by norm_num
-- example : (2:real) * 2 + 3 = 7 := by norm_num
-- example : (6:real) < 10 := by norm_num
-- example : (7:real)/2 > 3 := by norm_num
-- example : (4:real)⁻¹ < 1 := by norm_num
-- example : ((1:real) / 2)⁻¹ = 2 := by norm_num
example : 2 ^ 17 - 1 = 131071 := by norm_num
-- example : (3 : real) ^ (-2 : ℤ) = 1/9 := by norm_num
-- example : (3 : real) ^ (-2 : ℤ) = 1/9 := by norm_num1
-- example : (-3 : real) ^ (0 : ℤ) = 1 := by norm_num
-- example : (-3 : real) ^ (-1 : ℤ) = -1/3 := by norm_num
-- example : (-3 : real) ^ (2 : ℤ) = 9 := by norm_num

-- example : (1:complex) ≠ 2 := by norm_num
-- example : (1:complex) / 3 ≠ 2 / 7 := by norm_num

-- example : (1:real) ≠ 2 := by norm_num

-- example {α} [Semiring α] : (1:α) ≠ 2 := by norm_num -- [fixme]
-- example {α} [Ring α] : (-1:α) ≠ 2 := by norm_num -- [fixme]
-- example {α} [division_ring α] [char_zero α] : (-1:α) ≠ 2 := by norm_num
-- example {α} [division_ring α] [char_zero α] : (1:α) / 3 ≠ 2 / 7 := by norm_num
-- example {α} [division_ring α] [char_zero α] : (1:α) / 3 ≠ 0 := by norm_num

example : (5 / 2:ℕ) = 2 := by norm_num
example : (5 / -2:ℤ) < -1 := by norm_num
example : (0 + 1) / 2 < 0 + 1 := by norm_num
example : Nat.succ (Nat.succ (2 ^ 3)) = 10 := by norm_num
-- example : 10 = (-1 : ℤ) % 11 := by norm_num -- [fixme] ⊢ False ???
example : (12321 - 2 : ℤ) = 12319 := by norm_num
-- example : (63:ℚ) ≥ 5 := by norm_num

example (x : ℤ) (h : 1000 + 2000 < x) : 100 * 30 < x :=
by norm_num at *; exact h

example : (1103 : ℤ) ≤ (2102 : ℤ) := by norm_num
example : (110474 : ℤ) ≤ (210485 : ℤ) := by norm_num
example : (11047462383473829263 : ℤ) ≤ (21048574677772382462 : ℤ) := by norm_num
example : (210485742382937847263 : ℤ) ≤ (1104857462382937847262 : ℤ) := by norm_num
example : (210485987642382937847263 : ℕ) ≤ (11048512347462382937847262 : ℕ) := by norm_num
-- example : (210485987642382937847263 : ℚ) ≤ (11048512347462382937847262 : ℚ) := by norm_num
example : (2 * 12868 + 25705) * 11621 ^ 2 ≤ 23235 ^ 2 * 12868 := by norm_num

-- example (x : ℕ) : ℕ := by
--   let n : ℕ, {apply_normed (2^32 - 71)},
--   exact n


-- example (a : ℚ) (h : 3⁻¹ * a = a) : true :=
-- begin
--   norm_num at h,
--   guard_hyp h : 1 / 3 * a = a,
--   trivial
-- end

-- example (h : (5 : ℤ) ∣ 2) : false := by norm_num at h
-- example (h : false) : false := by norm_num at h
example : true := by norm_num
example : true ∧ true := by norm_num

example : 10 + 2 = 1 + 11 := by norm_num

example : 10 - 1 = 9 := by norm_num
example : 12 - 5 = 3 + 4 := by norm_num
example : 5 - 20 = 0 := by norm_num
example : 0 - 2 = 0 := by norm_num
example : 4 - (5 - 10) = 2 + (3 - 1) := by norm_num
example : 0 - 0 = 0 := by norm_num
example : 100 - 100 = 0 := by norm_num
example : 5 * (2 - 3) = 0 := by norm_num
example : 10 - 5 * 5 + (7 - 3) * 6 = 27 - 3 := by norm_num

def foo : ℕ := 1

example : foo = 1 := by norm_num

section
  variable (α : Type u) [Semiring α]
  example : (1 + 0 : α) = (0 + 1 : α) := by norm_num
  example : (0 + (2 + 3) + 1 : α) = 6 := by norm_num
  example : (70 * (33 + 2) : α) = 2450 := by norm_num
  example : (8 + 2 ^ 2 * 3 : α) = 20 := by norm_num
  example : ((2 * 1 + 1) ^ 2 : α) = (3 * 3 : α) := by norm_num
end
section
  variable {α : Type}
  variable [Ring α]

  -- example : (-1 :α) * 1 = -1 := by norm_num -- [fixme] support subtraction
  -- example : (-2 :α) * 1 = -2 := by norm_num -- [fixme]
  -- example : (-2 :α) * -1 = 2 := by norm_num -- [fixme]
  -- example : (-2 :α) * -2 = 4 := by norm_num -- [fixme]
  example : (1 : α) * 0 = 0 := by norm_num

  example : ((1 : α) + 1) * 5 = 6 + 4 := by norm_num

  example : (1 : α) = 0 + 1 := by norm_num
  example : (1 : α) = 1 + 0 := by norm_num
  example : (2 : α) = 1 + 1 := by norm_num
  example : (2 : α) = 0 + 2 := by norm_num
  example : (3 : α) = 1 + 2 := by norm_num
  example : (3 : α) = 2 + 1 := by norm_num
  example : (4 : α) = 3 + 1 := by norm_num
  example : (4 : α) = 2 + 2 := by norm_num
  example : (5 : α) = 4 + 1 := by norm_num
  example : (5 : α) = 3 + 2 := by norm_num
  example : (5 : α) = 2 + 3 := by norm_num
  example : (6 : α) = 0 + 6 := by norm_num
  example : (6 : α) = 3 + 3 := by norm_num
  example : (6 : α) = 4 + 2 := by norm_num
  example : (6 : α) = 5 + 1 := by norm_num
  example : (7 : α) = 4 + 3 := by norm_num
  example : (7 : α) = 1 + 6 := by norm_num
  example : (7 : α) = 6 + 1 := by norm_num
  example : 33 = 5 + (28 : α) := by norm_num

  example : (12 : α) = 0 + (2 + 3) + 7 := by norm_num
  example : (105 : α) = 70 + (33 + 2) := by norm_num

  example : (45000000000 : α) = 23000000000 + 22000000000 := by norm_num

  -- [fixme] needs to support subtraction.
  -- example : (0 : α) - 3 = -3 := by norm_num
  -- example : (0 : α) - 2 = -2 := by norm_num
  -- example : (1 : α) - 3 = -2 := by norm_num
  -- example : (1 : α) - 1 = 0 := by norm_num
  -- example : (0 : α) - 3 = -3 := by norm_num
  -- example : (0 : α) - 3 = -3 := by norm_num
  -- example : (12 : α) - 4 - (5 + -2) = 5 := by norm_num
  -- example : (12 : α) - 4 - (5 + -2) - 20 = -15 := by norm_num

  example : (0 : α) * 0 = 0 := by norm_num
  example : (0 : α) * 1 = 0 := by norm_num
  example : (0 : α) * 2 = 0 := by norm_num
  example : (2 : α) * 0 = 0 := by norm_num
  example : (1 : α) * 0 = 0 := by norm_num
  example : (1 : α) * 1 = 1 := by norm_num
  example : (2 : α) * 1 = 2 := by norm_num
  example : (1 : α) * 2 = 2 := by norm_num
  example : (2 : α) * 2 = 4 := by norm_num
  example : (3 : α) * 2 = 6 := by norm_num
  example : (2 : α) * 3 = 6 := by norm_num
  example : (4 : α) * 1 = 4 := by norm_num
  example : (1 : α) * 4 = 4 := by norm_num
  example : (3 : α) * 3 = 9 := by norm_num
  example : (3 : α) * 4 = 12 := by norm_num
  example : (4 : α) * 4 = 16 := by norm_num
  example : (11 : α) * 2 = 22 := by norm_num
  example : (15 : α) * 6 = 90 := by norm_num
  example : (123456 : α) * 123456 = 15241383936 := by norm_num
end

-- section
--   variable {α : Type}
--   variable [LinearOrderedField α]
--   example : (4 : α) / 2 = 2 := by norm_num
--   example : (4 : α) / 1 = 4 := by norm_num
--   example : (4 : α) / 3 = 4 / 3 := by norm_num
--   example : (50 : α) / 5 = 10 := by norm_num
--   example : (1056 : α) / 1 = 1056 := by norm_num
--   example : (6 : α) / 4 = 3/2 := by norm_num
--   example : (0 : α) / 3 = 0 := by norm_num
--   example : (3 : α) / 0 = 0 := by norm_num
--   example : (9 * 9 * 9) * (12 : α) / 27 = 81 * (2 + 2) := by norm_num
--   example : (-2 : α) * 4 / 3 = -8 / 3 := by norm_num
--   example : - (-4 / 3) = 1 / (3 / (4 : α)) := by norm_num
-- end

-- user command

-- #norm_num 1 = 1
example : 1 = 1 := by norm_num
-- #norm_num 2^4-1 ∣ 2^16-1
example : 2^4-1 ∣ 2^16-1 := by norm_num
-- #norm_num (3 : real) ^ (-2 : ℤ) = 1/9
-- example : (3 : real) ^ (-2 : ℤ) = 1/9 := by norm_num

section norm_num_cmd_variable

-- [fixme] obsolete?
-- variables (x y : ℕ)
-- #norm_num bit0 x < bit0 (y + x) ↔ 0 < y
-- example : bit0 x < bit0 (y + x) ↔ 0 < y := by norm_num
-- #norm_num bit0 x < bit0 (y + (2^10%11 - 1) + x) ↔ 0 < y
-- example : bit0 x < bit0 (y + (2^10%11 - 1) + x) ↔ 0 < y := by norm_num
-- #norm_num bit0 x < bit0 (y + (2^10%11 - 1) + x) + 3*2-6 ↔ 0 < y
-- example : bit0 x < bit0 (y + (2^10%11 - 1) + x) + 3*2-6 ↔ 0 < y := by norm_num

end norm_num_cmd_variable

-- auto gen tests
-- example : ((25 * (1 / 1)) + (30 - 16)) = (39 : α) := by norm_num
-- example : ((19 * (- 2 - 3)) / 6) = (-95/6 : α) := by norm_num
-- example : - (3 * 28) = (-84 : α) := by norm_num
-- example : - - (16 / ((11 / (- - (6 * 19) + 12)) * 21)) = (96/11 : α) := by norm_num
-- example : (- (- 21 + 24) - - (- - (28 + (- 21 / - (16 / ((1 * 26) * ((0 * - 11) + 13))))) * 21)) =
--   (79209/8 : α) := by norm_num
-- example : (27 * (((16 + - (12 + 4)) + (22 - - 19)) - 23)) = (486 : α) := by norm_num
-- example : - (13 * (- 30 / ((7 / 24) + - 7))) = (-9360/161 : α) := by norm_num
-- example : - (0 + 20) = (-20 : α) := by norm_num
-- example : (- 2 - (27 + (((2 / 14) - (7 + 21)) + (16 - - - 14)))) = (-22/7 : α) := by norm_num
-- example : (25 + ((8 - 2) + 16)) = (47 : α) := by norm_num
-- example : (- - 26 / 27) = (26/27 : α) := by norm_num
-- example : ((((16 * (22 / 14)) - 18) / 11) + 30) = (2360/77 : α) := by norm_num
-- example : (((- 28 * 28) / (29 - 24)) * 24) = (-18816/5 : α) := by norm_num
-- example : ((- (18 - ((- - (10 + - 2) - - (23 / 5)) / 5)) - (21 * 22)) -
--   (((20 / - ((((19 + 18) + 15) + 3) + - 22)) + 14) / 17)) = (-394571/825 : α) := by norm_num
-- example : ((3 + 25) - - 4) = (32 : α) := by norm_num
-- example : ((1 - 0) - 22) = (-21 : α) := by norm_num
-- example : (((- (8 / 7) / 14) + 20) + 22) = (2054/49 : α) := by norm_num
-- example : ((21 / 20) - 29) = (-559/20 : α) := by norm_num
-- example : - - 20 = (20 : α) := by norm_num
-- example : (24 - (- 9 / 4)) = (105/4 : α) := by norm_num
-- example : (((7 / ((23 * 19) + (27 * 10))) - ((28 - - 15) * 24)) + (9 / - (10 * - 3))) =
--   (-1042007/1010 : α) := by norm_num
-- example : (26 - (- 29 + (12 / 25))) = (1363/25 : α) := by norm_num
-- example : ((11 * 27) / (4 - 5)) = (-297 : α) := by norm_num
-- example : (24 - (9 + 15)) = (0 : α) := by norm_num
-- example : (- 9 - - 0) = (-9 : α) := by norm_num
-- example : (- 10 / (30 + 10)) = (-1/4 : α) := by norm_num
-- example : (22 - (6 * (28 * - 8))) = (1366 : α) := by norm_num
-- example : ((- - 2 * (9 * - 3)) + (22 / 30)) = (-799/15 : α) := by norm_num
-- example : - (26 / ((3 + 7) / - (27 * (12 / - 16)))) = (-1053/20 : α) := by norm_num
-- example : ((- 29 / 1) + 28) = (-1 : α) := by norm_num
-- example : ((21 * ((10 - (((17 + 28) - - 0) + 20)) + 26)) + ((17 + - 16) * 7)) = (-602 : α) :=
-- by norm_num
-- example : (((- 5 - ((24 + - - 8) + 3)) + 20) + - 23) = (-43 : α) := by norm_num
-- example : ((- ((14 - 15) * (14 + 8)) + ((- (18 - 27) - 0) + 12)) - 11) = (32 : α) := by norm_num
-- example : (((15 / 17) * (26 / 27)) + 28) = (4414/153 : α) := by norm_num
-- example : (14 - ((- 16 - 3) * - (20 * 19))) = (-7206 : α) := by norm_num
-- example : (21 - - - (28 - (12 * 11))) = (125 : α) := by norm_num
-- example : ((0 + (7 + (25 + 8))) * - (11 * 27)) = (-11880 : α) := by norm_num
-- example : (19 * - 5) = (-95 : α) := by norm_num
-- example : (29 * - 8) = (-232 : α) := by norm_num
-- example : ((22 / 9) - 29) = (-239/9 : α) := by norm_num
-- example : (3 + (19 / 12)) = (55/12 : α) := by norm_num
-- example : - (13 + 30) = (-43 : α) := by norm_num
-- example : - - - (((21 * - - ((- 25 - (- (30 - 5) / (- 5 - 5))) /
--   (((6 + ((25 * - 13) + 22)) - 3) / 2))) / (- 3 / 10)) * (- 8 - 0)) = (-308/3 : α) := by norm_num
-- example : - (2 * - (- 24 * 22)) = (-1056 : α) := by norm_num
-- example : - - (((28 / - ((- 13 * - 5) / - (((7 - 30) / 16) + 6))) * 0) - 24) = (-24 : α) :=
-- by norm_num
-- example : ((13 + 24) - (27 / (21 * 13))) = (3358/91 : α) := by norm_num
-- example : ((3 / - 21) * 25) = (-25/7 : α) := by norm_num
-- example : (17 - (29 - 18)) = (6 : α) := by norm_num
-- example : ((28 / 20) * 15) = (21 : α) := by norm_num
-- example : ((((26 * (- (23 - 13) - 3)) / 20) / (14 - (10 + 20))) / ((16 / 6) / (16 * - (3 / 28)))) =
-- (-1521/2240 : α) := by norm_num

-- example : (46 / (- ((- 17 * 28) - 77) + 87)) = (23/320 : α) := by norm_num
-- example : (73 * - (67 - (74 * - - 11))) = (54531 : α) := by norm_num
-- example : ((8 * (25 / 9)) + 59) = (731/9 : α) := by norm_num
-- example : - ((59 + 85) * - 70) = (10080 : α) := by norm_num
-- example : (66 + (70 * 58)) = (4126 : α) := by norm_num
-- example : (- - 49 * 0) = (0 : α) := by norm_num
-- example : ((- 78 - 69) * 9) = (-1323 : α) := by norm_num
-- example : - - (7 - - (50 * 79)) = (3957 : α) := by norm_num
-- example : - (85 * (((4 * 93) * 19) * - 31)) = (18624180 : α) := by norm_num
-- example : (21 + (- 5 / ((74 * 85) / 45))) = (26373/1258 : α) := by norm_num
-- example : (42 - ((27 + 64) + 26)) = (-75 : α) := by norm_num
-- example : (- ((38 - - 17) + 86) - (74 + 58)) = (-273 : α) := by norm_num
-- example : ((29 * - (75 + - 68)) + (- 41 / 28)) = (-5725/28 : α) := by norm_num
-- example : (- - (40 - 11) - (68 * 86)) = (-5819 : α) := by norm_num
-- example : (6 + ((65 - 14) + - 89)) = (-32 : α) := by norm_num
-- example : (97 * - (29 * 35)) = (-98455 : α) := by norm_num
-- example : - (66 / 33) = (-2 : α) := by norm_num
-- example : - ((94 * 89) + (79 - (23 - (((- 1 / 55) + 95) * (28 - (54 / - - - 22)))))) =
-- (-1369070/121 : α) := by norm_num
-- example : (- 23 + 61) = (38 : α) := by norm_num
-- example : - (93 / 69) = (-31/23 : α) := by norm_num
-- example : (- - ((68 / (39 + (((45 * - (59 - (37 + 35))) / (53 - 75)) -
--  - (100 + - (50 / (- 30 - 59)))))) - (69 - (23 * 30))) / (57 + 17)) = (137496481/16368578 : α) :=
-- by norm_num
-- example : (- 19 * - - (75 * - - 41)) = (-58425 : α) := by norm_num
-- example : ((3 / ((- 28 * 45) * (19 + ((- (- 88 - (- (- 1 + 90) + 8)) + 87) * 48)))) + 1) =
--   (1903019/1903020 : α) := by norm_num
-- example : ((- - (28 + 48) / 75) + ((- 59 - 14) - 0)) = (-5399/75 : α) := by norm_num
-- example : (- ((- (((66 - 86) - 36) / 94) - 3) / - - (77 / (56 - - - 79))) + 87) =
--   (312254/3619 : α) := by norm_num

-- example : 2 ^ 13 - 1 = int.of_nat 8191 := by norm_num
