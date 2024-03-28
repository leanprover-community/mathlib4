/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Tactic.ReduceModChar

/-!
# Tests for `reduce_mod_char` tactic
-/

open Polynomial

-- Numerals:
example : (5 : ZMod 4) = 1 := by reduce_mod_char

-- Negation:
example : (-5 : ZMod 4) = 3 := by reduce_mod_char
example : (-5 : (ZMod 4)[X]) = 3 := by reduce_mod_char
example : (-X : (ZMod 4)[X]) = 3 * X := by reduce_mod_char

-- Polynomials:
example : (4 * X + 3 : (ZMod 4)[X]) = 3 := by reduce_mod_char
example : (5 * X ^ 2 + 4 * X + 3 : (ZMod 4)[X]) = X ^ 2 + 3 := by reduce_mod_char

-- Negation:
example : (X ^ 2 - 3 : (ZMod 4)[X]) = X ^ 2 + 1 := by reduce_mod_char

-- Cleaning up `1 * X` and `X + 0`:
example : (5 * X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char

-- Exponentiation:
example : (11 : ZMod 987654319) ^ 987654318 = 1 := by reduce_mod_char
example : (-126432 : ZMod 1235412223) ^ 12355342321 = 1001528716 := by reduce_mod_char
example : (((((5 : ZMod 1235412223) ^ 5) ^ 5) ^ 5) ^ 5) ^ 5 = 806432269 := by reduce_mod_char
example : (2 : ZMod 75) ^ 0 = 1 := by reduce_mod_char
example : (0 : ZMod 34523432) ^ 0 = 1 := by reduce_mod_char
example : (0 : ZMod 56) ^ 90000000000000000 = 0 := by reduce_mod_char
example : (1 : ZMod 119) ^ 433440000000000000000000 = 1 := by reduce_mod_char
example : (75 : ZMod 111) ^ 1 = 75 := by reduce_mod_char
example : (23 : ZMod 19) ^ 1 = 4 := by reduce_mod_char
example : (1923423451 : ZMod 2) ^ 81000000000000000000 = 1 := by reduce_mod_char
example : (19 : ZMod 1) ^ 810000000000000000000 = 0 := by reduce_mod_char
example : (23423432049230423 : ZMod 0) ^ 0 = 1 := by reduce_mod_char
example : (23423432049230423 : ZMod 1) ^ 0 = 0 := by reduce_mod_char

-- Rewriting hypotheses:
example (a : ZMod 7) (h : a + 7 = 2) : a = 2 := by
  reduce_mod_char at h
  assumption

example (a : ZMod 7) (h : a + 14 = 2) : a + 7 = 2 := by
  reduce_mod_char at *
  assumption

-- A stress test:
example (a b : ZMod 37) : (a + b)^37 = a^37 + b^37 := by ring_nf; reduce_mod_char

-- From the zulip thread:
-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/tactic.20for.20easy.20calculations.20in.20ZMod.20p.3F
lemma foo (a b : ZMod 7) (h : a + 3 * b = 0) : a = 4 * b := by
  rw [eq_sub_of_add_eq h]
  reduce_mod_char
