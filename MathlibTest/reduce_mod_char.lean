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

-- A 1024-bit prime number
set_option linter.style.longLine false in
abbrev p : Nat := 0xb10b8f96a080e01dde92de5eae5d54ec52c99fbcfb06a3c69a6a9dca52d23b616073e28675a23d189838ef1e2ee652c013ecb4aea906112324975c3cd49b83bfaccbdd7d90c4bd7098488e9c219a73724effd6fae5644738faa31a4ff55bccc0a151af5f0dc8b4bd45bf37df365c1a65e68cfda76d4da708df1fb2bc2e4a4371

set_option linter.style.longLine false in
abbrev g : Nat := 0xa4d1cbd5c3fd34126765a442efb99905f8104dd258ac507fd6406cff14266d31266fea1e5c41564b777e690f5504f213160217b4b01b886a5e91547f9e2749f4d7fbd7d3b9a92ee1909d0d2263f80a76a6a24c087a091f531dbf0a0169b6a28ad662a4d18e73afa32d779d5918d08bc8858f4dcef97c2a24855e6eeb22b3b2e5

example : (g : ZMod p) ^ (p - 1) = 1 := by reduce_mod_char

-- The 20th Mersenne prime
abbrev q : Nat := 2 ^ 4423 - 1

-- This takes a little time but the 21st Mersenne prime is too large
set_option exponentiation.threshold 10000 in
example : (3 : ZMod q) ^ (q - 1) = 1 := by reduce_mod_char

-- We don't unfold semi-reducible definitions
def q' := 2
/--
error: unsolved goals
⊢ 3 ^ (q' - 1) = 1
-/
#guard_msgs in
example : (3 : ZMod q') ^ (q' - 1) = 1 := by reduce_mod_char

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

section Assumption

/-! `reduce_mod_char!` uses `CharP R n` hypotheses it finds in the local context. -/

-- From the Zulip thread:
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/reduce_mod_char.20doesn't.20work
example {R} [CommRing R] [CharP R 3] (x : R) : x + x + x + x = x := by
  ring_nf
  reduce_mod_char!

example {R} [CommRing R] [CharP R 2] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  ring_nf
  reduce_mod_char!

example {R : Type*} [Ring R] [CharP R 2] : (2 : R) = 0 := by
  reduce_mod_char!

end Assumption

section InferInstance

/-! `reduce_mod_char!` can't do instance synthesis for `CharP R n` if `n` is not known,
so we demonstrate a workaround using `inferInstance`. -/

def ZMod' (n : ℕ) := ZMod n

instance : CommRing (ZMod' n) := inferInstanceAs (CommRing (ZMod n))
instance ZMod'.instCharP : CharP (ZMod' n) n := inferInstanceAs (CharP (ZMod n) n)

example : (2 : ZMod' 2) = 0 := by
  have : CharP (ZMod' 2) 2 := inferInstance
  reduce_mod_char!

end InferInstance

def test (_ : ZMod 37) : Type := ℕ

-- wildcard `*` is supposed to ignore dependent and non-`Prop` hypotheses
set_option linter.unusedVariables false in
set_option linter.unusedTactic false in
example (a : test 100) : ℕ := by
  let x : ZMod 2 := 100
  reduce_mod_char at *
  guard_hyp a : test 100
  exact 0
