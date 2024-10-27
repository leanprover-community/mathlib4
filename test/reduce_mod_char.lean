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
