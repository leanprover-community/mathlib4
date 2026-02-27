/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Bijective Base-2 Numeration

This module formalizes a bijective base-2 numeration system.
Unlike standard binary representation, bijective base-2 numeration avoids the
"leading zeros" problem, providing a strict bijection `ℕ ≃ List Bool`.
-/

@[expose] public section

namespace BijectiveNumeration

/-- Encodes a natural number into a list of booleans using bijective base-2. -/
def toBits (n : ℕ) : List Bool :=
  if h : n = 0 then []
  else ((n - 1) % 2 == 1) :: toBits ((n - 1) / 2)
termination_by n
decreasing_by lia

@[simp] lemma toBits_zero : toBits 0 = [] := by rw [toBits]; simp

/-- Decodes a list of booleans into a natural number using bijective base-2.
    [] ↦ 0, [false] ↦ 1, [true] ↦ 2, [false, false] ↦ 3. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | false :: bs => 1 + 2 * ofBits bs
  | true :: bs => 2 + 2 * ofBits bs

@[simp] lemma ofBits_nil : ofBits [] = 0 := rfl

/-- Proves that decoding the encoded bijective base-2 bits of a natural number
returns the original number. -/
@[simp]
theorem ofBits_toBits (n : ℕ) : ofBits (toBits n) = n := by
  rw [toBits]
  split_ifs with h
  · subst h; rfl
  · have ih := ofBits_toBits ((n - 1) / 2)
    have h_mod : (n - 1) % 2 = 0 ∨ (n - 1) % 2 = 1 := by lia
    rcases h_mod with h0 | h1
    · simp [h0, ofBits, ih]
      lia
    · simp [h1, ofBits, ih]
      lia
termination_by n
decreasing_by lia

/-- Proves that encoding the decoded natural number of bijective base-2 bits
returns the original bits. -/
@[simp]
theorem toBits_ofBits (bs : List Bool) : toBits (ofBits bs) = bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b
    · change toBits (1 + 2 * ofBits bs) = false :: bs
      rw [toBits]
      split_ifs with h
      · lia
      · have h_math : 1 + 2 * ofBits bs - 1 = 2 * ofBits bs := by lia
        have h_div : (2 * ofBits bs) / 2 = ofBits bs := by lia
        have h_mod : (2 * ofBits bs) % 2 = 0 := by lia
        simp [h_math, h_div, h_mod, ih]
    · change toBits (2 + 2 * ofBits bs) = true :: bs
      rw [toBits]
      split_ifs with h
      · lia
      · have h_math : 2 + 2 * ofBits bs - 1 = 1 + 2 * ofBits bs := by lia
        have h_div : (1 + 2 * ofBits bs) / 2 = ofBits bs := by lia
        have h_mod : (1 + 2 * ofBits bs) % 2 = 1 := by lia
        simp [h_math, h_div, h_mod, ih]

end BijectiveNumeration

/-- The formal mathematical bijection between Natural Numbers and Boolean Lists
using bijective base-2 numeration. -/
def listNatBijectiveEquiv : ℕ ≃ List Bool where
  toFun := BijectiveNumeration.toBits
  invFun := BijectiveNumeration.ofBits
  left_inv := BijectiveNumeration.ofBits_toBits
  right_inv := BijectiveNumeration.toBits_ofBits

end
