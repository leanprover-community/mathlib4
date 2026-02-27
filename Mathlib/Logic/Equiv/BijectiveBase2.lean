/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Equiv.Basic

/-!
# Bijective Base-2 Numeration

This module formalizes a bijective base-2 numeration system.
Unlike standard binary representation, bijective base-2 numeration avoids the
"leading zeros" problem, providing a strict bijection `ℕ ≃ List Bool`.
-/

namespace Equiv.BijectiveBase2

/-- Encodes a natural number into a list of booleans using bijective base-2. -/
def toBits (n : ℕ) : List Bool :=
  if h : n = 0 then []
  else ((n - 1) % 2 == 1) :: toBits ((n - 1) / 2)
termination_by n
decreasing_by omega

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
    have h_mod : (n - 1) % 2 = 0 ∨ (n - 1) % 2 = 1 := by omega
    rcases h_mod with h0 | h1
    · simp [h0, ofBits, ih]
      omega
    · simp [h1, ofBits, ih]
      omega
termination_by n
decreasing_by omega

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
      · omega
      · have h_math : 1 + 2 * ofBits bs - 1 = 2 * ofBits bs := by omega
        have h_div : (2 * ofBits bs) / 2 = ofBits bs := by omega
        have h_mod : (2 * ofBits bs) % 2 = 0 := by omega
        simp [h_math, h_div, h_mod, ih]
    · change toBits (2 + 2 * ofBits bs) = true :: bs
      rw [toBits]
      split_ifs with h
      · omega
      · have h_math : 2 + 2 * ofBits bs - 1 = 1 + 2 * ofBits bs := by omega
        have h_div : (1 + 2 * ofBits bs) / 2 = ofBits bs := by omega
        have h_mod : (1 + 2 * ofBits bs) % 2 = 1 := by omega
        simp [h_math, h_div, h_mod, ih]

end Equiv.BijectiveBase2

/-- The formal mathematical bijection between Natural Numbers and Boolean Lists
using bijective base-2 numeration. -/
def equivBijectiveBase2 : ℕ ≃ List Bool where
  toFun := Equiv.BijectiveBase2.toBits
  invFun := Equiv.BijectiveBase2.ofBits
  left_inv := Equiv.BijectiveBase2.ofBits_toBits
  right_inv := Equiv.BijectiveBase2.toBits_ofBits
