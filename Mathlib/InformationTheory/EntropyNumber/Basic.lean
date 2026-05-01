/-
Copyright (c) 2026 Essam Abadir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Essam Abadir
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Nat
public import Mathlib.Data.Finset.Basic
public import Mathlib.InformationTheory.Basic



/-!
# EntropyNat: Information-Theoretic Natural Numbers

The natural numbers viewed as compressed binary paths. An `EntropyNat` is a list of
`true` values whose length encodes a natural number. This gives a bijection
`EntropyNat ≃ ℕ` together with arithmetic operations that respect that bijection.

## Main definitions

* `EntropyNat` — the subtype `{ L : List Bool // ∀ x ∈ L, x = true }`.
* `EntropyNat.toNat` / `EntropyNat.ofNat` — the bijection with `ℕ`.
* `entropyNatEquivNat` — the bundled `Equiv`.
* `EntropyNat.add` / `EntropyNat.mul` — arithmetic via the equivalence.

## Main results

* `EntropyNat.ofNat_toNat` — `ofNat` is a left inverse of `toNat`.
* `EntropyNat.toNat_ofNat` — `toNat` is a left inverse of `ofNat`.
* `EntropyNat.toNat_add` — `toNat` is additive.
* `EntropyNat.toNat_mul` — `toNat` is multiplicative.
-/

@[expose] public section

open List

namespace InformationTheory

/-! ## EntropyNat -/

/-- An `EntropyNat` is a `List Bool` all of whose entries are `true`.
The length of the list encodes a natural number. -/
abbrev EntropyNat := { L : List Bool // ∀ x ∈ L, x = true }

namespace EntropyNat

/-- Map an `EntropyNat` to `ℕ` by taking the length of its underlying list. -/
def toNat (u : EntropyNat) : ℕ := u.val.length

/-- Construct the `EntropyNat` encoding of a natural number. -/
def ofNat (n : ℕ) : EntropyNat :=
  ⟨List.replicate n true, by
    intro x h_mem
    rw [List.mem_replicate] at h_mem
    exact h_mem.right⟩

/-- `toNat (ofNat n) = n`. -/
lemma ofNat_toNat (n : ℕ) : toNat (ofNat n) = n := by
  simp [toNat, ofNat]

/-- `ofNat (toNat u) = u`. -/
lemma toNat_ofNat (u : EntropyNat) : ofNat (toNat u) = u := by
  cases u with
  | mk L hL =>
      simp [toNat, ofNat, List.length_replicate, Subtype.ext]
      exact (List.eq_replicate_of_mem hL).symm

end EntropyNat

/-- The canonical equivalence `EntropyNat ≃ ℕ`. -/
def entropyNatEquivNat : EntropyNat ≃ ℕ :=
{ toFun    := EntropyNat.toNat,
  invFun   := EntropyNat.ofNat,
  left_inv := EntropyNat.toNat_ofNat,
  right_inv := EntropyNat.ofNat_toNat }

namespace EntropyNat

/-- Add two `EntropyNat` values via their `ℕ` representations. -/
def add (path1 path2 : EntropyNat) : EntropyNat :=
  entropyNatEquivNat.invFun
    (entropyNatEquivNat.toFun path1 + entropyNatEquivNat.toFun path2)

/-- Helper for multiplication: multiply by adding repeatedly. -/
def mulRec (a : EntropyNat) : ℕ → EntropyNat
  | 0 => ofNat 0
  | Nat.succ n => add a (mulRec a n)

/-- Multiply two `EntropyNat` values: `mul a b` adds `a` to itself `toNat b` times. -/
def mul (a b : EntropyNat) : EntropyNat :=
  mulRec a (toNat b)

/-- `toNat` respects addition. -/
lemma toNat_add (a b : EntropyNat) :
    toNat (add a b) = toNat a + toNat b := by
  simp [add, entropyNatEquivNat, toNat, ofNat]

/-- `toNat` respects multiplication. -/
theorem toNat_mul (a b : EntropyNat) :
    toNat (mul a b) = toNat a * toNat b := by
  unfold mul
  induction toNat b with
  | zero =>
    simp [mulRec, toNat, ofNat]
  | succ i ih =>
    show toNat (mulRec a (i + 1)) = toNat a * (i + 1)
    rw [mulRec, toNat_add, ih, Nat.mul_succ, Nat.add_comm]

end EntropyNat

end InformationTheory
