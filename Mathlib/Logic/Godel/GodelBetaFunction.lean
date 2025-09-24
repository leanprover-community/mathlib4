/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Gödel's Beta Function Lemma

This file proves Gödel's Beta Function Lemma, used to prove the First Incompleteness Theorem. It
permits quantification over finite sequences of natural numbers in formal theories of arithmetic.
This Beta Function has no connection with the unrelated Beta Function defined in analysis. Note
that `Nat.beta` and `Nat.unbeta` provide similar functionality to `Encodable.encodeList` and
`Encodable.decodeList`. We define these separately, because it is easier to prove that `Nat.beta`
and `Nat.unbeta` are arithmetically definable, and this is hard to prove that for
`Encodable.encodeList` and `Encodable.decodeList` directly. The arithmetic
definability is needed for the proof of the First Incompleteness Theorem.

## Main result

- `beta_unbeta_coe`: Gödel's Beta Function Lemma.

## Implementation note

This code is a step towards eventually including a proof of Gödel's First Incompleteness Theorem
and other key results from the repository https://github.com/iehality/lean4-logic.

## References

* [R. Kaye, *Models of Peano arithmetic*][kaye1991]
* <https://en.wikipedia.org/wiki/G%C3%B6del%27s_%CE%B2_function>

## Tags

Gödel, beta function
-/

namespace Nat

lemma coprime_mul_succ {n m a} (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd fun p pp hn hm => by
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    apply pp.ne_one
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hn (this.mul_left n)

variable {m : ℕ}

private def supOfSeq (a : Fin m → ℕ) : ℕ := max m (Finset.sup .univ a) + 1

private def coprimes (a : Fin m → ℕ) : Fin m → ℕ := fun i => (i + 1) * (supOfSeq a)! + 1

lemma coprimes_lt (a : Fin m → ℕ) (i) : a i < coprimes a i := by
  have h₁ : a i < supOfSeq a :=
    Nat.lt_add_one_iff.mpr (le_max_of_le_right <| Finset.le_sup (by simp))
  have h₂ : supOfSeq a ≤ (i + 1) * (supOfSeq a)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (supOfSeq a)! (succ_pos i))
      (le_add_right _ _))
  simpa only [coprimes] using lt_of_lt_of_le h₁ h₂

open scoped Function in -- required for scoped `on` notation
private lemma pairwise_coprime_coprimes (a : Fin m → ℕ) : Pairwise (Coprime on coprimes a) := by
  intro i j hij
  wlog ltij : i < j
  · exact (this a hij.symm (lt_of_le_of_ne (Fin.not_lt.mp ltij) hij.symm)).symm
  unfold Function.onFun coprimes
  have hja : j < supOfSeq a := lt_of_lt_of_le j.prop (le_step (le_max_left _ _))
  exact coprime_mul_succ
    (Nat.dvd_factorial (by cutsat)
      (by simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hja)))

/-- Gödel's Beta Function. This is similar to `(Encodable.decodeList)[i]`, but it is easier to
prove that it is arithmetically definable. -/
def beta (n i : ℕ) : ℕ := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

/-- Inverse of Gödel's Beta Function. This is similar to `Encodable.encodeList`, but it is easier
to prove that it is arithmetically definable. -/
def unbeta (l : List ℕ) : ℕ :=
  (chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
    (by simp [coprimes])
    (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _)) : ℕ).pair
  (supOfSeq (l[·]))!

/-- **Gödel's Beta Function Lemma** -/
lemma beta_unbeta_coe (l : List ℕ) (i : Fin l.length) : beta (unbeta l) i = l[i] := by
  simpa [beta, unbeta, coprimes] using mod_eq_of_modEq
    ((chineseRemainderOfFinset (l[·]) (coprimes (l[·])) Finset.univ
      (by simp [coprimes])
      (by simpa using Set.pairwise_univ.mpr (pairwise_coprime_coprimes _))).prop i (by simp))
    (coprimes_lt _ _)

end Nat
