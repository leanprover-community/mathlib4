/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.MinMax
import Mathlib.Data.ZMod.Coprime

/-!
# Gödel's Beta Function Lemma

This file proves Gödel's Beta Function Lemma, used to prove the First Incompleteness Theorem. It
 permits  quantification over finite sequences of natural numbers in formal theories of arithmetic.
 This Beta Function has no connection with the unrelated Beta Function defined in analysis. Note
 that beta and unbeta provide similar functionality to List.encodeList and List.decodeList, ,
 except that we can prove that `Nat.beta` and `Nat.unbeta` are arithmetically definable, and it is
 hard to prove that for `Encodable.encodeList` and `Encodable.decodeList` directly. The arithmetic
 definability is needed for the proof of the  First Incompleteness Theorem.

## Main result

- `beta_function_lemma`: Gödel's Beta Function Lemma.

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

open ZMod

/-- Gödel's Beta Function. This is similar to `(Encodable.decodeList).get i`, but it is easier to
prove that it is arithmetically definable. -/
def beta (n i : ℕ) : ℕ := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

/-- Inverse of Gödel's Beta Function. This is similar to `Encodable.encodeList` , but it is easier
to prove that it is arithmetically definable. -/
def unbeta (l : List ℕ) : ℕ :=
  (chineseRemainderList (coprimeList l) (pairwise_coprime_coprimeList l) : ℕ).pair (listSup l)!

lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b := by
  simpa[show a % n = b % n from h] using mod_eq_of_lt hb

/-- **Gödel's Beta Function Lemma** -/
lemma beta_function_lemma (l : List ℕ) (i : Fin l.length) :
    beta (unbeta l) i = l.get i := by
  simpa[beta, unbeta, coprimeList] using mod_eq_of_modEq
    ((chineseRemainderList (coprimeList l) (pairwise_coprime_coprimeList l)).2 (i.cast $ by simp))
    (coprimeList_lt l _)

end Nat
