/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.ModEq

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

/-- Maximum of a list's length and its largest element plus one -/
def listSup (l : List ℕ) := max l.length (List.foldr max 0 l) + 1

/-- A list of coprimes -/
def coprimeList (l : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin l.length => (l.get i, (i + 1) * (listSup l)! + 1))

@[simp] lemma coprimeList_length (l : List ℕ) : (coprimeList l).length = l.length :=
  by simp[coprimeList, List.length_ofFn]

lemma coprimeList_lt (l : List ℕ) (i) : ((coprimeList l).get i).1 < ((coprimeList l).get i).2 := by
  have h₁ : l.get (i.cast $ by simp[coprimeList]) < listSup l :=
    Nat.lt_add_one_iff.mpr (by simpa using Or.inr $ List.le_max_of_le (List.get_mem _ _ _) (by rfl))
  have h₂ : listSup l ≤ (i + 1) * (listSup l)! + 1 :=
    le_trans (self_le_factorial _) (le_trans (Nat.le_mul_of_pos_left (succ_pos _))
      (le_add_right _ _))
  simpa only [coprimeList, List.get_ofFn] using lt_of_lt_of_le h₁ h₂

lemma coprime_mul_succ {n m a} (h : n ≤ m) (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd (by
    intro p pp hn hm
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ← Nat.mul_sub_right_distrib] using
        Nat.dvd_sub (Nat.succ_le_succ $ Nat.mul_le_mul_right a h) hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    have : p = 1 := by
      simpa[Nat.add_sub_cancel_left] using Nat.dvd_sub (le_add_right _ _) hn
        (Dvd.dvd.mul_left this n)
    simp[this] at pp
    apply Nat.not_prime_one at pp
    exact pp)

lemma pairwise_coprime_coprimeList (l : List ℕ) :
    ((coprimeList l).map Prod.snd).Pairwise Coprime := by
  have : (coprimeList l).map Prod.snd = List.ofFn (fun i : Fin l.length => (i + 1) *
      (listSup l)! + 1) := by
    simp[coprimeList, Function.comp]
  rw[this]
  exact List.Nodup.pairwise_of_forall_ne
    (List.nodup_ofFn_ofInjective $ by
       intro i j; simp[listSup, ← Fin.ext_iff, Nat.factorial_ne_zero])
    (by
      simp[← Fin.ext_iff, not_or]
      suffices : ∀ i j : Fin l.length, i < j → Coprime ((i + 1) * (listSup l)! + 1) ((j + 1) *
        (listSup l)! + 1)
      · intro i j hij _
        rcases Ne.lt_or_lt hij with (hij | hij)
        · exact this i j hij
        · exact coprime_comm.mp (this j i hij)
      intro i j hij
      have hjl : j < listSup l := lt_of_lt_of_le j.prop (le_step (le_max_left l.length
        (List.foldr max 0 l)))
      apply coprime_mul_succ
        (Nat.succ_le_succ $ le_of_lt hij)
        (Nat.dvd_factorial (by simp[Nat.succ_sub_succ, hij]) (by
          simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hjl))))

/-- Gödel's Beta Function. This is similar to `(Encodable.decodeList).get i`, but it is easier to
prove that it is arithmetically definable. -/
def beta (n i : ℕ) : ℕ := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

/-- Inverse of Gödel's Beta Function. This is similar to `Encodable.encodeList`, but it is easier
to prove that it is arithmetically definable. -/
def unbeta (l : List ℕ) : ℕ :=
  (chineseRemainderOfList (coprimeList l) (pairwise_coprime_coprimeList l) : ℕ).pair (listSup l)!

lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b := by
  simpa[show a % n = b % n from h] using mod_eq_of_lt hb

/-- **Gödel's Beta Function Lemma** -/
lemma beta_function_lemma (l : List ℕ) (i : Fin l.length) :
    beta (unbeta l) i = l.get i := by
  simpa[beta, unbeta, coprimeList] using mod_eq_of_modEq
    ((chineseRemainderOfList (coprimeList l) (pairwise_coprime_coprimeList l)).2 (i.cast $ by simp))
    (coprimeList_lt l _)

end Nat
