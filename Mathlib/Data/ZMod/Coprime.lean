/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Nat.ModEq

#align_import data.zmod.coprime from "leanprover-community/mathlib"@"4b4975cf92a1ffe2ddfeff6ff91b0c46a9162bf5"

/-!
# Coprimality and vanishing

We show that for prime `p`, the image of an integer `a` in `ZMod p` vanishes if and only if
`a` and `p` are not coprime. We also provide lemmas for working with lists of coprimes.
-/

namespace ZMod

/-- If `p` is a prime and `a` is an integer, then `a : ZMod p` is zero if and only if
`gcd a p ≠ 1`. -/
theorem eq_zero_iff_gcd_ne_one {a : ℤ} {p : ℕ} [pp : Fact p.Prime] :
    (a : ZMod p) = 0 ↔ a.gcd p ≠ 1 := by
  rw [Ne, Int.gcd_comm, Int.gcd_eq_one_iff_coprime,
    (Nat.prime_iff_prime_int.1 pp.1).coprime_iff_not_dvd, Classical.not_not,
    int_cast_zmod_eq_zero_iff_dvd]
#align zmod.eq_zero_iff_gcd_ne_one ZMod.eq_zero_iff_gcd_ne_one

/-- If an integer `a` and a prime `p` satisfy `gcd a p = 1`, then `a : ZMod p` is nonzero. -/
theorem ne_zero_of_gcd_eq_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p = 1) : (a : ZMod p) ≠ 0 :=
  mt (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mp (Classical.not_not.mpr h)
#align zmod.ne_zero_of_gcd_eq_one ZMod.ne_zero_of_gcd_eq_one

/-- If an integer `a` and a prime `p` satisfy `gcd a p ≠ 1`, then `a : ZMod p` is zero. -/
theorem eq_zero_of_gcd_ne_one {a : ℤ} {p : ℕ} (pp : p.Prime) (h : a.gcd p ≠ 1) : (a : ZMod p) = 0 :=
  (@eq_zero_iff_gcd_ne_one a p ⟨pp⟩).mpr h
#align zmod.eq_zero_of_gcd_ne_one ZMod.eq_zero_of_gcd_ne_one

open Nat

lemma coprime_list_prod_iff_right {k} {l : List ℕ} :
    Coprime k l.prod ↔ ∀ n ∈ l, Coprime k n := by
  induction' l with m l ih <;> simp[Nat.coprime_mul_iff_right, *]

lemma coprime_list_prod_iff_left {k} {l : List ℕ} :
    Coprime l.prod k ↔ ∀ n ∈ l, Coprime k n := by
  induction' l with m l ih <;> simp[Nat.coprime_mul_iff_left, *]
  intro
  exact coprime_comm

lemma pairwise_coprime_cons_iff_pairwise_coprime_coprime_prod {n} {l : List ℕ} :
    (n :: l).Pairwise Coprime ↔ l.Pairwise Coprime ∧ Coprime n l.prod := by
  rw[List.pairwise_cons, coprime_list_prod_iff_right, and_comm]

lemma modEq_iff_modEq_list_prod {a b} {l : List ℕ} (co : l.Pairwise Coprime) :
    (∀ i, a ≡ b [MOD l.get i]) ↔ a ≡ b [MOD l.prod] := by
  induction' l with m l ih <;> simp[Nat.modEq_one]
  · rcases co with (_ | ⟨hm, hl⟩)
    have : a ≡ b [MOD m] ∧ a ≡ b [MOD l.prod] ↔ a ≡ b [MOD m * l.prod] :=
      Nat.modEq_and_modEq_iff_modEq_mul (coprime_list_prod_iff_right.mpr hm)
    simp[← this, ← ih hl]
    constructor
    · intro h; exact ⟨by simpa using h ⟨0, by simp⟩, fun i => by simpa using h i.succ⟩
    · intro h i
      cases i using Fin.cases
      · simpa using h.1
      · simpa using h.2 _

/-- List of coprimes, using the Chinese remainder theorem -/
def chineseRemainderList : (l : List (ℕ × ℕ)) → (H : (l.map Prod.snd).Pairwise Coprime) →
    { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] }
  | [],          _ => ⟨0, by simp⟩
  | (a, m) :: l, H => by
    have hl : (l.map Prod.snd).Pairwise Coprime ∧ Coprime m (l.map Prod.snd).prod :=
      pairwise_coprime_cons_iff_pairwise_coprime_coprime_prod.mp H
    let ih : { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] } := chineseRemainderList l hl.1
    let z := Nat.chineseRemainder hl.2 a ih
    exact ⟨z, by
      intro i; cases' i using Fin.cases with i <;> simp
      · exact z.prop.1
      · have : z ≡ ih [MOD (l.get i).2] := by
          simpa using (modEq_iff_modEq_list_prod hl.1).mpr z.prop.2 (i.cast $ by simp)
        have : z ≡ (l.get i).1 [MOD (l.get i).2] := Nat.ModEq.trans this (ih.prop i)
        exact this⟩

/-- Maximum of a list's length and its largest element plus one -/
def listSup (l : List ℕ) := max l.length (List.foldr max 0 l) + 1

/-- A list of coprimes -/
def coprimeList (l : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin l.length => (l.get i, (i + 1) * (listSup l)! + 1))

@[simp] lemma coprimeList_length (l : List ℕ) : (coprimeList l).length = l.length :=
  by simp[coprimeList]

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
    exact pp
    )

lemma pairwise_coprime_coprimeList (l : List ℕ) : ((coprimeList l).map Prod.snd).Pairwise
    Coprime := by
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



end ZMod
