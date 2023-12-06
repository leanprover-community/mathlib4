/-
Copyright (c) 2023 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime
import Mathlib.Data.W.Basic

/-!
# Gödel's Beta Function Lemma

This file proves Gödel's Beta Function Lemma, used to prove the First Incompleteness Theorem. It
 permits  quantification over finite sequences of natural numbers in formal theories of arithmetic.
 This Beta Function has no connection with the unrelated Beta Function defined in analysis.

## Implementation notes

This file is taken from https://github.com/iehality/lean4-logic, which includes proofs of Gödel's
First Incompleteness Theorem and other key results in logic. The eventual goal is to import
these into mathlib.

## References

* [Richard Kaye, *Models of Peano Arithmetic*][kaye1991]
* <https://en.wikipedia.org/wiki/G%C3%B6del%27s_%CE%B2_function>

## Tags

Gödel, Logic
-/

namespace List

section
variable {α : Type u} [SemilatticeSup α] [OrderBot α]

/-- These lemmas set the stage for Gödel's Beta Function Lemma, -/
def sup : List α → α
  | [] => ⊥
  | a :: as => a ⊔ as.sup

@[simp] lemma sup_cons (a : α) (as : List α) : (a :: as).sup = a ⊔ as.sup := rfl

lemma le_sup {a} {l : List α} : a ∈ l → a ≤ l.sup :=
  by induction' l with a l ih <;> simp[*]; rintro (rfl | h); { simp }; { exact le_sup_of_le_right $ ih h }

end

end List

namespace Nat

/-- These lemmas set the stage for Gödel's Beta Function Lemma, -/
lemma mod_eq_of_modEq {a b n} (h : a ≡ b [MOD n]) (hb : b < n) : a % n = b := by
  have : a % n = b % n := h
  simp[this]; exact mod_eq_of_lt hb

lemma coprime_list_prod_iff_right {k} {l : List ℕ} :
    Coprime k l.prod ↔ ∀ n ∈ l, Coprime k n := by
  induction' l with m l ih <;> simp[Nat.coprime_mul_iff_right, *]

inductive Coprimes : List ℕ → Prop
  | nil : Coprimes []
  | cons {n : ℕ} {l : List ℕ} : (∀ m ∈ l, Coprime n m) → Coprimes l → Coprimes (n :: l)

lemma coprimes_of_nodup {l : List ℕ} (hl : l.Nodup) (H : ∀ n ∈ l, ∀ m ∈ l, n ≠ m → Coprime n m) :
    Coprimes l := by
  induction' l with n l ih
  · exact Coprimes.nil
  · have : Coprimes l := ih (List.Nodup.of_cons hl) (fun m hm k hk => H m (by simp[hm]) k (by simp[hk]))
    exact Coprimes.cons (fun m hm => coprime_comm.mp
      (H m (by simp[hm]) n (by simp) (by rintro rfl; exact (List.nodup_cons.mp hl).1 hm))) this

lemma coprimes_cons_iff_coprimes_coprime_prod {n} {l : List ℕ} :
    Coprimes (n :: l) ↔ Coprimes l ∧ Coprime n l.prod := by
  simp[coprime_list_prod_iff_right]; constructor
  · rintro ⟨⟩ ; simpa[*]
  · rintro ⟨hl, hn⟩; exact Coprimes.cons hn hl

lemma modEq_iff_modEq_list_prod {a b} {l : List ℕ} (co : Coprimes l) :
    (∀ i, a ≡ b [MOD l.get i]) ↔ a ≡ b [MOD l.prod] := by
  induction' l with m l ih <;> simp[Nat.modEq_one]
  · rcases co with (_ | ⟨hm, hl⟩)
    have : a ≡ b [MOD m] ∧ a ≡ b [MOD l.prod] ↔ a ≡ b [MOD m * l.prod] :=
      Nat.modEq_and_modEq_iff_modEq_mul (coprime_list_prod_iff_right.mpr hm)
    simp[←this, ←ih hl]
    constructor
    · intro h; exact ⟨by simpa using h ⟨0, by simp⟩, fun i => by simpa using h i.succ⟩
    · intro h i
      cases i using Fin.cases
      · simpa using h.1
      · simpa using h.2 _

def chineseRemainderList : (l : List (ℕ × ℕ)) → (H : Coprimes (l.map Prod.snd)) →
    { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] }
  | [],          _ => ⟨0, by simp⟩
  | (a, m) :: l, H => by
    have hl : Coprimes (l.map Prod.snd) ∧ Coprime m (l.map Prod.snd).prod :=
      coprimes_cons_iff_coprimes_coprime_prod.mp H
    let ih : { k // ∀ i, k ≡ (l.get i).1 [MOD (l.get i).2] } := chineseRemainderList l hl.1
    let z := Nat.chineseRemainder hl.2 a ih
    exact ⟨z, by
      intro i; cases' i using Fin.cases with i <;> simp
      · exact z.prop.1
      · have : z ≡ ih [MOD (l.get i).2] := by
          simpa using (modEq_iff_modEq_list_prod hl.1).mpr z.prop.2 (i.cast $ by simp)
        have : z ≡ (l.get i).1 [MOD (l.get i).2] := Nat.ModEq.trans this (ih.prop i)
        exact this⟩

def listSup (l : List ℕ) := max l.length l.sup + 1

def coprimeList (l : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun i : Fin l.length => (l.get i, (i + 1) * (listSup l)! + 1))

@[simp] lemma coprimeList_length (l : List ℕ) : (coprimeList l).length = l.length := by simp[coprimeList]

lemma coprimeList_lt (l : List ℕ) (i) : ((coprimeList l).get i).1 < ((coprimeList l).get i).2 := by
  have h₁ : l.get (i.cast $ by simp[coprimeList]) < listSup l :=
    Nat.lt_add_one_iff.mpr (by simp; right; exact List.le_sup (by apply List.get_mem))
  have h₂ : Nat.listSup l ≤ (i + 1) * (Nat.listSup l)! + 1 := calc
    Nat.listSup l ≤ (Nat.listSup l)!               := self_le_factorial _
    _             ≤ (i + 1) * (Nat.listSup l)!     := Nat.le_mul_of_pos_left (succ_pos _)
    _             ≤ (i + 1) * (Nat.listSup l)! + 1 := le_add_right _ _
  simpa only [coprimeList, List.get_ofFn] using lt_of_lt_of_le h₁ h₂

lemma coprime_mul_succ {n m a} (h : n ≤ m) (ha : m - n ∣ a) : Coprime (n * a + 1) (m * a + 1) :=
  Nat.coprime_of_dvd (by
    intro p pp hn hm
    have : p ∣ (m - n) * a := by
      simpa [Nat.succ_sub_succ, ←Nat.mul_sub_right_distrib] using
        Nat.dvd_sub (Nat.succ_le_succ $ Nat.mul_le_mul_right a h) hm hn
    have : p ∣ a := by
      rcases (Nat.Prime.dvd_mul pp).mp this with (hp | hp)
      · exact Nat.dvd_trans hp ha
      · exact hp
    have : p = 1 := by
      simpa[Nat.add_sub_cancel_left] using Nat.dvd_sub (le_add_right _ _) hn (Dvd.dvd.mul_left this n)
    simp[this] at pp)

lemma coprimes_coprimeList (l : List ℕ) : Coprimes ((coprimeList l).map Prod.snd) := by
  have : (coprimeList l).map Prod.snd = List.ofFn (fun i : Fin l.length => (i + 1) * (listSup l)! + 1) := by
    simp[coprimeList, Function.comp]
  rw[this]
  exact coprimes_of_nodup
    (List.nodup_ofFn_ofInjective $ by
       intro i j; simp[listSup, ←Fin.ext_iff, Nat.factorial_ne_zero])
    (by
      simp[←Fin.ext_iff, not_or]
      suffices : ∀ i j : Fin l.length, i < j → Coprime ((i + 1) * (listSup l)! + 1) ((j + 1) * (listSup l)! + 1)
      · intro i j hij _
        have : i < j ∨ j < i := Ne.lt_or_lt hij; rcases this with (hij | hij)
        · exact this i j hij
        · exact coprime_comm.mp (this j i hij)
      intro i j hij
      have hjl : j < listSup l := lt_of_lt_of_le j.prop (le_step (le_max_left l.length l.sup))
      apply coprime_mul_succ
        (Nat.succ_le_succ $ le_of_lt hij)
        (Nat.dvd_factorial (by simp[Nat.succ_sub_succ, hij]) (by
          simpa only [Nat.succ_sub_succ] using le_of_lt (lt_of_le_of_lt (sub_le j i) hjl))))

def beta (n i : ℕ) := n.unpair.1 % ((i + 1) * n.unpair.2 + 1)

def unbeta (l : List ℕ) := (chineseRemainderList (coprimeList l) (coprimes_coprimeList l) : ℕ).pair (listSup l)!

/-- **Gödel's Beta Function Lemma** -/
lemma beta_function_lemma (l : List ℕ) (i : Fin l.length) :
    beta (unbeta l) i = l.get i := by
  simpa[beta, unbeta, coprimeList] using mod_eq_of_modEq
    ((chineseRemainderList (coprimeList l) (coprimes_coprimeList l)).2 (i.cast $ by simp))
    (coprimeList_lt l _)

end Nat
