/-
Copyright (c) 2023 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.Algebra.BigOperators.List.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.BigOperators

/-!
# Chinese Remainder Theorem

This file provides definitions and theorems for the Chinese Remainder Theorem. These are used in
Gödel's Beta function, which is used in proving Gödel's incompleteness theorems.

## Main result

- `chineseRemainderOfList`: Definition of the Chinese remainder of a list

## Tags

Chinese Remainder Theorem, Gödel, beta function
-/

namespace Nat

variable {ι : Type*}
open BigOperators

lemma modEq_list_prod_iff {a b} {l : List ℕ} (co : l.Pairwise Coprime) :
    a ≡ b [MOD l.prod] ↔ ∀ i, a ≡ b [MOD l.get i] := by
  induction' l with m l ih
  · simp [modEq_one]
  · have : Coprime m l.prod := coprime_list_prod_right_iff.mpr (List.pairwise_cons.mp co).1
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]
    constructor
    · rintro ⟨h0, hs⟩ i
      cases i using Fin.cases <;> simp [h0, hs]
    · intro h; exact ⟨h 0, fun i => h i.succ⟩

lemma modEq_list_prod_iff' {a b} {s : ι → ℕ} {l : List ι} (co : l.Pairwise (Coprime on s)) :
    a ≡ b [MOD (l.map s).prod] ↔ ∀ i ∈ l, a ≡ b [MOD s i] := by
  induction' l with i l ih
  · simp [modEq_one]
  · have : Coprime (s i) (l.map s).prod := coprime_list_prod_right_iff.mpr
      (by simp; intro j hj; exact (List.pairwise_cons.mp co).1 j hj)
    simp [← modEq_and_modEq_iff_modEq_mul this, ih (List.Pairwise.of_cons co)]

variable (a s : ι → ℕ)

/-- The natural number less than `(l.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ l`. -/
def chineseRemainderOfList : (l : List ι) → l.Pairwise (Coprime on s) →
    { k // ∀ i ∈ l, k ≡ a i [MOD s i] }
  | [],     _  => ⟨0, by simp⟩
  | i :: l, co => by
    have : Coprime (s i) (l.map s).prod := coprime_list_prod_right_iff.mpr
      (by simp; intro j hj; exact (List.pairwise_cons.mp co).1 j hj)
    have ih := chineseRemainderOfList l co.of_cons
    have k := chineseRemainder this (a i) ih
    exact ⟨k, by
      simp [k.prop.1]; intro j hj
      exact ((modEq_list_prod_iff' co.of_cons).mp k.prop.2 j hj).trans (ih.prop j hj)⟩

@[simp] theorem chineseRemainderOfList_nil :
    (chineseRemainderOfList a s [] List.Pairwise.nil : ℕ) = 0 := rfl

theorem chineseRemainderOfList_lt_prod (l : List ι)
    (co : l.Pairwise (Coprime on s)) (hs : ∀ i ∈ l, s i ≠ 0) :
    chineseRemainderOfList a s l co < (l.map s).prod := by
  cases' l with i l <;> simp
  · simp [chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := coprime_list_prod_right_iff.mpr
      (by simp; intro j hj; exact (List.pairwise_cons.mp co).1 j hj)
    exact chineseRemainder_lt_mul this (a i)
      (chineseRemainderOfList a s l co.of_cons)
        (hs i (by simp)) (by simp; intro j hj; exact hs j (by simp [hj]))

theorem chineseRemainderOfList_modEq_unique (l : List ι)
    (co : l.Pairwise (Coprime on s)) {z} (hz : ∀ i ∈ l, z ≡ a i [MOD s i]) :
    z ≡ chineseRemainderOfList a s l co [MOD (l.map s).prod] := by
  induction' l with i l ih
  · simp [modEq_one]
  · simp [chineseRemainderOfList]
    have : Coprime (s i) (l.map s).prod := coprime_list_prod_right_iff.mpr
      (by simp; intro j hj; exact (List.pairwise_cons.mp co).1 j hj)
    exact chineseRemainder_modEq_unique this
      (hz i (by simp)) (ih co.of_cons (fun j hj => hz j (by simp [hj])))

theorem chineseRemainderOfList_perm {l l' : List ι} (hl : l.Perm l')
    (hs : ∀ i ∈ l, s i ≠ 0) (co : l.Pairwise (Coprime on s)) :
    (chineseRemainderOfList a s l co : ℕ) =
    chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr) := by
  let z := chineseRemainderOfList a s l' (co.perm hl coprime_comm.mpr)
  have hlp : (l.map s).prod = (l'.map s).prod := List.Perm.prod_eq (List.Perm.map s hl)
  exact (chineseRemainderOfList_modEq_unique a s l co (z := z)
    (fun i hi => z.prop i (hl.symm.mem_iff.mpr hi))).symm.eq_of_lt_of_lt
      (chineseRemainderOfList_lt_prod _ _ _ _ hs)
      (by rw [hlp]
          exact chineseRemainderOfList_lt_prod _ _ _ _
            (by simpa [List.Perm.mem_iff hl.symm] using hs))

/-- The natural number less than `(m.map s).prod` congruent to
`a i` mod `s i` for all  `i ∈ m`. -/
def chineseRemainderOfMultiset {m : Multiset ι} :
    m.Nodup → (∀ i ∈ m, s i ≠ 0) → Set.Pairwise {x | x ∈ m} (Coprime on s) →
    { k // ∀ i ∈ m, k ≡ a i [MOD s i] } :=
  Quotient.recOn m
    (fun l nod _ co =>
      chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
    (fun l l' (pp : l.Perm l') ↦
      funext fun nod' : l'.Nodup =>
      have nod : l.Nodup := pp.symm.nodup_iff.mp nod'
      funext fun hs' : ∀ i ∈ l', s i ≠ 0 =>
      have hs : ∀ i ∈ l, s i ≠ 0  := by simpa [List.Perm.mem_iff pp] using hs'
      funext fun co' : Set.Pairwise {x | x ∈ l'} (Coprime on s) =>
      have co : Set.Pairwise {x | x ∈ l} (Coprime on s) := by simpa [List.Perm.mem_iff pp] using co'
      have lco : l.Pairwise (Coprime on s) := List.Nodup.pairwise_of_forall_ne nod co
      have : ∀ {m' e nod'' hs'' co''}, @Eq.ndrec (Multiset ι) l
        (fun m ↦ m.Nodup → (∀ i ∈ m, s i ≠ 0) →
          Set.Pairwise {x | x ∈ m} (Coprime on s) → { k // ∀ i ∈ m, k ≡ a i [MOD s i] })
        (fun nod _ co ↦ chineseRemainderOfList a s l (List.Nodup.pairwise_of_forall_ne nod co))
          m' e nod'' hs'' co'' =
        (chineseRemainderOfList a s l lco : ℕ) := by
          rintro _ rfl _ _ _; rfl
      by ext; exact this.trans <| chineseRemainderOfList_perm a s pp hs lco)

theorem chineseRemainderOfMultiset_lt_prod {m : Multiset ι}
    (nod : m.Nodup) (hs : ∀ i ∈ m, s i ≠ 0) (pp : Set.Pairwise {x | x ∈ m} (Coprime on s)) :
    chineseRemainderOfMultiset a s nod hs pp < (m.map s).prod := by
  induction' m using Quot.ind with l
  unfold chineseRemainderOfMultiset; simp
  exact chineseRemainderOfList_lt_prod a s l
    (List.Nodup.pairwise_of_forall_ne nod pp) (by simpa using hs)

/-- The natural number less than `∏ i in t, s i` congruent to
`a i` mod `s i` for all  `i ∈ t`. -/
def chineseRemainderOfFinset (t : Finset ι)
    (hs : ∀ i ∈ t, s i ≠ 0) (pp : Set.Pairwise t (Coprime on s)) :
    { k // ∀ i ∈ t, k ≡ a i [MOD s i] } :=
  by simpa using chineseRemainderOfMultiset a s t.nodup (by simpa using hs) (by simpa using pp)

theorem chineseRemainderOfFinset_lt_prod {t : Finset ι}
    (hs : ∀ i ∈ t, s i ≠ 0) (pp : Set.Pairwise t (Coprime on s)) :
    chineseRemainderOfFinset a s t hs pp < ∏ i in t, s i := by
  simpa [chineseRemainderOfFinset] using
    chineseRemainderOfMultiset_lt_prod a s t.nodup (by simpa using hs) (by simpa using pp)

end Nat
