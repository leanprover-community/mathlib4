/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/

import Mathlib.Init.Data.Nat.Lemmas

/-!
# `Nat.find` and `Nat.findGreatest`
-/

variable {a b c d m n k : ℕ} {p q : ℕ → Prop}

namespace Nat

section Find

/-! ### `Nat.find` -/

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] [DecidablePred q] (H : ∃ n, p n)

private def wf_lbp : WellFounded (@lbp p) :=
  ⟨let ⟨n, pn⟩ := H
    suffices ∀ m k, n ≤ k + m → Acc lbp k from fun a => this _ _ (Nat.le_add_left _ _)
    fun m =>
    Nat.recOn m
      (fun k kn =>
        ⟨_, fun y r =>
          match y, r with
          | _, ⟨rfl, a⟩ => absurd pn (a _ kn)⟩)
      fun m IH k kn =>
      ⟨_, fun y r =>
        match y, r with
        | _, ⟨rfl, _a⟩ => IH _ (by rw [Nat.add_right_comm]; exact kn)⟩⟩

protected def findX : { n // p n ∧ ∀ m < n, ¬p m } :=
  @WellFounded.fix _ (fun k => (∀ n < k, ¬p n) → { n // p n ∧ ∀ m < n, ¬p m }) lbp (wf_lbp H)
    (fun m IH al =>
      if pm : p m then ⟨m, pm, al⟩
      else
        have : ∀ n ≤ m, ¬p n := fun n h =>
          Or.elim (Decidable.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
        IH _ ⟨rfl, this⟩ fun n h => this n <| Nat.le_of_succ_le_succ h)
    0 fun n h => absurd h (Nat.not_lt_zero _)
#align nat.find_x Nat.findX

/-- If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.
-/
protected def find : ℕ :=
  (Nat.findX H).1
#align nat.find Nat.find

protected theorem find_spec : p (Nat.find H) :=
  (Nat.findX H).2.left
#align nat.find_spec Nat.find_spec

protected theorem find_min : ∀ {m : ℕ}, m < Nat.find H → ¬p m :=
  @(Nat.findX H).2.right
#align nat.find_min Nat.find_min

protected theorem find_min' {m : ℕ} (h : p m) : Nat.find H ≤ m :=
  le_of_not_lt fun l => Nat.find_min H l h
#align nat.find_min' Nat.find_min'

lemma find_eq_iff (h : ∃ n : ℕ, p n) : Nat.find h = m ↔ p m ∧ ∀ n < m, ¬ p n := by
  constructor
  · rintro rfl
    exact ⟨Nat.find_spec h, fun _ ↦ Nat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (Nat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| Nat.find_spec h)
#align nat.find_eq_iff Nat.find_eq_iff

@[simp] lemma find_lt_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 ↦ ⟨Nat.find h, h2, Nat.find_spec h⟩,
    fun ⟨_, hmn, hm⟩ ↦ Nat.lt_of_le_of_lt (Nat.find_min' h hm) hmn⟩
#align nat.find_lt_iff Nat.find_lt_iff

@[simp] lemma find_le_iff (h : ∃ n : ℕ, p n) (n : ℕ) : Nat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← Nat.lt_succ_iff, find_lt_iff]
#align nat.find_le_iff Nat.find_le_iff

@[simp] lemma le_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n ≤ Nat.find h ↔ ∀ m < n, ¬ p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
#align nat.le_find_iff Nat.le_find_iff

@[simp] lemma lt_find_iff (h : ∃ n : ℕ, p n) (n : ℕ) : n < Nat.find h ↔ ∀ m ≤ n, ¬ p m := by
  simp only [← succ_le_iff, le_find_iff, succ_le_succ_iff]
#align nat.lt_find_iff Nat.lt_find_iff

@[simp] lemma find_eq_zero (h : ∃ n : ℕ, p n) : Nat.find h = 0 ↔ p 0 := by
  simp [find_eq_iff, not_lt_zero]
#align nat.find_eq_zero Nat.find_eq_zero

lemma find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} : Nat.find hp ≤ Nat.find hq :=
  Nat.find_min' _ (h _ (Nat.find_spec hq))
#align nat.find_mono Nat.find_mono

lemma find_le {h : ∃ n, p n} (hn : p n) : Nat.find h ≤ n :=
  (Nat.find_le_iff _ _).2 ⟨n, le_refl _, hn⟩
#align nat.find_le Nat.find_le

lemma find_comp_succ (h₁ : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h0 : ¬ p 0) :
    Nat.find h₁ = Nat.find h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨Nat.find_spec h₂, fun n hn ↦ _⟩
  cases n
  exacts [h0, @Nat.find_min (fun n ↦ p (n + 1)) _ h₂ _ (succ_lt_succ_iff.1 hn)]
#align nat.find_comp_succ Nat.find_comp_succ

end Find

/-! ### `Nat.findGreatest` -/

section FindGreatest

/-- `Nat.findGreatest P n` is the largest `i ≤ bound` such that `P i` holds, or `0` if no such `i`
exists -/
def findGreatest (P : ℕ → Prop) [DecidablePred P] : ℕ → ℕ
  | 0 => 0
  | n + 1 => if P (n + 1) then n + 1 else Nat.findGreatest P n
#align nat.find_greatest Nat.findGreatest

variable {P Q : ℕ → Prop} [DecidablePred P] {n : ℕ}

@[simp] lemma findGreatest_zero : Nat.findGreatest P 0 = 0 := rfl
#align nat.find_greatest_zero Nat.findGreatest_zero

lemma findGreatest_succ (n : ℕ) :
    Nat.findGreatest P (n + 1) = if P (n + 1) then n + 1 else Nat.findGreatest P n := rfl
#align nat.find_greatest_succ Nat.findGreatest_succ

@[simp] lemma findGreatest_eq : ∀ {n}, P n → Nat.findGreatest P n = n
  | 0, _ => rfl
  | n + 1, h => by simp [Nat.findGreatest, h]
#align nat.find_greatest_eq Nat.findGreatest_eq

@[simp]
lemma findGreatest_of_not (h : ¬ P (n + 1)) : findGreatest P (n + 1) = findGreatest P n := by
  simp [Nat.findGreatest, h]
#align nat.find_greatest_of_not Nat.findGreatest_of_not

end FindGreatest

end Nat
