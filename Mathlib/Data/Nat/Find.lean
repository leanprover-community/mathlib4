/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad
-/

import Batteries.WF
import Mathlib.Init.Data.Nat.Basic

namespace Nat

/-!
# Nat.find

If `p` is a (decidable) predicate on `ℕ` and `hp : ∃ (n : ℕ), p n` is a proof that
there exists some natural number satisfying `p`, then `Nat.find hp` is the
smallest natural number satisfying `p`. Note that `Nat.find` is protected,
meaning that you can't just write `find`, even if the `Nat` namespace is open.

The API for `Nat.find` is:

* `Nat.find_spec` is the proof that `Nat.find hp` satisfies `p`.
* `Nat.find_min` is the proof that if `m < Nat.find hp` then `m` does not satisfy `p`.
* `Nat.find_min'` is the proof that if `m` does satisfy `p` then `Nat.find hp ≤ m`.

-/


section Find

variable {p : ℕ → Prop}

private def lbp (m n : ℕ) : Prop :=
  m = n + 1 ∧ ∀ k ≤ n, ¬p k

variable [DecidablePred p] (H : ∃ n, p n)

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
          Or.elim (Nat.lt_or_eq_of_le h) (al n) fun e => by rw [e]; exact pm
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
  Nat.le_of_not_lt fun l => Nat.find_min H l h
#align nat.find_min' Nat.find_min'

end Find

end Nat
