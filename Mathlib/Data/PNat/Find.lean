/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn

! This file was ported from Lean 3 source module data.pnat.find
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Pnat.Basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `nat.find`.

-/


namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+)(hn : n' = n), p n :=
  fun n' =>
  decidable_of_iff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [Subtype.coe_mk, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']
#align pnat.decidable_pred_exists_nat PNat.decidablePredExistsNat

include h

/-- The `pnat` version of `nat.find_x` -/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ)(n : ℕ+)(hn' : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine' ⟨⟨n, _⟩, _, fun m hm pm => _⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
#align pnat.find_x PNat.findX

/-- If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
  PNat.findX h
#align pnat.find PNat.find

protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).Prop.left
#align pnat.find_spec PNat.find_spec

protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  (PNat.findX h).Prop.right
#align pnat.find_min PNat.find_min

protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_lt fun l => PNat.find_min h l hm
#align pnat.find_min' PNat.find_min'

variable {n m : ℕ+}

theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)
#align pnat.find_eq_iff PNat.find_eq_iff

@[simp]
theorem find_lt_iff (n : ℕ+) : PNat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨m, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩
#align pnat.find_lt_iff PNat.find_lt_iff

@[simp]
theorem find_le_iff (n : ℕ+) : PNat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]
#align pnat.find_le_iff PNat.find_le_iff

@[simp]
theorem le_find_iff (n : ℕ+) : n ≤ PNat.find h ↔ ∀ m < n, ¬p m := by
  simp_rw [← not_lt, find_lt_iff, not_exists]
#align pnat.le_find_iff PNat.le_find_iff

@[simp]
theorem lt_find_iff (n : ℕ+) : n < PNat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]
#align pnat.lt_find_iff PNat.lt_find_iff

@[simp]
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]
#align pnat.find_eq_one PNat.find_eq_one

@[simp]
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 :=
  not_iff_not.mp <| by simp
#align pnat.one_le_find PNat.one_le_find

theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} :
    PNat.find hp ≤ PNat.find hq :=
  PNat.find_min' _ (h _ (PNat.find_spec hq))
#align pnat.find_mono PNat.find_mono

theorem find_le {h : ∃ n, p n} (hn : p n) : PNat.find h ≤ n :=
  (PNat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩
#align pnat.find_le PNat.find_le

theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) :
    PNat.find h = PNat.find h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨PNat.find_spec h₂, fun n => PNat.recOn n _ _⟩
  · simp [h1]
  intro m IH hm
  simp only [add_lt_add_iff_right, lt_find_iff] at hm
  exact hm _ le_rfl
#align pnat.find_comp_succ PNat.find_comp_succ

end PNat

