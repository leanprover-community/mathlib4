/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
import Mathlib.Data.PNat.Basic

#align_import data.pnat.find from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `Nat.find`.

-/


namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+) (_ : n' = n), p n :=
  fun n' =>
  decidable_of_iff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [mk_coe, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']
      -- 🎉 no goals
#align pnat.decidable_pred_exists_nat PNat.decidablePredExistsNat

--include h

/-- The `PNat` version of `Nat.findX` -/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ) (n : ℕ+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  -- ⊢ { n // p n ∧ ∀ (m : ℕ+), m < n → ¬p m }
  have n := Nat.findX this
  -- ⊢ { n // p n ∧ ∀ (m : ℕ+), m < n → ¬p m }
  refine' ⟨⟨n, _⟩, _, fun m hm pm => _⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    -- ⊢ 0 < ↑n
    rw [hn']
    -- ⊢ 0 < ↑n'
    exact n'.prop
    -- 🎉 no goals
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    -- ⊢ p { val := ↑n, property := (_ : 0 < ↑n) }
    simpa [hn', Subtype.coe_eta] using pn'
    -- 🎉 no goals
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
    -- 🎉 no goals
#align pnat.find_x PNat.findX

/-- If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `PNat.find hp` is the
smallest positive natural number satisfying `p`. Note that `PNat.find` is protected,
meaning that you can't just write `find`, even if the `PNat` namespace is open.

The API for `PNat.find` is:

* `PNat.find_spec` is the proof that `PNat.find hp` satisfies `p`.
* `PNat.find_min` is the proof that if `m < PNat.find hp` then `m` does not satisfy `p`.
* `PNat.find_min'` is the proof that if `m` does satisfy `p` then `PNat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
  PNat.findX h
#align pnat.find PNat.find

protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).prop.left
#align pnat.find_spec PNat.find_spec

protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  @(PNat.findX h).prop.right
#align pnat.find_min PNat.find_min

protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_lt fun l => PNat.find_min h l hm
#align pnat.find_min' PNat.find_min'

variable {n m : ℕ+}

theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  -- ⊢ PNat.find h = m → p m ∧ ∀ (n : ℕ+), n < m → ¬p n
  · rintro rfl
    -- ⊢ p (PNat.find h) ∧ ∀ (n : ℕ+), n < PNat.find h → ¬p n
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
    -- 🎉 no goals
  · rintro ⟨hm, hlt⟩
    -- ⊢ PNat.find h = m
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)
    -- 🎉 no goals
#align pnat.find_eq_iff PNat.find_eq_iff

@[simp]
theorem find_lt_iff (n : ℕ+) : PNat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨PNat.find h, h2, PNat.find_spec h⟩, fun ⟨_, hmn, hm⟩ =>
    (PNat.find_min' h hm).trans_lt hmn⟩
#align pnat.find_lt_iff PNat.find_lt_iff

@[simp]
theorem find_le_iff (n : ℕ+) : PNat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [exists_prop, ← lt_add_one_iff, find_lt_iff]
  -- 🎉 no goals
#align pnat.find_le_iff PNat.find_le_iff

@[simp]
theorem le_find_iff (n : ℕ+) : n ≤ PNat.find h ↔ ∀ m < n, ¬p m := by
  simp only [← not_lt, find_lt_iff, not_exists, not_and]
  -- 🎉 no goals
#align pnat.le_find_iff PNat.le_find_iff

@[simp]
theorem lt_find_iff (n : ℕ+) : n < PNat.find h ↔ ∀ m ≤ n, ¬p m := by
  simp only [← add_one_le_iff, le_find_iff, add_le_add_iff_right]
  -- 🎉 no goals
#align pnat.lt_find_iff PNat.lt_find_iff

@[simp]
theorem find_eq_one : PNat.find h = 1 ↔ p 1 := by simp [find_eq_iff]
                                                  -- 🎉 no goals
#align pnat.find_eq_one PNat.find_eq_one

-- porting notes: deleted `@[simp]` to satisfy the linter because `le_find_iff` is more general
theorem one_le_find : 1 < PNat.find h ↔ ¬p 1 :=
  not_iff_not.mp <| by simp
                       -- 🎉 no goals
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
  -- ⊢ 1 < PNat.find h₂ + 1 → ¬p 1
  · simp [h1]
    -- 🎉 no goals
  intro m _ hm
  -- ⊢ ¬p (m + 1)
  simp only [add_lt_add_iff_right, lt_find_iff] at hm
  -- ⊢ ¬p (m + 1)
  exact hm _ le_rfl
  -- 🎉 no goals
#align pnat.find_comp_succ PNat.find_comp_succ

end PNat
