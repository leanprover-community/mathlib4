/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

assert_not_exists OrderedCommMonoid Ring

universe u

namespace Multiset

open List

variable {α β : Type*}

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l ↦ (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h ↦ Quot.sound (revzip_powersetAux_perm h)

theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l) :=
  rfl

@[simp]
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' l) :=
  Quot.sound revzip_powersetAux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} :
    x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
  Quotient.inductionOn s fun l ↦ by
    dsimp only [quot_mk_to_coe, antidiagonal_coe]
    refine ⟨fun h => revzip_powersetAux h, fun h ↦ ?_⟩
    have _ := Classical.decEq α
    simp only [revzip_powersetAux_lemma l revzip_powersetAux, h.symm, mem_coe,
      List.mem_map, mem_powersetAux]
    obtain ⟨x₁, x₂⟩ := x
    exact ⟨x₁, le_add_right _ _, by rw [add_tsub_cancel_left x₁ x₂]⟩

@[simp]
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotient.inductionOn s fun l ↦ by simp [powersetAux']

@[simp]
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotient.inductionOn s fun l ↦ by simp [powersetAux']

@[simp]
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl

@[simp]
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotient.inductionOn s fun l ↦ by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powersetAux'_cons, cons_coe,
      map_coe, antidiagonal_coe', coe_add]
    rw [← zip_map, ← zip_map, zip_append, (_ : _ ++ _ = _)]
    · congr
      · simp only [List.map_id]
      · rw [map_reverse]
      · simp
    · simp

theorem antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) :
    s.antidiagonal = s.powerset.map fun t ↦ (s - t, t) := by
  induction s using Multiset.induction_on with
  | empty => simp only [antidiagonal_zero, powerset_zero, Multiset.zero_sub, map_singleton]
  | cons a s hs =>
    simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_apply,
      id, sub_cons, erase_cons_head]
    rw [add_comm]
    congr 1
    refine Multiset.map_congr rfl fun x hx ↦ ?_
    rw [cons_sub_of_le _ (mem_powerset.mp hx)]

@[simp]
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s
  rwa [← antidiagonal_map_fst, card_map] at this

end Multiset
