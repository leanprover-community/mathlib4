/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module set_theory.cardinal.finite
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Zmod.Defs
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `part_enat.card α` is the cardinality of `α` as an extended natural number
  (`part ℕ` implementation). If `α` is infinite, `part_enat.card α = ⊤`.
-/


open Cardinal

noncomputable section

open BigOperators

variable {α β : Type _}

namespace Nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type _) : ℕ :=
  (mk α).toNat
#align nat.card Nat.card

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card
#align nat.card_eq_fintype_card Nat.card_eq_fintype_card

@[simp]
theorem card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  mk_toNat_of_infinite
#align nat.card_eq_zero_of_infinite Nat.card_eq_zero_of_infinite

theorem finite_of_card_ne_zero (h : Nat.card α ≠ 0) : Finite α :=
  not_infinite_iff_finite.mp <| h ∘ @Nat.card_eq_zero_of_infinite α
#align nat.finite_of_card_ne_zero Nat.finite_of_card_ne_zero

theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f
#align nat.card_congr Nat.card_congr

theorem card_eq_of_bijective (f : α → β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)
#align nat.card_eq_of_bijective Nat.card_eq_of_bijective

theorem card_eq_of_equiv_fin {α : Type _} {n : ℕ} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa using card_congr f
#align nat.card_eq_of_equiv_fin Nat.card_eq_of_equiv_fin

/-- If the cardinality is positive, that means it is a finite type, so there is
an equivalence between `α` and `fin (nat.card α)`. See also `finite.equiv_fin`. -/
def equivFinOfCardPos {α : Type _} (h : Nat.card α ≠ 0) : α ≃ Fin (Nat.card α) :=
  by
  cases fintypeOrInfinite α
  · simpa using Fintype.equivFin α
  · simpa using h
#align nat.equiv_fin_of_card_pos Nat.equivFinOfCardPos

theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 :=
  by
  letI := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card, Fintype.card_ofSubsingleton a]
#align nat.card_of_subsingleton Nat.card_of_subsingleton

@[simp]
theorem card_unique [Unique α] : Nat.card α = 1 :=
  card_of_subsingleton default
#align nat.card_unique Nat.card_unique

theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique
#align nat.card_eq_one_iff_unique Nat.card_eq_one_iff_unique

theorem card_eq_two_iff : Nat.card α = 2 ↔ ∃ x y : α, x ≠ y ∧ {x, y} = @Set.univ α :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) mk_eq_two_iff
#align nat.card_eq_two_iff Nat.card_eq_two_iff

theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ ∃! y, y ≠ x :=
  (toNat_eq_iff two_ne_zero).trans <| Iff.trans (by rw [Nat.cast_two]) (mk_eq_two_iff' x)
#align nat.card_eq_two_iff' Nat.card_eq_two_iff'

theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp
#align nat.card_of_is_empty Nat.card_of_isEmpty

@[simp]
theorem card_prod (α β : Type _) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, to_nat_mul, to_nat_lift]
#align nat.card_prod Nat.card_prod

@[simp]
theorem card_uLift (α : Type _) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift
#align nat.card_ulift Nat.card_uLift

@[simp]
theorem card_pLift (α : Type _) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift
#align nat.card_plift Nat.card_pLift

theorem card_pi {β : α → Type _} [Fintype α] : Nat.card (∀ a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, to_nat_lift, to_nat_finset_prod]
#align nat.card_pi Nat.card_pi

theorem card_fun [Finite α] : Nat.card (α → β) = Nat.card β ^ Nat.card α :=
  by
  haveI := Fintype.ofFinite α
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
#align nat.card_fun Nat.card_fun

@[simp]
theorem card_zMod (n : ℕ) : Nat.card (ZMod n) = n :=
  by
  cases n
  · exact Nat.card_eq_zero_of_infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]
#align nat.card_zmod Nat.card_zMod

end Nat

namespace PartENat

/-- `part_enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `part_enat.card α = ⊤`. -/
def card (α : Type _) : PartENat :=
  (mk α).toPartEnat
#align part_enat.card PartENat.card

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_toPartEnat_eq_coe_card
#align part_enat.card_eq_coe_fintype_card PartENat.card_eq_coe_fintype_card

@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_toPartEnat_of_infinite
#align part_enat.card_eq_top_of_infinite PartENat.card_eq_top_of_infinite

end PartENat

