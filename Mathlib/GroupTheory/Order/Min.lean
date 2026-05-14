/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Attr
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Minimum order of an element

This file defines the minimum order of an element of a monoid.

## Main declarations

* `Monoid.minOrder`: The minimum order of an element of a given monoid.
* `Monoid.minOrder_eq_top`: The minimum order is infinite iff the monoid is torsion-free.
* `ZMod.minOrder`: The minimum order of $ℤ/nℤ$ is the smallest factor of `n`, unless `n = 0, 1`.
-/

@[expose] public section

open Subgroup

variable {G α : Type*}

namespace Monoid
section Monoid
variable (α) [Monoid α]

/-- The minimum order of a non-identity element. Also the minimum size of a nontrivial subgroup, see
`Monoid.le_minOrder_iff_forall_subgroup`. Returns `∞` if the monoid is torsion-free. -/
@[to_additive /-- The minimum order of a non-identity element. Also the minimum size of a nontrivial
subgroup, see `AddMonoid.le_minOrder_iff_forall_addSubgroup`. Returns `∞` if the monoid is
torsion-free. -/]
noncomputable def minOrder : ℕ∞ := ⨅ (a : α) (_ha : a ≠ 1) (_ha' : IsOfFinOrder a), orderOf a

variable {α} {a : α}

@[to_additive (attr := simp)]
lemma le_minOrder {n : ℕ∞} :
    n ≤ minOrder α ↔ ∀ ⦃a : α⦄, a ≠ 1 → IsOfFinOrder a → n ≤ orderOf a := by simp [minOrder]

@[to_additive]
lemma minOrder_le_orderOf (ha : a ≠ 1) (ha' : IsOfFinOrder a) : minOrder α ≤ orderOf a :=
  le_minOrder.1 le_rfl ha ha'

end Monoid

section Group
variable [Group G] {s : Subgroup G}

@[to_additive]
lemma le_minOrder_iff_forall_subgroup {n : ℕ∞} :
    n ≤ minOrder G ↔ ∀ ⦃s : Subgroup G⦄, s ≠ ⊥ → (s : Set G).Finite → n ≤ Nat.card s := by
  rw [le_minOrder]
  refine ⟨fun h s hs hs' ↦ ?_, fun h a ha ha' ↦ ?_⟩
  · obtain ⟨a, has, ha⟩ := s.bot_or_exists_ne_one.resolve_left hs
    exact
      (h ha <| finite_zpowers.1 <| hs'.subset <| zpowers_le.2 has).trans
        (WithTop.coe_le_coe.2 <| s.orderOf_le_card hs' has)
  · simpa using h (zpowers_ne_bot.2 ha) ha'.finite_zpowers

@[to_additive]
lemma minOrder_le_natCard (hs : s ≠ ⊥) (hs' : (s : Set G).Finite) : minOrder G ≤ Nat.card s :=
  le_minOrder_iff_forall_subgroup.1 le_rfl hs hs'

@[to_additive (attr := simp)]
lemma minOrder_eq_top [IsMulTorsionFree G] : minOrder G = ⊤ := by
  simpa [minOrder] using fun _ ↦ not_isOfFinOrder_of_isMulTorsionFree

end Group

section CommGroup
variable [CommGroup G] {s : Subgroup G}

@[to_additive (attr := simp)]
lemma minOrder_eq_top_iff : minOrder G = ⊤ ↔ IsMulTorsionFree G := by
  simp [minOrder, isMulTorsionFree_iff_not_isOfFinOrder]

end CommGroup
end Monoid

open AddMonoid AddSubgroup Nat Set

namespace ZMod

@[simp]
protected lemma minOrder {n : ℕ} (hn : n ≠ 0) (hn₁ : n ≠ 1) : minOrder (ZMod n) = n.minFac := by
  have : Fact (1 < n) := ⟨one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn, hn₁⟩⟩
  classical
  have : (↑(n / n.minFac) : ZMod n) ≠ 0 := by
    rw [Ne, ringChar.spec, ringChar.eq (ZMod n) n]
    exact
      not_dvd_of_pos_of_lt (Nat.div_pos (minFac_le hn.bot_lt) n.minFac_pos)
        (div_lt_self hn.bot_lt (minFac_prime hn₁).one_lt)
  refine ((minOrder_le_natCard (zmultiples_eq_bot.not.2 this) <| toFinite _).trans ?_).antisymm <|
    le_minOrder_iff_forall_addSubgroup.2 fun s hs _ ↦ ?_
  · rw [Nat.card_zmultiples, ZMod.addOrderOf_coe _ hn,
      gcd_eq_right (div_dvd_of_dvd n.minFac_dvd), Nat.div_div_self n.minFac_dvd hn]
  · haveI : Nontrivial s := s.bot_or_nontrivial.resolve_left hs
    exact WithTop.coe_le_coe.2 <| minFac_le_of_dvd Finite.one_lt_card <|
      (card_addSubgroup_dvd_card _).trans n.card_zmod.dvd

@[simp]
lemma minOrder_of_prime {p : ℕ} (hp : p.Prime) : minOrder (ZMod p) = p := by
  rw [ZMod.minOrder hp.ne_zero hp.ne_one, hp.minFac_eq]

end ZMod
