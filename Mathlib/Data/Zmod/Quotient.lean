/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module data.zmod.quotient
! leanprover-community/mathlib commit da420a8c6dd5bdfb85c4ced85c34388f633bc6ff
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

/-!
# `zmod n` and quotient groups / rings

This file relates `zmod n` to the quotient group
`quotient_add_group.quotient (add_subgroup.zmultiples n)` and to the quotient ring
`(ideal.span {n}).quotient`.

## Main definitions

 - `zmod.quotient_zmultiples_nat_equiv_zmod` and `zmod.quotient_zmultiples_equiv_zmod`:
   `zmod n` is the group quotient of `ℤ` by `n ℤ := add_subgroup.zmultiples (n)`,
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.quotient_span_nat_equiv_zmod` and `zmod.quotient_span_equiv_zmod`:
   `zmod n` is the ring quotient of `ℤ` by `n ℤ : ideal.span {n}`
   (where `n : ℕ` and `n : ℤ` respectively)
 - `zmod.lift n f` is the map from `zmod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group, quotient ring, ideal quotient
-/


open quotientAddGroup

open ZMod

variable (n : ℕ) {A R : Type _} [AddGroup A] [Ring R]

namespace Int

/-- `ℤ` modulo multiples of `n : ℕ` is `zmod n`. -/
def quotientZmultiplesNatEquivZmod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_int_castAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) coe int_cast_zmod_cast
#align int.quotient_zmultiples_nat_equiv_zmod Int.quotientZmultiplesNatEquivZmod

/-- `ℤ` modulo multiples of `a : ℤ` is `zmod a.nat_abs`. -/
def quotientZmultiplesEquivZmod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZmultiplesNatEquivZmod a.natAbs)
#align int.quotient_zmultiples_equiv_zmod Int.quotientZmultiplesEquivZmod

/-- `ℤ` modulo the ideal generated by `n : ℕ` is `zmod n`. -/
def quotientSpanNatEquivZmod : ℤ ⧸ Ideal.span {↑n} ≃+* ZMod n :=
  (Ideal.quotEquivOfEq (ZMod.ker_int_castRingHom _)).symm.trans <|
    RingHom.quotientKerEquivOfRightInverse <|
      show Function.RightInverse coe (Int.castRingHom (ZMod n)) from int_cast_zmod_cast
#align int.quotient_span_nat_equiv_zmod Int.quotientSpanNatEquivZmod

/-- `ℤ` modulo the ideal generated by `a : ℤ` is `zmod a.nat_abs`. -/
def quotientSpanEquivZmod (a : ℤ) : ℤ ⧸ Ideal.span ({a} : Set ℤ) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZmod a.natAbs)
#align int.quotient_span_equiv_zmod Int.quotientSpanEquivZmod

end Int

namespace AddAction

open AddSubgroup AddMonoidHom AddEquiv Function

variable {α β : Type _} [AddGroup α] (a : α) [AddAction α β] (b : β)

/-- The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod ((· +ᵥ ·) a) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le, mem_comap, mem_stabilizer_iff, zmultiplesHom_apply, coe_nat_zsmul,
                ← vadd_iterate]
              exact is_periodic_pt_minimal_period ((· +ᵥ ·) a) b))
          ⟨by
            rw [← ker_eq_bot_iff, eq_bot_iff]
            refine' fun q => induction_on' q fun n hn => _
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimal_period_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on' q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZmultiplesNatEquivZmod (minimalPeriod ((· +ᵥ ·) a) b))
#align add_action.zmultiples_quotient_stabilizer_equiv AddAction.zmultiplesQuotientStabilizerEquiv

theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod ((· +ᵥ ·) a) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl
#align add_action.zmultiples_quotient_stabilizer_equiv_symm_apply AddAction.zmultiplesQuotientStabilizerEquiv_symm_apply

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type _} [Group α] (a : α) [MulAction α β] (b : β)

attribute [local semireducible] MulOpposite

/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimal_period ((•) a) b`. -/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod ((· • ·) a) b)) :=
  let f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  ⟨f.toFun, f.invFun, f.left_inv, f.right_inv, f.map_add'⟩
#align mul_action.zpowers_quotient_stabilizer_equiv MulAction.zpowersQuotientStabilizerEquiv

theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod ((· • ·) a) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (n : ℤ) :=
  rfl
#align mul_action.zpowers_quotient_stabilizer_equiv_symm_apply MulAction.zpowersQuotientStabilizerEquiv_symm_apply

/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimal_period ((•) a) b`. -/
noncomputable def orbitZpowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod ((· • ·) a) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv
#align mul_action.orbit_zpowers_equiv MulAction.orbitZpowersEquiv

/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimal_period ((+ᵥ) a) b`. -/
noncomputable def AddAction.orbitZmultiplesEquiv {α β : Type _} [AddGroup α] (a : α) [AddAction α β]
    (b : β) : AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod ((· +ᵥ ·) a) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv
#align add_action.orbit_zmultiples_equiv AddAction.orbitZmultiplesEquiv

attribute [to_additive orbit_zmultiples_equiv] orbit_zpowers_equiv

@[to_additive orbit_zmultiples_equiv_symm_apply]
theorem orbitZpowersEquiv_symm_apply (k : ZMod (minimalPeriod ((· • ·) a) b)) :
    (orbitZpowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl
#align mul_action.orbit_zpowers_equiv_symm_apply MulAction.orbitZpowersEquiv_symm_apply
#align add_action.orbit_zmultiples_equiv_symm_apply AddAction.orbit_zmultiples_equiv_symm_apply

theorem orbitZpowersEquiv_symm_apply' (k : ℤ) :
    (orbitZpowersEquiv a b).symm k = (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ :=
  by
  rw [orbit_zpowers_equiv_symm_apply, ZMod.coe_int_cast]
  exact Subtype.ext (zpow_smul_mod_minimal_period _ _ k)
#align mul_action.orbit_zpowers_equiv_symm_apply' MulAction.orbitZpowersEquiv_symm_apply'

theorem AddAction.orbitZmultiplesEquiv_symm_apply' {α β : Type _} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZmultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbit_zmultiples_equiv_symm_apply, ZMod.coe_int_cast]
  exact Subtype.ext (zsmul_vadd_mod_minimal_period _ _ k)
#align add_action.orbit_zmultiples_equiv_symm_apply' AddAction.orbitZmultiplesEquiv_symm_apply'

attribute [to_additive orbit_zmultiples_equiv_symm_apply'] orbit_zpowers_equiv_symm_apply'

@[to_additive]
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod ((· • ·) a) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbit_zpowers_equiv a b), ZMod.card]
#align mul_action.minimal_period_eq_card MulAction.minimalPeriod_eq_card
#align add_action.minimal_period_eq_card AddAction.minimal_period_eq_card

@[to_additive]
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod ((· • ·) a) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    haveI : Nonempty (orbit (zpowers a) b) := (orbit_nonempty b).to_subtype
    rw [minimal_period_eq_card]
    exact Fintype.card_ne_zero⟩
#align mul_action.minimal_period_pos MulAction.minimalPeriod_pos
#align add_action.minimal_period_pos AddAction.minimal_period_pos

end MulAction

section Group

open Subgroup

variable {α : Type _} [Group α] (a : α)

/-- See also `order_eq_card_zpowers`. -/
@[to_additive add_order_eq_card_zmultiples' "See also `add_order_eq_card_zmultiples`."]
theorem order_eq_card_zpowers' : orderOf a = Nat.card (zpowers a) := by
  have := Nat.card_congr (MulAction.orbitZpowersEquiv a (1 : α))
  rwa [Nat.card_zMod, orbit_subgroup_one_eq_self, eq_comm] at this
#align order_eq_card_zpowers' order_eq_card_zpowers'
#align add_order_eq_card_zmultiples' add_order_eq_card_zmultiples'

variable {a}

@[to_additive IsOfFinAddOrder.finite_zmultiples]
theorem IsOfFinOrder.finite_zpowers (h : IsOfFinOrder a) : Finite <| zpowers a := by
  rw [← orderOf_pos_iff, order_eq_card_zpowers'] at h
  exact Nat.finite_of_card_ne_zero h.ne.symm
#align is_of_fin_order.finite_zpowers IsOfFinOrder.finite_zpowers
#align is_of_fin_add_order.finite_zmultiples IsOfFinAddOrder.finite_zmultiples

end Group

