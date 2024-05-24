/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.ZMod

#align_import data.zmod.quotient from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient group
`ℤ / AddSubgroup.zmultiples (n : ℤ)` and to the quotient ring
`ℤ ⧸ Ideal.span {(n : ℤ)}`.

## Main definitions

 - `ZMod.quotientZMultiplesNatEquivZMod` and `ZMod.quotientZMultiplesEquivZMod`:
   `ZMod n` is the group quotient of `ℤ` by `n ℤ := AddSubgroup.zmultiples (n)`,
   (where `n : ℕ` and `n : ℤ` respectively)
 - `ZMod.quotient_span_nat_equiv_zmod` and `ZMod.quotientSpanEquivZMod `:
   `ZMod n` is the ring quotient of `ℤ` by `n ℤ : Ideal.span {n}`
   (where `n : ℕ` and `n : ℤ` respectively)
 - `ZMod.lift n f` is the map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group, quotient ring, ideal quotient
-/

open QuotientAddGroup Set ZMod

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

/-- `ℤ` modulo multiples of `n : ℕ` is `ZMod n`. -/
def quotientZMultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast
#align int.quotient_zmultiples_nat_equiv_zmod Int.quotientZMultiplesNatEquivZMod

/-- `ℤ` modulo multiples of `a : ℤ` is `ZMod a.natAbs`. -/
def quotientZMultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)
#align int.quotient_zmultiples_equiv_zmod Int.quotientZMultiplesEquivZMod

/-- `ℤ` modulo the ideal generated by `n : ℕ` is `ZMod n`. -/
def quotientSpanNatEquivZMod : ℤ ⧸ Ideal.span {(n : ℤ)} ≃+* ZMod n :=
  (Ideal.quotEquivOfEq (ZMod.ker_intCastRingHom _)).symm.trans <|
    RingHom.quotientKerEquivOfRightInverse <|
      show Function.RightInverse ZMod.cast (Int.castRingHom (ZMod n)) from intCast_zmod_cast
#align int.quotient_span_nat_equiv_zmod Int.quotientSpanNatEquivZMod

/-- `ℤ` modulo the ideal generated by `a : ℤ` is `ZMod a.natAbs`. -/
def quotientSpanEquivZMod (a : ℤ) : ℤ ⧸ Ideal.span ({a} : Set ℤ) ≃+* ZMod a.natAbs :=
  (Ideal.quotEquivOfEq (span_natAbs a)).symm.trans (quotientSpanNatEquivZMod a.natAbs)
#align int.quotient_span_equiv_zmod Int.quotientSpanEquivZMod

end Int

noncomputable section ChineseRemainder
open BigOperators Ideal

/-- The **Chinese remainder theorem**, elementary version for `ZMod`. See also
`Mathlib.Data.ZMod.Basic` for versions involving only two numbers. -/
def ZMod.prodEquivPi {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (coprime : Pairwise fun i j => Nat.Coprime (a i) (a j)) : ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  have : Pairwise fun i j => IsCoprime (span {(a i : ℤ)}) (span {(a j : ℤ)}) :=
    fun _i _j h ↦ (isCoprime_span_singleton_iff _ _).mpr ((coprime h).cast (R := ℤ))
  Int.quotientSpanNatEquivZMod _ |>.symm.trans <|
  quotEquivOfEq (iInf_span_singleton_natCast (R := ℤ) coprime) |>.symm.trans <|
  quotientInfRingEquivPiQuotient _ this |>.trans <|
  RingEquiv.piCongrRight fun i ↦ Int.quotientSpanNatEquivZMod (a i)

end ChineseRemainder

namespace AddAction

open AddSubgroup AddMonoidHom AddEquiv Function

variable {α β : Type*} [AddGroup α] (a : α) [AddAction α β] (b : β)

/-- The quotient `(ℤ ∙ a) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod (a +ᵥ ·) b`. -/
noncomputable def zmultiplesQuotientStabilizerEquiv :
    zmultiples a ⧸ stabilizer (zmultiples a) b ≃+ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (ofBijective
          (map _ (stabilizer (zmultiples a) b) (zmultiplesHom (zmultiples a) ⟨a, mem_zmultiples a⟩)
            (by
              rw [zmultiples_le, mem_comap, mem_stabilizer_iff, zmultiplesHom_apply, natCast_zsmul]
              simp_rw [← vadd_iterate]
              exact isPeriodicPt_minimalPeriod (a +ᵥ ·) b))
          ⟨by
            rw [← ker_eq_bot_iff, eq_bot_iff]
            refine' fun q => induction_on' q fun n hn => _
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimalPeriod_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on' q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZMultiplesNatEquivZMod (minimalPeriod (a +ᵥ ·) b))
#align add_action.zmultiples_quotient_stabilizer_equiv AddAction.zmultiplesQuotientStabilizerEquiv

theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +ᵥ ·) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (cast n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl
#align add_action.zmultiples_quotient_stabilizer_equiv_symm_apply AddAction.zmultiplesQuotientStabilizerEquiv_symm_apply

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type*} [Group α] (a : α) [MulAction α β] (b : β)

/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod ((•) a) b`. -/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod (a • ·) b)) :=
  letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f
#align mul_action.zpowers_quotient_stabilizer_equiv MulAction.zpowersQuotientStabilizerEquiv

theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast n : ℤ) :=
  rfl
#align mul_action.zpowers_quotient_stabilizer_equiv_symm_apply MulAction.zpowersQuotientStabilizerEquiv_symm_apply

/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimalPeriod ((•) a) b`. -/
noncomputable def orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv
#align mul_action.orbit_zpowers_equiv MulAction.orbitZPowersEquiv

/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimalPeriod (a +ᵥ ·) b`. -/
noncomputable def _root_.AddAction.orbitZMultiplesEquiv {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) :
    AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv
#align add_action.orbit_zmultiples_equiv AddAction.orbitZMultiplesEquiv

attribute [to_additive existing] orbitZPowersEquiv

@[to_additive]
theorem orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl
#align mul_action.orbit_zpowers_equiv_symm_apply MulAction.orbitZPowersEquiv_symm_apply
#align add_action.orbit_zmultiples_equiv_symm_apply AddAction.orbitZMultiplesEquiv_symm_apply

@[deprecated] -- 2024-02-21
alias _root_.AddAction.orbit_zmultiples_equiv_symm_apply := orbitZMultiplesEquiv_symm_apply

theorem orbitZPowersEquiv_symm_apply' (k : ℤ) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ := by
  rw [orbitZPowersEquiv_symm_apply, ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)
#align mul_action.orbit_zpowers_equiv_symm_apply' MulAction.orbitZPowersEquiv_symm_apply'

theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply' {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZMultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply, ZMod.coe_intCast]
  -- Porting note: times out without `a b` explicit
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a b k)
#align add_action.orbit_zmultiples_equiv_symm_apply' AddAction.orbitZMultiplesEquiv_symm_apply'

attribute [to_additive existing]
  orbitZPowersEquiv_symm_apply'

@[to_additive]
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b) := by
  -- Porting note: added `(_)` to find `Fintype` by unification
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b), @ZMod.card _ (_)]
#align mul_action.minimal_period_eq_card MulAction.minimalPeriod_eq_card
#align add_action.minimal_period_eq_card AddAction.minimalPeriod_eq_card

@[to_additive]
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod (a • ·) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    haveI : Nonempty (orbit (zpowers a) b) := (orbit_nonempty b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩
#align mul_action.minimal_period_pos MulAction.minimalPeriod_pos
#align add_action.minimal_period_pos AddAction.minimalPeriod_pos

end MulAction

section Group

open Subgroup

variable {α : Type*} [Group α] (a : α)

/-- See also `Fintype.card_zpowers`. -/
@[to_additive (attr := simp) "See also `Fintype.card_zmultiples`."]
theorem Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this
#align order_eq_card_zpowers' Nat.card_zpowersₓ
#align add_order_eq_card_zmultiples' Nat.card_zmultiplesₓ

variable {a}

@[to_additive (attr := simp)]
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, Subgroup.coe_nonempty, true_and]

@[to_additive (attr := simp)]
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers
#align is_of_fin_order.finite_zpowers IsOfFinOrder.finite_zpowers
#align is_of_fin_add_order.finite_zmultiples IsOfFinAddOrder.finite_zmultiples

end Group
