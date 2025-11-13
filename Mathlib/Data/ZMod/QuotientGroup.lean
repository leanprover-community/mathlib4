/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Data.ZMod.Basic

/-!
# `ZMod n` and quotient groups / rings

This file relates `ZMod n` to the quotient group `ℤ / AddSubgroup.zmultiples (n : ℤ)`.

## Main definitions

- `ZMod.quotientZMultiplesNatEquivZMod` and `ZMod.quotientZMultiplesEquivZMod`:
  `ZMod n` is the group quotient of `ℤ` by `n ℤ := AddSubgroup.zmultiples (n)`,
  (where `n : ℕ` and `n : ℤ` respectively)
- `ZMod.lift n f` is the map from `ZMod n` induced by `f : ℤ →+ A` that maps `n` to `0`.

## Tags

zmod, quotient group
-/

assert_not_exists Ideal TwoSidedIdeal

open QuotientAddGroup Set ZMod

variable (n : ℕ) {A R : Type*} [AddGroup A] [Ring R]

namespace Int

/-- `ℤ` modulo multiples of `n : ℕ` is `ZMod n`. -/
def quotientZMultiplesNatEquivZMod : ℤ ⧸ AddSubgroup.zmultiples (n : ℤ) ≃+ ZMod n :=
  (quotientAddEquivOfEq (ZMod.ker_intCastAddHom _)).symm.trans <|
    quotientKerEquivOfRightInverse (Int.castAddHom (ZMod n)) cast intCast_zmod_cast

/-- `ℤ` modulo multiples of `a : ℤ` is `ZMod a.natAbs`. -/
def quotientZMultiplesEquivZMod (a : ℤ) : ℤ ⧸ AddSubgroup.zmultiples a ≃+ ZMod a.natAbs :=
  (quotientAddEquivOfEq (zmultiples_natAbs a)).symm.trans (quotientZMultiplesNatEquivZMod a.natAbs)

@[simp]
lemma index_zmultiples (a : ℤ) : (AddSubgroup.zmultiples a).index = a.natAbs := by
  rw [AddSubgroup.index, Nat.card_congr (quotientZMultiplesEquivZMod a).toEquiv, Nat.card_zmod]

end Int


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
            refine fun q => induction_on q fun n hn => ?_
            rw [mem_bot, eq_zero_iff, Int.mem_zmultiples_iff, ←
              zsmul_vadd_eq_iff_minimalPeriod_dvd]
            exact (eq_zero_iff _).mp hn, fun q =>
            induction_on q fun ⟨_, n, rfl⟩ => ⟨n, rfl⟩⟩).symm.trans
    (Int.quotientZMultiplesNatEquivZMod (minimalPeriod (a +ᵥ ·) b))

theorem zmultiplesQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a +ᵥ ·) b)) :
    (zmultiplesQuotientStabilizerEquiv a b).symm n =
      (cast n : ℤ) • (⟨a, mem_zmultiples a⟩ : zmultiples a) :=
  rfl

end AddAction

namespace MulAction

open AddAction Subgroup AddSubgroup Function

variable {α β : Type*} [Group α] (a : α) [MulAction α β] (b : β)

/-- The quotient `(a ^ ℤ) ⧸ (stabilizer b)` is cyclic of order `minimalPeriod ((•) a) b`. -/
noncomputable def zpowersQuotientStabilizerEquiv :
    zpowers a ⧸ stabilizer (zpowers a) b ≃* Multiplicative (ZMod (minimalPeriod (a • ·) b)) :=
  letI f := zmultiplesQuotientStabilizerEquiv (Additive.ofMul a) b
  AddEquiv.toMultiplicative f

theorem zpowersQuotientStabilizerEquiv_symm_apply (n : ZMod (minimalPeriod (a • ·) b)) :
    (zpowersQuotientStabilizerEquiv a b).symm n = (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast n : ℤ) :=
  rfl

/-- The orbit `(a ^ ℤ) • b` is a cycle of order `minimalPeriod ((•) a) b`. -/
noncomputable def orbitZPowersEquiv : orbit (zpowers a) b ≃ ZMod (minimalPeriod (a • ·) b) :=
  (orbitEquivQuotientStabilizer _ b).trans (zpowersQuotientStabilizerEquiv a b).toEquiv

/-- The orbit `(ℤ • a) +ᵥ b` is a cycle of order `minimalPeriod (a +ᵥ ·) b`. -/
noncomputable def _root_.AddAction.orbitZMultiplesEquiv {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) :
    AddAction.orbit (zmultiples a) b ≃ ZMod (minimalPeriod (a +ᵥ ·) b) :=
  (AddAction.orbitEquivQuotientStabilizer (zmultiples a) b).trans
    (zmultiplesQuotientStabilizerEquiv a b).toEquiv

attribute [to_additive existing] orbitZPowersEquiv

@[to_additive]
theorem orbitZPowersEquiv_symm_apply (k : ZMod (minimalPeriod (a • ·) b)) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ (cast k : ℤ) • ⟨b, mem_orbit_self b⟩ :=
  rfl

theorem orbitZPowersEquiv_symm_apply' (k : ℤ) :
    (orbitZPowersEquiv a b).symm k =
      (⟨a, mem_zpowers a⟩ : zpowers a) ^ k • ⟨b, mem_orbit_self b⟩ := by
  rw [orbitZPowersEquiv_symm_apply, ZMod.coe_intCast]
  exact Subtype.ext (zpow_smul_mod_minimalPeriod _ _ k)

theorem _root_.AddAction.orbitZMultiplesEquiv_symm_apply' {α β : Type*} [AddGroup α] (a : α)
    [AddAction α β] (b : β) (k : ℤ) :
    (AddAction.orbitZMultiplesEquiv a b).symm k =
      k • (⟨a, mem_zmultiples a⟩ : zmultiples a) +ᵥ ⟨b, AddAction.mem_orbit_self b⟩ := by
  rw [AddAction.orbitZMultiplesEquiv_symm_apply, ZMod.coe_intCast]
  -- Making `a` explicit turns this from ~190000 heartbeats to ~700.
  exact Subtype.ext (zsmul_vadd_mod_minimalPeriod a _ k)

attribute [to_additive existing]
  orbitZPowersEquiv_symm_apply'

@[to_additive]
theorem minimalPeriod_eq_card [Fintype (orbit (zpowers a) b)] :
    minimalPeriod (a • ·) b = Fintype.card (orbit (zpowers a) b) := by
  rw [← Fintype.ofEquiv_card (orbitZPowersEquiv a b), ZMod.card]

@[to_additive]
instance minimalPeriod_pos [Finite <| orbit (zpowers a) b] :
    NeZero <| minimalPeriod (a • ·) b :=
  ⟨by
    cases nonempty_fintype (orbit (zpowers a) b)
    haveI : Nonempty (orbit (zpowers a) b) := (nonempty_orbit b).to_subtype
    rw [minimalPeriod_eq_card]
    exact Fintype.card_ne_zero⟩

end MulAction

section Group

open Subgroup

variable {α : Type*} [Group α] (a : α)

/-- See also `Fintype.card_zpowers`. -/
@[to_additive (attr := simp) /-- See also `Fintype.card_zmultiples`. -/]
theorem Nat.card_zpowers : Nat.card (zpowers a) = orderOf a := by
  have := Nat.card_congr (MulAction.orbitZPowersEquiv a (1 : α))
  rwa [Nat.card_zmod, orbit_subgroup_one_eq_self] at this

variable {a}

@[to_additive (attr := simp)]
lemma finite_zpowers : (zpowers a : Set α).Finite ↔ IsOfFinOrder a := by
  simp only [← orderOf_pos_iff, ← Nat.card_zpowers, Nat.card_pos_iff, ← SetLike.coe_sort_coe,
    nonempty_coe_sort, Nat.card_pos_iff, Set.finite_coe_iff, Subgroup.coe_nonempty, true_and]

@[to_additive (attr := simp)]
lemma infinite_zpowers : (zpowers a : Set α).Infinite ↔ ¬IsOfFinOrder a := finite_zpowers.not

@[to_additive]
protected alias ⟨_, IsOfFinOrder.finite_zpowers⟩ := finite_zpowers

end Group

namespace Subgroup
variable {G : Type*} [Group G] (H : Subgroup G) (g : G)

open Equiv Function MulAction

/-- Partition `G ⧸ H` into orbits of the action of `g : G`. -/
noncomputable def quotientEquivSigmaZMod :
    G ⧸ H ≃ Σ q : orbitRel.Quotient (zpowers g) (G ⧸ H), ZMod (minimalPeriod (g • ·) q.out) :=
  (selfEquivSigmaOrbits (zpowers g) (G ⧸ H)).trans
    (sigmaCongrRight fun q => orbitZPowersEquiv g q.out)

lemma quotientEquivSigmaZMod_symm_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H))
    (k : ZMod (minimalPeriod (g • ·) q.out)) :
    (quotientEquivSigmaZMod H g).symm ⟨q, k⟩ = g ^ (cast k : ℤ) • q.out := rfl

lemma quotientEquivSigmaZMod_apply (q : orbitRel.Quotient (zpowers g) (G ⧸ H)) (k : ℤ) :
    quotientEquivSigmaZMod H g (g ^ k • q.out) = ⟨q, k⟩ := by
  rw [apply_eq_iff_eq_symm_apply, quotientEquivSigmaZMod_symm_apply, ZMod.coe_intCast,
    zpow_smul_mod_minimalPeriod]

end Subgroup
